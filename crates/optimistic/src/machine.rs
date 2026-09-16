// SPDX-License-Identifier: LGPL-3.0-or-later

//! An in-process EVM whose every interpreter step can be observed, with the one change to the
//! verifier's semantics that a step-by-step re-execution needs: `GAS` pushes a constant.

use revm::{
    Context, InspectCommitEvm, MainBuilder, MainContext,
    context::{
        TxEnv,
        result::{ExecutionResult, Output},
    },
    database::{CacheDB, EmptyDB},
    handler::{MainnetContext, MainnetEvm},
    inspector::Inspector,
    interpreter::{
        CallInputs, CallOutcome, CreateInputs, CreateOutcome, Interpreter, interpreter::EthInterpreter,
        interpreter_types::Jumps,
    },
    primitives::{Address, Bytes, TxKind, U256, hardfork::SpecId},
    state::AccountInfo,
};

/// The caller every transaction is sent from.
pub const CALLER: Address = Address::new([0x11; 20]);

/// Gas limit given to every transaction.
pub const GAS: u64 = 1 << 62;

/// What `GAS` pushes in a traced execution.
pub const GAS_CONSTANT: u64 = 1 << 32;

/// The `GAS` opcode.
pub const OP_GAS: u8 = 0x5a;

/// An observer of interpreter steps at call depth zero.
pub trait Sink {
    /// Called before the instruction at the current program counter executes.
    fn step(&mut self, interp: &mut Interpreter<EthInterpreter>);

    /// Called after it has executed.
    fn step_end(&mut self, interp: &mut Interpreter<EthInterpreter>) {
        let _ = interp;
    }

    /// The sink, for downcasting once the call is over.
    fn into_any(self: Box<Self>) -> Box<dyn std::any::Any>;
}

/// The inspector: fixes `GAS` and forwards depth-zero steps to a sink.
#[derive(Default)]
pub struct Hook {
    /// The sink, if any.
    pub sink: Option<Box<dyn Sink>>,
    last: u8,
    depth: usize,
}

impl<CTX> Inspector<CTX, EthInterpreter> for Hook {
    #[inline]
    fn step(&mut self, interp: &mut Interpreter<EthInterpreter>, _context: &mut CTX) {
        if self.depth != 1 {
            return;
        }
        self.last = interp.bytecode.opcode();
        if let Some(sink) = self.sink.as_mut() {
            sink.step(interp);
        }
    }

    #[inline]
    fn step_end(&mut self, interp: &mut Interpreter<EthInterpreter>, _context: &mut CTX) {
        if self.depth != 1 {
            return;
        }
        if self.last == OP_GAS {
            if let Some(top) = interp.stack.top() {
                *top = U256::from(GAS_CONSTANT);
            }
        }
        if let Some(sink) = self.sink.as_mut() {
            sink.step_end(interp);
        }
    }

    fn call(&mut self, _context: &mut CTX, _inputs: &mut CallInputs) -> Option<CallOutcome> {
        self.depth += 1;
        return None;
    }

    fn call_end(&mut self, _context: &mut CTX, _inputs: &CallInputs, _outcome: &mut CallOutcome) {
        self.depth -= 1;
    }

    fn create(&mut self, _context: &mut CTX, _inputs: &mut CreateInputs) -> Option<CreateOutcome> {
        self.depth += 1;
        return None;
    }

    fn create_end(&mut self, _context: &mut CTX, _inputs: &CreateInputs, _outcome: &mut CreateOutcome) {
        self.depth -= 1;
    }
}

/// The outcome of one call.
#[derive(Clone, Debug)]
pub struct Outcome {
    /// Whether it returned rather than reverted or halted.
    pub success: bool,
    /// Gas used, intrinsic gas included.
    pub gas: u64,
    /// Return or revert data.
    pub output: Vec<u8>,
}

/// An EVM under Osaka rules with the caps lifted, and a step hook.
pub struct Machine {
    evm: MainnetEvm<MainnetContext<CacheDB<EmptyDB>>, Hook>,
    nonce: u64,
}

impl Default for Machine {
    fn default() -> Self {
        return Self::new(false);
    }
}

impl Machine {
    /// A fresh machine; `capped` keeps mainnet's transaction gas cap, block limit and code-size
    /// limit instead of lifting them.
    pub fn new(capped: bool) -> Self {
        let mut db = CacheDB::<EmptyDB>::default();
        db.insert_account_info(
            CALLER,
            AccountInfo {
                balance: U256::MAX,
                ..Default::default()
            },
        );
        let ctx = Context::mainnet()
            .with_db(db)
            .modify_cfg_chained(|cfg| {
                cfg.spec = SpecId::OSAKA;
                if !capped {
                    cfg.tx_gas_limit_cap = Some(u64::MAX);
                    cfg.disable_block_gas_limit = true;
                    cfg.memory_limit = u64::MAX;
                }
                cfg.limit_contract_code_size = Some(usize::MAX);
                cfg.limit_contract_initcode_size = Some(usize::MAX);
                cfg.disable_base_fee = true;
                cfg.disable_nonce_check = true;
            })
            .modify_block_chained(|block| {
                block.gas_limit = if capped { 1 << 30 } else { GAS };
            });
        return Self {
            evm: ctx.build_mainnet_with_inspector(Hook::default()),
            nonce: 0,
        };
    }

    fn run(&mut self, kind: TxKind, data: Vec<u8>, gas: u64, value: U256) -> ExecutionResult {
        return self.run_as(CALLER, kind, data, gas, value);
    }

    fn run_as(&mut self, from: Address, kind: TxKind, data: Vec<u8>, gas: u64, value: U256) -> ExecutionResult {
        let tx = TxEnv::builder()
            .caller(from)
            .kind(kind)
            .data(Bytes::from(data))
            .gas_limit(gas)
            .gas_price(0)
            .value(value)
            .nonce(self.nonce)
            .build_fill();
        self.nonce += 1;
        self.evm.inspector.depth = 0;
        return self.evm.inspect_tx_commit(tx).expect("transaction is valid");
    }

    /// Deploys `initcode`, returning the new contract's address and the deployment's gas.
    pub fn deploy(&mut self, initcode: Vec<u8>) -> (Address, u64) {
        let gas = self.default_gas();
        match self.run(TxKind::Create, initcode, gas, U256::ZERO) {
            ExecutionResult::Success {
                output: Output::Create(_, Some(address)),
                gas,
                ..
            } => return (address, gas.tx_gas_used()),
            other => panic!("deployment failed: {other:?}"),
        }
    }

    fn default_gas(&self) -> u64 {
        return if self.evm.ctx.cfg.tx_gas_limit_cap == Some(u64::MAX) { GAS } else { 1 << 24 };
    }

    /// Calls `to` with `data`, with `sink` observing its steps.
    pub fn call_traced(&mut self, to: Address, data: Vec<u8>, sink: Option<Box<dyn Sink>>) -> (Outcome, Option<Box<dyn Sink>>) {
        self.evm.inspector.sink = sink;
        let gas = self.default_gas();
        let result = self.run(TxKind::Call(to), data, gas, U256::ZERO);
        let sink = self.evm.inspector.sink.take();
        return (outcome(result), sink);
    }

    /// Calls `to` with `data`.
    pub fn call(&mut self, to: Address, data: Vec<u8>) -> Outcome {
        return self.call_traced(to, data, None).0;
    }

    /// Calls `to` with `data`, sending `value` wei.
    pub fn call_value(&mut self, to: Address, data: Vec<u8>, value: U256) -> Outcome {
        let gas = self.default_gas();
        return outcome(self.run(TxKind::Call(to), data, gas, value));
    }

    /// Calls `to` with `data` from `from`, sending `value` wei, under mainnet's transaction gas
    /// cap.
    pub fn call_as(&mut self, from: Address, to: Address, data: Vec<u8>, value: U256) -> Outcome {
        return outcome(self.run_as(from, TxKind::Call(to), data, 1 << 24, value));
    }

    /// Sets the block timestamp.
    pub fn set_time(&mut self, timestamp: u64) {
        self.evm.ctx.block.timestamp = U256::from(timestamp);
    }

    /// The balance of `who`.
    pub fn balance(&mut self, who: Address) -> U256 {
        use revm::database::DatabaseRef;
        return self.evm.ctx.journaled_state.database.basic_ref(who).ok().flatten().map_or(U256::ZERO, |a| a.balance);
    }

    /// The deployed code at `at`.
    pub fn code(&self, at: Address) -> Vec<u8> {
        let db = &self.evm.ctx.journaled_state.database;
        let info = &db.cache.accounts.get(&at).expect("deployed account").info;
        return info.code.as_ref().expect("code").original_byte_slice().to_vec();
    }

    /// Credits `who` with `amount` wei.
    pub fn fund(&mut self, who: Address, amount: U256) {
        let db = &mut self.evm.ctx.journaled_state.database;
        let mut info = db.cache.accounts.get(&who).map(|a| a.info.clone()).unwrap_or_default();
        info.balance = amount;
        db.insert_account_info(who, info);
    }
}

fn outcome(result: ExecutionResult) -> Outcome {
    return match result {
        ExecutionResult::Success { gas, output, .. } => Outcome {
            success: true,
            gas: gas.tx_gas_used(),
            output: output.data().to_vec(),
        },
        ExecutionResult::Revert { gas, output, .. } => Outcome {
            success: false,
            gas: gas.tx_gas_used(),
            output: output.to_vec(),
        },
        ExecutionResult::Halt { gas, reason, .. } => Outcome {
            success: false,
            gas: gas.tx_gas_used(),
            output: format!("{reason:?}").into_bytes(),
        },
    };
}
