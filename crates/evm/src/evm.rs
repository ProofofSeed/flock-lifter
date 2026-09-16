// SPDX-License-Identifier: LGPL-3.0-or-later

//! An in-process EVM, configured like Ethereum mainnet except that nothing caps gas or code
//! size, so that a verification larger than a block can still run to completion and be metered.

use std::{path::PathBuf, process::Command, sync::OnceLock};

use revm::{
    Context, ExecuteCommitEvm, MainBuilder, MainContext,
    context::{
        TxEnv,
        result::{ExecutionResult, Output},
    },
    database::{CacheDB, EmptyDB},
    primitives::{Address, Bytes, TxKind, U256, hardfork::SpecId, keccak256},
    state::AccountInfo,
};

/// The caller every transaction is sent from.
const CALLER: Address = Address::new([0x11; 20]);

/// Gas limit given to every transaction.
const GAS: u64 = 1 << 62;

/// The verifier's Foundry project.
pub fn project() -> PathBuf {
    return PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../verifier");
}

/// Builds the contracts once per process.
pub fn build() {
    static BUILT: OnceLock<()> = OnceLock::new();
    BUILT.get_or_init(|| {
        let forge = std::env::var("FORGE").unwrap_or_else(|_| {
            format!("{}/.foundry/bin/forge", std::env::var("HOME").expect("HOME"))
        });
        let status = Command::new(forge)
            .arg("build")
            .arg("--quiet")
            .current_dir(project())
            .status()
            .expect("run forge");
        assert!(status.success(), "forge build failed");
    });
}

/// The creation bytecode of contract `name` in source file `file`.
pub fn artifact(file: &str, name: &str) -> Vec<u8> {
    build();
    let path = project().join("out").join(file).join(format!("{name}.json"));
    let json: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display())))
            .expect("artifact json");
    let hex = json["bytecode"]["object"].as_str().expect("bytecode object");
    return hex::decode(hex.trim_start_matches("0x")).expect("bytecode hex");
}

/// The outcome of one transaction.
#[derive(Clone, Debug)]
pub struct Outcome {
    /// Whether it succeeded.
    pub success: bool,
    /// Gas used, intrinsic gas included.
    pub gas: u64,
    /// Intrinsic gas: the base cost and the calldata.
    pub intrinsic: u64,
    /// Return or revert data.
    pub output: Vec<u8>,
    /// Emitted logs, as `(topics, data)`.
    pub logs: Vec<(Vec<[u8; 32]>, Vec<u8>)>,
}

impl Outcome {
    /// Gas used by execution alone.
    pub fn execution(&self) -> u64 {
        return self.gas - self.intrinsic;
    }

    /// The `i`-th word of the output.
    pub fn word(&self, i: usize) -> [u8; 32] {
        return self.output[32 * i..32 * i + 32].try_into().expect("word");
    }
}

/// Intrinsic gas of a call carrying `data`, under the standard (not floor) calldata price.
pub fn intrinsic(data: &[u8]) -> u64 {
    let zeros = data.iter().filter(|&&b| b == 0).count() as u64;
    return 21_000 + 4 * zeros + 16 * (data.len() as u64 - zeros);
}

/// An EVM with deployed contracts.
pub struct Evm {
    evm: revm::MainnetEvm<revm::handler::MainnetContext<CacheDB<EmptyDB>>>,
    nonce: u64,
}

impl Default for Evm {
    fn default() -> Self {
        return Self::new();
    }
}

impl Evm {
    /// A fresh EVM under the latest mainnet rules.
    pub fn new() -> Self {
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
                cfg.tx_gas_limit_cap = Some(u64::MAX);
                cfg.limit_contract_code_size = Some(usize::MAX);
                cfg.limit_contract_initcode_size = Some(usize::MAX);
                cfg.disable_block_gas_limit = true;
                cfg.disable_base_fee = true;
                cfg.memory_limit = u64::MAX;
            })
            .modify_block_chained(|block| {
                block.gas_limit = GAS;
            });
        return Self {
            evm: ctx.build_mainnet(),
            nonce: 0,
        };
    }

    fn run(&mut self, kind: TxKind, data: Vec<u8>) -> ExecutionResult {
        let tx = TxEnv::builder()
            .caller(CALLER)
            .kind(kind)
            .data(Bytes::from(data))
            .gas_limit(GAS)
            .gas_price(0)
            .nonce(self.nonce)
            .build_fill();
        self.nonce += 1;
        return self.evm.transact_commit(tx).expect("transaction is valid");
    }

    /// Deploys `initcode`, returning the new contract's address and the deployment's gas.
    pub fn deploy(&mut self, initcode: Vec<u8>) -> (Address, u64) {
        match self.run(TxKind::Create, initcode) {
            ExecutionResult::Success {
                output: Output::Create(_, Some(address)),
                gas,
                ..
            } => return (address, gas.tx_gas_used()),
            other => panic!("deployment failed: {other:?}"),
        }
    }

    /// Calls `to` with `data`.
    pub fn call(&mut self, to: Address, data: Vec<u8>) -> Outcome {
        let intrinsic = intrinsic(&data);
        let result = self.run(TxKind::Call(to), data);
        let logs = result
            .logs()
            .iter()
            .map(|l| (l.topics().iter().map(|t| t.0).collect(), l.data.data.to_vec()))
            .collect();
        return match result {
            ExecutionResult::Success { gas, output, .. } => Outcome {
                success: true,
                gas: gas.tx_gas_used(),
                intrinsic,
                output: output.data().to_vec(),
                logs,
            },
            ExecutionResult::Revert { gas, output, .. } => Outcome {
                success: false,
                gas: gas.tx_gas_used(),
                intrinsic,
                output: output.to_vec(),
                logs,
            },
            ExecutionResult::Halt { gas, reason, .. } => Outcome {
                success: false,
                gas: gas.tx_gas_used(),
                intrinsic,
                output: format!("{reason:?}").into_bytes(),
                logs,
            },
        };
    }
}

/// A minimal ABI encoder: the selector, then head words and a tail of dynamic data.
#[derive(Default)]
pub struct Abi {
    head: Vec<[u8; 32]>,
    tail: Vec<u8>,
    dynamic: Vec<(usize, Vec<u8>)>,
}

impl Abi {
    /// A call to the function with signature `sig`.
    pub fn call(sig: &str) -> (Vec<u8>, Self) {
        return (keccak256(sig.as_bytes())[..4].to_vec(), Self::default());
    }

    /// Appends a `uint256` argument.
    pub fn uint(mut self, v: U256) -> Self {
        self.head.push(v.to_be_bytes());
        return self;
    }

    /// Appends a `uint256` argument from a `u128`.
    pub fn u128(self, v: u128) -> Self {
        return self.uint(U256::from(v));
    }

    /// Appends a `bytes` argument.
    pub fn bytes(mut self, b: &[u8]) -> Self {
        let mut enc = (U256::from(b.len())).to_be_bytes::<32>().to_vec();
        enc.extend_from_slice(b);
        enc.resize(32 + b.len().div_ceil(32) * 32, 0);
        self.dynamic.push((self.head.len(), enc));
        self.head.push([0u8; 32]);
        return self;
    }

    /// Appends a `uint256[]` argument.
    pub fn uints(mut self, v: &[U256]) -> Self {
        let mut enc = (U256::from(v.len())).to_be_bytes::<32>().to_vec();
        for x in v {
            enc.extend_from_slice(&x.to_be_bytes::<32>());
        }
        self.dynamic.push((self.head.len(), enc));
        self.head.push([0u8; 32]);
        return self;
    }

    /// The encoded arguments, after `selector`.
    pub fn finish(mut self, selector: Vec<u8>) -> Vec<u8> {
        let head_len = 32 * self.head.len();
        for (slot, enc) in std::mem::take(&mut self.dynamic) {
            self.head[slot] = U256::from(head_len + self.tail.len()).to_be_bytes();
            self.tail.extend_from_slice(&enc);
        }
        let mut out = selector;
        for w in &self.head {
            out.extend_from_slice(w);
        }
        out.extend_from_slice(&self.tail);
        return out;
    }
}

/// Encodes a call to `sig` with the arguments built by `args`.
pub fn encode(sig: &str, args: impl FnOnce(Abi) -> Abi) -> Vec<u8> {
    let (selector, abi) = Abi::call(sig);
    return args(abi).finish(selector);
}
