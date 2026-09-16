// SPDX-License-Identifier: LGPL-3.0-or-later

//! Putting the machine on chain for a scenario: the programs' code held in data contracts, the
//! one-step contract, and its jump tables, each transaction metered.

use pofseed_flock_lift_evm::evm::{Abi, artifact, encode};
use revm::primitives::{Address, B256, U256};

use crate::{
    machine::{CALLER, Machine},
    scenario::Scenario,
    vm::{Ctx, Snap, Witness},
};

/// Data bytes per holding contract, as `CodeStore.CHUNK`.
pub const CHUNK: usize = 24_000;

/// The chain identifier the machine sees.
pub const CHAIN_ID: u64 = 1;

/// The deployed one-step contract and what deploying it cost.
pub struct OnChain {
    /// The one-step contract.
    pub onestep: Address,
    /// Gas of every deployment transaction, labelled.
    pub gas: Vec<(String, u64)>,
}

fn address_of(out: &[u8]) -> Address {
    return Address::from_slice(&out[12..32]);
}

fn put_all(machine: &mut Machine, store: Address, code: &[u8], label: &str, gas: &mut Vec<(String, u64)>) -> Vec<Address> {
    let mut out = Vec::new();
    for (i, chunk) in code.chunks(CHUNK).enumerate() {
        let res = machine.call(store, encode("put(bytes)", |a| a.bytes(chunk)));
        assert!(res.success, "put failed");
        gas.push((format!("{label} code chunk {i}"), res.gas));
        out.push(address_of(&res.output));
    }
    return out;
}

/// Deploys the one-step contract for `scenario`, whose stream's word tree has root
/// `stream_root`.
pub fn deploy(machine: &mut Machine, scenario: &Scenario, stream_root: B256) -> OnChain {
    let mut gas = Vec::new();
    let (store, g) = machine.deploy(artifact("Store.sol", "Store"));
    gas.push(("store".into(), g));
    let lift_code = machine.code(scenario.lift);
    let discharge_code = machine.code(scenario.discharge);
    let lift_chunks = put_all(machine, store, &lift_code, "lift", &mut gas);
    let discharge_chunks = put_all(machine, store, &discharge_code, "discharge", &mut gas);
    let addr = |a: &Address| U256::from_be_slice(a.as_slice());
    let args = Abi::default()
        .uints(&lift_chunks.iter().map(addr).collect::<Vec<_>>())
        .uint(U256::from(lift_code.len()))
        .uints(&discharge_chunks.iter().map(addr).collect::<Vec<_>>())
        .uint(U256::from(discharge_code.len()))
        .uint(addr(&scenario.lift))
        .uint(addr(&scenario.discharge))
        .uint(U256::from_be_bytes(stream_root.0))
        .uint(U256::from(scenario.stream.len()))
        .uint(addr(&CALLER))
        .uint(U256::from(CHAIN_ID))
        .finish(Vec::new());
    let mut code = artifact("OneStep.sol", "OneStep");
    code.extend_from_slice(&args);
    let (onestep, g) = machine.deploy(code);
    gas.push(("one-step contract".into(), g));
    for which in 0..2 {
        let res = machine.call(onestep, encode("buildJumps(uint256)", |a| a.uint(U256::from(which))));
        assert!(res.success, "buildJumps failed: {}", String::from_utf8_lossy(&res.output));
        gas.push((format!("jump table {which}"), res.gas));
    }
    return OnChain { onestep, gas };
}

/// Calldata of a one-step call.
pub fn step_calldata(pre: &[U256; 5], snap: &Snap, ctx: &Ctx, witness: &Witness) -> Vec<u8> {
    let cx = ctx.words();
    return encode("step(uint256[5],uint256[],bytes,uint256[8],bytes)", |a| {
        let mut a = a;
        for v in pre {
            a = a.uint(*v);
        }
        a = a.uints(&snap.stack).bytes(&snap.ret);
        for word in cx {
            a = a.uint(U256::from_be_bytes(word));
        }
        a.bytes(&witness.encode())
    });
}
