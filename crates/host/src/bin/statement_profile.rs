// SPDX-License-Identifier: LGPL-3.0-or-later

//! Prints the gate counts and response size of the hardened-child statement.

use pofseed_flock_lift_host::{bip32_vector_1, vector_1_proof};
use pofseed_flock_lift_statement::{HardenedChildCircuit, S};
use zkboo_bip32::HARDENED_OFFSET;
use zkboo_profiling::profile;

fn main() {
    let (_, chain_code) = bip32_vector_1();
    let circuit = HardenedChildCircuit::public_only(chain_code, HARDENED_OFFSET);
    let data = profile(&circuit);
    println!("{:#?}", data.gate_counts());
    println!("response data: {:#?}", data.response_data());
    println!("response size: {} B", data.response_size::<S, S>());
    let (_, output, proof) = vector_1_proof(3, b"profile", b"");
    println!("output shape: {:?}", output.shape());
    for response in &proof {
        println!(
            "challenge {} and-msg shape {:?} bytes {}",
            response.challenge().index(),
            response.and_msg_next_party().shape(),
            response.as_bytes().len()
        );
    }
}
