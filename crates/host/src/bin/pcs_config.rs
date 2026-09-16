// SPDX-License-Identifier: LGPL-3.0-or-later

//! Prints the Ligerito verifier configuration and grinding policies a chunk proof is checked
//! under, for every chunk size the lift uses.

use pofseed_flock_lift::chunk_rm::pcs_params;

fn main() {
    for m in 31..=35 {
        let params = pcs_params(m);
        println!("m = {m}");
        println!("{:#?}", params.ligerito_verifier_config().expect("registered configuration"));
        println!("{:?}", params.zerocheck_grinding());
        println!("{:?}", params.lincheck_grinding());
        println!("{:?}", params.opening_grinding());
        println!("num_ntts {}", params.num_ntts());
    }
}
