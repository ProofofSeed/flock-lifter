// SPDX-License-Identifier: LGPL-3.0-or-later

//! Runs a lift's verification with every step observed and reports what a step-by-step
//! re-execution would face: steps per call, the opcodes used, stack depth, memory size, and the
//! largest bulk operations.
//!
//! Usage: `trace-stats <responses> <lift-cache-file>`.

use std::{env, time::Instant};

use pofseed_flock_lift_optimistic::{
    machine::{Machine, Sink},
    scenario::{CALLS, Scenario},
};
use revm::interpreter::{Interpreter, interpreter::EthInterpreter, interpreter_types::Jumps};

#[derive(Default)]
struct Stats {
    steps: u64,
    ops: Vec<u64>,
    max_stack: usize,
    max_memory: usize,
    bulk: Vec<(u64, u64)>,
    proved: Vec<(u64, u64)>,
    unsupported: u64,
    calldata_len: u64,
    code_len: u64,
}

/// Opcodes the on-chain interpreter implements.
pub fn supported(op: u8) -> bool {
    return pofseed_flock_lift_optimistic::vm::supported(op);
}

fn word(v: u64) -> u64 {
    return v / 32;
}

impl Sink for Stats {
    fn step(&mut self, interp: &mut Interpreter<EthInterpreter>) {
        let op = interp.bytecode.opcode() as usize;
        self.ops[op] += 1;
        self.max_stack = self.max_stack.max(interp.stack.len());
        self.max_memory = self.max_memory.max(interp.memory.len());
        let size_at = match op {
            0x37 | 0x39 | 0x5e => Some(2),
            0x20 | 0xf3 | 0xfd | 0xa0..=0xa4 => Some(1),
            0xfa => Some(3),
            _ => None,
        };
        if !supported(op as u8) {
            self.unsupported += 1;
        }
        if let Some(k) = size_at {
            let size = interp.stack.peek(k).map(|v| v.saturating_to::<u64>()).unwrap_or(0);
            if size > self.bulk[op].0 {
                self.bulk[op] = (size, self.steps);
            }
            let arg = |i: usize| interp.stack.peek(i).map(|v| v.saturating_to::<u64>()).unwrap_or(0);
            let msize_w = interp.memory.len() as u64 / 32;
            let span = |o: u64, len: u64| if len == 0 { 0 } else { word(o + len - 1) + 1 - word(o) };
            let below = |o: u64, len: u64| {
                if len == 0 || word(o) >= msize_w { 0 } else { (word(o + len - 1) + 1).min(msize_w) - word(o) }
            };
            let words = match op {
                0x20 | 0xf3 => below(arg(0), arg(1)),
                0x37 => {
                    if arg(1) >= self.calldata_len { below(arg(0), arg(2)) } else { 2 * span(arg(0), arg(2)) }
                }
                0x39 => {
                    if arg(1) >= self.code_len { below(arg(0), arg(2)) } else { span(arg(0), arg(2)) }
                }
                0x5e => below(arg(1), arg(2)) + span(arg(0), arg(2)),
                0xfa => below(arg(2), arg(3)) + span(arg(4), arg(5)),
                _ => 0,
            };
            if words > self.proved[op].0 {
                self.proved[op] = (words, self.steps);
            }
        }
        self.steps += 1;
    }

    fn into_any(self: Box<Self>) -> Box<dyn std::any::Any> {
        return self;
    }
}

fn main() {
    let n: usize = env::args().nth(1).map_or(219, |s| s.parse().expect("responses"));
    let cache = env::args().nth(2).expect("lift cache file");
    let mut machine = Machine::new(false);
    let t = Instant::now();
    let scenario = Scenario::new(&mut machine, n, &cache);
    println!("scenario built in {:.1} s", t.elapsed().as_secs_f64());
    let t = Instant::now();
    let plain = scenario.run(&mut machine);
    let code_lens = [machine.code(scenario.lift).len() as u64, machine.code(scenario.matrix).len() as u64];
    println!("untraced run in {:.1} s: success {:?}, gas {:?}", t.elapsed().as_secs_f64(), plain.success, plain.gas);
    let mut outputs = Vec::new();
    let mut total_ops = vec![0u64; 256];
    for i in 0..CALLS {
        let data = scenario.calldata(i, &outputs, &scenario.proof, &scenario.matrix_proof);
        let len = data.len();
        let stats = Stats {
            ops: vec![0; 256],
            bulk: vec![(0, 0); 256],
            proved: vec![(0, 0); 256],
            calldata_len: len as u64,
            code_len: code_lens[i],
            ..Default::default()
        };
        let t = Instant::now();
        let (out, sink) = machine.call_traced(scenario.target(i), data, Some(Box::new(stats)));
        let secs = t.elapsed().as_secs_f64();
        let stats = sink.expect("sink").into_any().downcast::<Stats>().expect("stats");
        assert!(out.success, "call {i} failed");
        assert_eq!(out.output, plain.outputs[i], "call {i}: traced output differs from the untraced one");
        println!(
            "call {i}: calldata {len} B, {} steps in {secs:.1} s ({:.0} steps/s), max stack {}, max memory {} B, output {} B",
            stats.steps,
            stats.steps as f64 / secs,
            stats.max_stack,
            stats.max_memory,
            out.output.len()
        );
        for (op, &(size, at)) in stats.bulk.iter().enumerate() {
            if size > 0 {
                println!("  largest 0x{op:02x}: {size} B at step {at}");
            }
        }
        for (op, &(words, at)) in stats.proved.iter().enumerate() {
            if words > 0 {
                println!("  most words proved by one 0x{op:02x}: {words} at step {at}");
            }
        }
        println!("  unsupported opcodes stepped: {}", stats.unsupported);
        for (a, b) in total_ops.iter_mut().zip(&stats.ops) {
            *a += b;
        }
        outputs.push(out.output);
    }
    println!("opcodes used:");
    for (op, &count) in total_ops.iter().enumerate() {
        if count > 0 {
            println!("  0x{op:02x}: {count}");
        }
    }
    println!("steps in all: {}", total_ops.iter().sum::<u64>());
}
