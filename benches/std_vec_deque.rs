/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]

#[macro_use]
extern crate bencher;
extern crate rpds;

mod utils;

use bencher::{black_box, Bencher};
use std::collections::VecDeque;
use utils::iterations;
use utils::BencherNoDrop;

fn std_vec_dequeue_enqueue(bench: &mut Bencher) {
    let limit = iterations(100_000);

    bench.iter_no_drop(|| {
        let mut deque: VecDeque<usize> = VecDeque::new();

        for i in 0..limit {
            deque.push_back(i);
        }

        deque
    });
}

// TODO implement deque_dequeue in the same style once we can do per-iteration initialization.

fn std_vec_dequeue_iterate(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut deque: VecDeque<usize> = VecDeque::new();

    for i in 0..limit {
        deque.push_back(i);
    }

    bench.iter(|| {
        for i in deque.iter() {
            black_box(i);
        }
    });
}

benchmark_group!(benches, std_vec_dequeue_enqueue, std_vec_dequeue_iterate);
benchmark_main!(benches);
