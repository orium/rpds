/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]

#[macro_use]
extern crate criterion;
extern crate rpds;

mod utils;

use criterion::{black_box, Criterion};
use std::collections::VecDeque;
use utils::limit;

fn std_vec_dequeue_enqueue(c: &mut Criterion) {
    let limit = limit(10_000);

    c.bench_function("std vec dequeue enqueue", move |b| {
        b.iter(|| {
            let mut deque: VecDeque<usize> = VecDeque::new();

            for i in 0..limit {
                deque.push_back(i);
            }

            deque
        })
    });
}

// TODO implement deque_dequeue in the same style once we can do per-iteration initialization.

fn std_vec_dequeue_iterate(c: &mut Criterion) {
    let limit = limit(10_000);
    let mut deque: VecDeque<usize> = VecDeque::new();

    for i in 0..limit {
        deque.push_back(i);
    }

    c.bench_function("std vec dequeue iterate", move |b| {
        b.iter(|| {
            for i in deque.iter() {
                black_box(i);
            }
        })
    });
}

criterion_group!(benches, std_vec_dequeue_enqueue, std_vec_dequeue_iterate);
criterion_main!(benches);
