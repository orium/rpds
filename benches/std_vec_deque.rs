/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]

use criterion::{Criterion, criterion_group, criterion_main};
use std::collections::VecDeque;
use std::hint::black_box;

fn std_vec_dequeue_push_back(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("std vec dequeue push back", move |b| {
        b.iter(|| {
            let mut deque: VecDeque<usize> = VecDeque::new();

            for i in 0..limit {
                deque.push_back(i);
            }

            deque
        });
    });
}

fn std_vec_dequeue_pop_front(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("std vec dequeue pop front", move |b| {
        b.iter_with_setup(
            || {
                let mut queue: VecDeque<usize> = VecDeque::new();

                for i in 0..limit {
                    queue.push_back(i);
                }

                queue
            },
            |mut queue| {
                for _ in 0..limit {
                    queue.pop_front();
                }

                queue
            },
        );
    });
}

#[allow(clippy::explicit_iter_loop)]
fn std_vec_dequeue_iterate(c: &mut Criterion) {
    let limit = 100_000;
    let mut deque: VecDeque<usize> = VecDeque::new();

    for i in 0..limit {
        deque.push_back(i);
    }

    c.bench_function("std vec dequeue iterate", move |b| {
        b.iter(|| {
            for i in deque.iter() {
                black_box(i);
            }
        });
    });
}

criterion_group!(
    benches,
    std_vec_dequeue_push_back,
    std_vec_dequeue_pop_front,
    std_vec_dequeue_iterate
);
criterion_main!(benches);
