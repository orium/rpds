/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]

use criterion::{Criterion, criterion_group, criterion_main};
use rpds::QueueSync;
use std::hint::black_box;

fn rpds_queue_sync_enqueue(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds queue sync enqueue", move |b| {
        b.iter(|| {
            let mut queue: QueueSync<usize> = QueueSync::new_sync();

            for i in 0..limit {
                queue = queue.enqueue(i);
            }

            queue
        });
    });
}

fn rpds_queue_sync_enqueue_mut(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds queue sync enqueue mut", move |b| {
        b.iter(|| {
            let mut queue: QueueSync<usize> = QueueSync::new_sync();

            for i in 0..limit {
                queue.enqueue_mut(i);
            }

            queue
        });
    });
}

fn rpds_queue_sync_dequeue(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds queue sync dequeue", move |b| {
        b.iter_with_setup(
            || {
                let mut queue: QueueSync<usize> = QueueSync::new_sync();

                for i in 0..limit {
                    queue.enqueue_mut(i);
                }

                queue
            },
            |mut queue| {
                for _ in 0..limit {
                    queue = queue.dequeue().unwrap();
                }

                queue
            },
        );
    });
}

fn rpds_queue_sync_dequeue_mut(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds queue sync dequeue mut", move |b| {
        b.iter_with_setup(
            || {
                let mut queue: QueueSync<usize> = QueueSync::new_sync();

                for i in 0..limit {
                    queue.enqueue_mut(i);
                }

                queue
            },
            |mut queue| {
                for _ in 0..limit {
                    queue.dequeue_mut();
                }

                queue
            },
        );
    });
}

#[allow(clippy::explicit_iter_loop)]
fn rpds_queue_sync_iterate(c: &mut Criterion) {
    let limit = 1_000_000;
    let mut queue: QueueSync<usize> = QueueSync::new_sync();

    for i in 0..limit {
        queue.enqueue_mut(i);
    }

    c.bench_function("rpds queue sync iterate", move |b| {
        b.iter(|| {
            for i in queue.iter() {
                black_box(i);
            }
        });
    });
}

criterion_group!(
    benches,
    rpds_queue_sync_enqueue,
    rpds_queue_sync_enqueue_mut,
    rpds_queue_sync_dequeue,
    rpds_queue_sync_dequeue_mut,
    rpds_queue_sync_iterate
);
criterion_main!(benches);
