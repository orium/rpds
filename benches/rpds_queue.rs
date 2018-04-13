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
use rpds::Queue;
use utils::iterations;
use utils::BencherNoDrop;

fn rpds_queue_enqueue(bench: &mut Bencher) {
    let limit = iterations(100_000);

    bench.iter_no_drop(|| {
        let mut queue: Queue<usize> = Queue::new();

        for i in 0..limit {
            queue = queue.enqueue(i);
        }

        queue
    });
}

fn rpds_queue_enqueue_mut(bench: &mut Bencher) {
    let limit = iterations(100_000);

    bench.iter_no_drop(|| {
        let mut queue: Queue<usize> = Queue::new();

        for i in 0..limit {
            queue.enqueue_mut(i);
        }

        queue
    });
}

fn rpds_queue_dequeue(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut full_queue: Queue<usize> = Queue::new();

    for i in 0..limit {
        full_queue.enqueue_mut(i);
    }

    bench.iter_no_drop(|| {
        let mut queue: Queue<usize> = full_queue.clone();

        for _ in 0..limit {
            queue = queue.dequeue().unwrap();
        }

        queue
    });
}

fn rpds_queue_dequeue_mut(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut full_queue: Queue<usize> = Queue::new();

    for i in 0..limit {
        full_queue.enqueue_mut(i);
    }

    bench.iter_no_drop(|| {
        let mut queue: Queue<usize> = full_queue.clone();

        for _ in 0..limit {
            queue.dequeue_mut();
        }

        queue
    });
}

fn rpds_queue_iterate(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut queue: Queue<usize> = Queue::new();

    for i in 0..limit {
        queue.enqueue_mut(i);
    }

    bench.iter(|| {
        for i in queue.iter() {
            black_box(i);
        }
    });
}

benchmark_group!(
    benches,
    rpds_queue_enqueue,
    rpds_queue_enqueue_mut,
    rpds_queue_dequeue,
    rpds_queue_dequeue_mut,
    rpds_queue_iterate
);
benchmark_main!(benches);
