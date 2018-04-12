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
use rpds::Vector;
use utils::iterations;
use utils::BencherNoDrop;

fn rpds_vector_push_back(bench: &mut Bencher) {
    let limit = iterations(100_000);

    bench.iter_no_drop(|| {
        let mut vector: Vector<usize> = Vector::new();

        for i in 0..limit {
            vector = vector.push_back(i);
        }

        vector
    });
}

fn rpds_vector_push_back_mut(bench: &mut Bencher) {
    let limit = iterations(100_000);

    bench.iter_no_drop(|| {
        let mut vector: Vector<usize> = Vector::new();

        for i in 0..limit {
            vector.push_back_mut(i);
        }

        vector
    });
}

fn rpds_vector_drop_last(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut full_vector: Vector<usize> = Vector::new();

    for i in 0..limit {
        full_vector = full_vector.push_back(i);
    }

    bench.iter_no_drop(|| {
        let mut vector: Vector<usize> = full_vector.clone();

        for _ in 0..limit {
            vector = vector.drop_last().unwrap();
        }

        vector
    });
}

fn rpds_vector_drop_last_mut(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut full_vector: Vector<usize> = Vector::new();

    for i in 0..limit {
        full_vector.push_back_mut(i);
    }

    bench.iter_no_drop(|| {
        let mut vector: Vector<usize> = full_vector.clone();

        for _ in 0..limit {
            vector.drop_last_mut();
        }

        vector
    });
}

fn rpds_vector_get(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut vector: Vector<usize> = Vector::new();

    for i in 0..limit {
        vector = vector.push_back(i);
    }

    bench.iter(|| {
        for i in 0..limit {
            black_box(vector.get(i));
        }
    });
}

fn rpds_vector_iterate(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut vector: Vector<usize> = Vector::new();

    for i in 0..limit {
        vector = vector.push_back(i);
    }

    bench.iter(|| {
        for i in vector.iter() {
            black_box(i);
        }
    });
}

benchmark_group!(
    benches,
    rpds_vector_push_back,
    rpds_vector_push_back_mut,
    rpds_vector_drop_last,
    rpds_vector_drop_last_mut,
    rpds_vector_get,
    rpds_vector_iterate
);
benchmark_main!(benches);
