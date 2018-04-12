/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]

#[macro_use]
extern crate bencher;

mod utils;

use bencher::{black_box, Bencher};
use utils::iterations;
use utils::BencherNoDrop;

fn std_vec_push(bench: &mut Bencher) {
    let limit = iterations(100_000);

    bench.iter_no_drop(|| {
        let mut vector: Vec<usize> = Vec::new();

        for i in 0..limit {
            vector.push(i);
        }

        vector
    });
}

// TODO implement rust_vec_pop in the same style as the test of `Vector::drop_last()` once we can
// do per-iteration initialization.

fn std_vec_get(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut vector: Vec<usize> = Vec::new();

    for i in 0..limit {
        vector.push(i);
    }

    bench.iter(|| {
        for i in 0..limit {
            black_box(vector.get(i as usize));
        }
    });
}

fn std_vec_iterate(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut vector: Vec<usize> = Vec::new();

    for i in 0..limit {
        vector.push(i);
    }

    bench.iter(|| {
        for i in &vector {
            black_box(i);
        }
    });
}

benchmark_group!(benches, std_vec_push, std_vec_get, std_vec_iterate);
benchmark_main!(benches);
