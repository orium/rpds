/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]

#[macro_use]
extern crate criterion;

mod utils;

use criterion::{black_box, Criterion};
use utils::limit;

fn std_vec_push(c: &mut Criterion) {
    let limit = limit(10_000);

    c.bench_function("std vec push", move |b| {
        b.iter(|| {
            let mut vector: Vec<usize> = Vec::new();

            for i in 0..limit {
                vector.push(i);
            }

            vector
        })
    });
}

// TODO implement rust_vec_pop in the same style as the test of `Vector::drop_last()` once we can
// do per-iteration initialization.

fn std_vec_get(c: &mut Criterion) {
    let limit = limit(10_000);
    let mut vector: Vec<usize> = Vec::new();

    for i in 0..limit {
        vector.push(i);
    }

    c.bench_function("std vec get", move |b| {
        b.iter(|| {
            for i in 0..limit {
                black_box(vector.get(i as usize));
            }
        })
    });
}

fn std_vec_iterate(c: &mut Criterion) {
    let limit = limit(10_000);
    let mut vector: Vec<usize> = Vec::new();

    for i in 0..limit {
        vector.push(i);
    }

    c.bench_function("std vec iterate", move |b| {
        b.iter(|| {
            for i in &vector {
                black_box(i);
            }
        })
    });
}

criterion_group!(benches, std_vec_push, std_vec_get, std_vec_iterate);
criterion_main!(benches);
