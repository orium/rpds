/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]

use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;

fn std_vec_push(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("std vec push", move |b| {
        b.iter(|| {
            let mut vector: Vec<usize> = Vec::new();

            for i in 0..limit {
                vector.push(i);
            }

            vector
        });
    });
}

fn std_vec_pop(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("std vec pop", move |b| {
        b.iter_with_setup(
            || {
                let mut vector: Vec<usize> = Vec::new();

                for i in 0..limit {
                    vector.push(i);
                }

                vector
            },
            |mut vector| {
                for _ in 0..limit {
                    vector.pop();
                }

                vector
            },
        );
    });
}

fn std_vec_reverse(c: &mut Criterion) {
    let limit = 10_000;

    c.bench_function("std vec reverse", move |b| {
        b.iter_with_setup(
            || {
                let mut vector: Vec<usize> = Vec::new();

                for i in 0..limit {
                    vector.push(i);
                }

                vector
            },
            |mut vector| {
                for _ in 0..limit {
                    vector.reverse();
                }

                vector
            },
        );
    });
}

fn std_vec_get(c: &mut Criterion) {
    let limit = 100_000;
    let mut vector: Vec<usize> = Vec::new();

    for i in 0..limit {
        vector.push(i);
    }

    c.bench_function("std vec get", move |b| {
        b.iter(|| {
            for i in 0..limit {
                black_box(vector.get(i));
            }
        });
    });
}

fn std_vec_iterate(c: &mut Criterion) {
    let limit = 100_000;
    let mut vector: Vec<usize> = Vec::new();

    for i in 0..limit {
        vector.push(i);
    }

    c.bench_function("std vec iterate", move |b| {
        b.iter(|| {
            for i in &vector {
                black_box(i);
            }
        });
    });
}

criterion_group!(benches, std_vec_push, std_vec_pop, std_vec_reverse, std_vec_get, std_vec_iterate);
criterion_main!(benches);
