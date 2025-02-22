/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]

use criterion::{Criterion, criterion_group, criterion_main};
use rpds::Vector;
use std::hint::black_box;

fn rpds_vector_push_back(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds vector push back", move |b| {
        b.iter(|| {
            let mut vector: Vector<usize> = Vector::new();

            for i in 0..limit {
                vector = vector.push_back(i);
            }

            vector
        });
    });
}

fn rpds_vector_push_back_mut(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds vector push back mut", move |b| {
        b.iter(|| {
            let mut vector: Vector<usize> = Vector::new();

            for i in 0..limit {
                vector.push_back_mut(i);
            }

            vector
        });
    });
}

fn rpds_vector_drop_last(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds vector drop last", move |b| {
        b.iter_with_setup(
            || {
                let mut vector: Vector<usize> = Vector::new();

                for i in 0..limit {
                    vector.push_back_mut(i);
                }

                vector
            },
            |mut vector| {
                for _ in 0..limit {
                    vector = vector.drop_last().unwrap();
                }

                vector
            },
        );
    });
}

fn rpds_vector_drop_last_mut(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds vector drop last mut", move |b| {
        b.iter_with_setup(
            || {
                let mut vector: Vector<usize> = Vector::new();

                for i in 0..limit {
                    vector.push_back_mut(i);
                }

                vector
            },
            |mut vector| {
                for _ in 0..limit {
                    vector.drop_last_mut();
                }

                vector
            },
        );
    });
}

fn rpds_vector_get(c: &mut Criterion) {
    let limit = 100_000;
    let mut vector: Vector<usize> = Vector::new();

    for i in 0..limit {
        vector.push_back_mut(i);
    }

    c.bench_function("rpds vector get", move |b| {
        b.iter(|| {
            for i in 0..limit {
                black_box(vector.get(i));
            }
        });
    });
}

#[allow(clippy::explicit_iter_loop)]
fn rpds_vector_iterate(c: &mut Criterion) {
    let limit = 100_000;
    let mut vector: Vector<usize> = Vector::new();

    for i in 0..limit {
        vector.push_back_mut(i);
    }

    c.bench_function("rpds vector iterate", move |b| {
        b.iter(|| {
            for i in vector.iter() {
                black_box(i);
            }
        });
    });
}

criterion_group!(
    benches,
    rpds_vector_push_back,
    rpds_vector_push_back_mut,
    rpds_vector_drop_last,
    rpds_vector_drop_last_mut,
    rpds_vector_get,
    rpds_vector_iterate
);
criterion_main!(benches);
