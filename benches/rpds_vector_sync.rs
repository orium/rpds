/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]

use criterion::{criterion_group, criterion_main, Criterion};
use rpds::VectorSync;
use std::hint::black_box;

fn rpds_vector_syncpush_back(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds vector sync push back", move |b| {
        b.iter(|| {
            let mut vector: VectorSync<usize> = VectorSync::new_sync();

            for i in 0..limit {
                vector = vector.push_back(i);
            }

            vector
        });
    });
}

fn rpds_vector_syncpush_back_mut(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds vector sync push back mut", move |b| {
        b.iter(|| {
            let mut vector: VectorSync<usize> = VectorSync::new_sync();

            for i in 0..limit {
                vector.push_back_mut(i);
            }

            vector
        });
    });
}

fn rpds_vector_syncdrop_last(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds vector sync drop last", move |b| {
        b.iter_with_setup(
            || {
                let mut vector: VectorSync<usize> = VectorSync::new_sync();

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

fn rpds_vector_syncdrop_last_mut(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds vector sync drop last mut", move |b| {
        b.iter_with_setup(
            || {
                let mut vector: VectorSync<usize> = VectorSync::new_sync();

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

fn rpds_vector_syncinsert(c: &mut Criterion) {
    let limit = 1 << 12;

    c.bench_function("rpds vector sync insert", move |b| {
        b.iter(|| {
            let mut vector: VectorSync<usize> = VectorSync::new_sync();

            for i in 0..limit {
                vector = vector.insert(vector.len() - i, i).unwrap();
            }

            vector
        });
    });
}

fn rpds_vector_syncinsert_mut(c: &mut Criterion) {
    let limit = 1 << 12;

    c.bench_function("rpds vector sync insert mut", move |b| {
        b.iter(|| {
            let mut vector: VectorSync<usize> = VectorSync::new_sync();

            for i in 0..limit {
                vector.insert_mut(vector.len() - i, i);
            }

            vector
        });
    });
}

fn rpds_vector_syncremove(c: &mut Criterion) {
    let limit = 1 << 12;

    c.bench_function("rpds vector sync remove", move |b| {
        b.iter_with_setup(
            || {
                let mut vector: VectorSync<usize> = VectorSync::new_sync();

                for i in 0..limit {
                    vector.push_back_mut(i);
                }

                vector
            },
            |mut vector| {
                for i in (0..limit).rev() {
                    vector = vector.remove(vector.len() - i - 1).unwrap();
                }

                vector
            },
        );
    });
}

fn rpds_vector_syncremove_mut(c: &mut Criterion) {
    let limit = 1 << 12;

    c.bench_function("rpds vector sync remove mut", move |b| {
        b.iter_with_setup(
            || {
                let mut vector: VectorSync<usize> = VectorSync::new_sync();

                for i in 0..limit {
                    vector.push_back_mut(i);
                }

                vector
            },
            |mut vector| {
                for i in (0..limit).rev() {
                    vector.remove_mut(vector.len() - i - 1);
                }

                vector
            },
        );
    });
}

fn rpds_vector_syncget(c: &mut Criterion) {
    let limit = 1_000_000;
    let mut vector: VectorSync<usize> = VectorSync::new_sync();

    for i in 0..limit {
        vector.push_back_mut(i);
    }

    c.bench_function("rpds vector sync get", move |b| {
        b.iter(|| {
            for i in 0..limit {
                black_box(vector.get(i));
            }
        });
    });
}

#[allow(clippy::explicit_iter_loop)]
fn rpds_vector_synciterate(c: &mut Criterion) {
    let limit = 1_000_000;
    let mut vector: VectorSync<usize> = VectorSync::new_sync();

    for i in 0..limit {
        vector.push_back_mut(i);
    }

    c.bench_function("rpds vector sync iterate", move |b| {
        b.iter(|| {
            for i in vector.iter() {
                black_box(i);
            }
        });
    });
}

criterion_group!(
    benches,
    rpds_vector_syncpush_back,
    rpds_vector_syncpush_back_mut,
    rpds_vector_syncdrop_last,
    rpds_vector_syncdrop_last_mut,
    rpds_vector_syncinsert,
    rpds_vector_syncinsert_mut,
    rpds_vector_syncremove,
    rpds_vector_syncremove_mut,
    rpds_vector_syncget,
    rpds_vector_synciterate
);
criterion_main!(benches);
