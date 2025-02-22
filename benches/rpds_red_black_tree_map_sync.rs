/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]

use criterion::{Criterion, criterion_group, criterion_main};
use rpds::RedBlackTreeMapSync;
use std::hint::black_box;

fn rpds_red_black_tree_map_sync_insert(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds red black tree map sync insert", move |b| {
        b.iter(|| {
            let mut map = RedBlackTreeMapSync::new_sync();

            for i in 0..limit {
                map = map.insert(i, -(i as isize));
            }

            map
        });
    });
}

fn rpds_red_black_tree_map_sync_insert_mut(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds red black tree map sync insert mut", move |b| {
        b.iter(|| {
            let mut map = RedBlackTreeMapSync::new_sync();

            for i in 0..limit {
                map.insert_mut(i, -(i as isize));
            }

            map
        });
    });
}

fn rpds_red_black_tree_map_sync_remove(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds red black tree map sync remove", move |b| {
        b.iter_with_setup(
            || {
                let mut map = RedBlackTreeMapSync::new_sync();

                for i in 0..limit {
                    map.insert_mut(i, -(i as isize));
                }

                map
            },
            |mut map| {
                for i in 0..limit {
                    map = map.remove(&i);
                }

                map
            },
        );
    });
}

fn rpds_red_black_tree_map_sync_remove_mut(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds red black tree map sync remove mut", move |b| {
        b.iter_with_setup(
            || {
                let mut map = RedBlackTreeMapSync::new_sync();

                for i in 0..limit {
                    map.insert_mut(i, -(i as isize));
                }

                map
            },
            |mut map| {
                for i in 0..limit {
                    map.remove_mut(&i);
                }

                map
            },
        );
    });
}

fn rpds_red_black_tree_map_sync_get(c: &mut Criterion) {
    let limit = 100_000;
    let mut map = RedBlackTreeMapSync::new_sync();

    for i in 0..limit {
        map.insert_mut(i, -(i as isize));
    }

    c.bench_function("rpds red black tree map sync get", move |b| {
        b.iter(|| {
            for i in 0..limit {
                black_box(map.get(&i));
            }
        });
    });
}

#[allow(clippy::explicit_iter_loop)]
fn rpds_red_black_tree_map_sync_iterate(c: &mut Criterion) {
    let limit = 1_000_000;
    let mut map = RedBlackTreeMapSync::new_sync();

    for i in 0..limit {
        map.insert_mut(i, -(i as isize));
    }

    c.bench_function("rpds red black tree map sync iterate", move |b| {
        b.iter(|| {
            for kv in map.iter() {
                black_box(kv);
            }
        });
    });
}

criterion_group!(
    benches,
    rpds_red_black_tree_map_sync_insert,
    rpds_red_black_tree_map_sync_insert_mut,
    rpds_red_black_tree_map_sync_remove,
    rpds_red_black_tree_map_sync_remove_mut,
    rpds_red_black_tree_map_sync_get,
    rpds_red_black_tree_map_sync_iterate
);
criterion_main!(benches);
