/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]
#![allow(clippy::cast_possible_wrap)]

use criterion::{Criterion, criterion_group, criterion_main};
use std::collections::BTreeMap;
use std::hint::black_box;

fn std_btree_map_insert(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("std b-tree map insert", move |b| {
        b.iter(|| {
            let mut map: BTreeMap<usize, isize> = BTreeMap::new();

            for i in 0..limit {
                map.insert(i, -(i as isize));
            }

            map
        });
    });
}

fn std_btree_map_remove(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("std btree map remove", move |b| {
        b.iter_with_setup(
            || {
                let mut map = BTreeMap::new();

                for i in 0..limit {
                    map.insert(i, -(i as isize));
                }

                map
            },
            |mut map| {
                for i in 0..limit {
                    map.remove(&i);
                }

                map
            },
        );
    });
}

fn std_btree_map_get(c: &mut Criterion) {
    let limit = 100_000;
    let mut map: BTreeMap<usize, isize> = BTreeMap::new();

    for i in 0..limit {
        map.insert(i, -(i as isize));
    }

    c.bench_function("std b-tree map get", move |b| {
        b.iter(|| {
            for i in 0..limit {
                black_box(map.get(&i));
            }
        });
    });
}

fn std_btree_map_iterate(c: &mut Criterion) {
    let limit = 100_000;
    let mut map: BTreeMap<usize, isize> = BTreeMap::new();

    for i in 0..limit {
        map.insert(i, -(i as isize));
    }

    c.bench_function("std b-tree map iterate", move |b| {
        b.iter(|| {
            for kv in &map {
                black_box(kv);
            }
        });
    });
}

criterion_group!(
    benches,
    std_btree_map_insert,
    std_btree_map_remove,
    std_btree_map_get,
    std_btree_map_iterate
);
criterion_main!(benches);
