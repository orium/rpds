/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]
#![allow(clippy::cast_possible_wrap)]

use criterion::{Criterion, criterion_group, criterion_main};
use std::collections::HashMap;
use std::hint::black_box;

fn std_hash_map_insert(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("std hash map insert", move |b| {
        b.iter(|| {
            let mut map: HashMap<usize, isize> = HashMap::new();

            for i in 0..limit {
                map.insert(i, -(i as isize));
            }

            map
        });
    });
}

fn std_hash_map_remove(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("std hash map remove", move |b| {
        b.iter_with_setup(
            || {
                let mut map = HashMap::new();

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

fn std_hash_map_get(c: &mut Criterion) {
    let limit = 100_000;
    let mut map: HashMap<usize, isize> = HashMap::new();

    for i in 0..limit {
        map.insert(i, -(i as isize));
    }

    c.bench_function("std hash map get", move |b| {
        b.iter(|| {
            for i in 0..limit {
                black_box(map.get(&i));
            }
        });
    });
}

fn std_hash_map_iterate(c: &mut Criterion) {
    let limit = 100_000;
    let mut map: HashMap<usize, isize> = HashMap::new();

    for i in 0..limit {
        map.insert(i, -(i as isize));
    }

    c.bench_function("std hash map iterate", move |b| {
        b.iter(|| {
            for kv in &map {
                black_box(kv);
            }
        });
    });
}

criterion_group!(
    benches,
    std_hash_map_insert,
    std_hash_map_remove,
    std_hash_map_get,
    std_hash_map_iterate
);
criterion_main!(benches);
