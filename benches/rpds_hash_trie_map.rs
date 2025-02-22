/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]

use criterion::{Criterion, criterion_group, criterion_main};
use rpds::HashTrieMap;
use std::hint::black_box;

fn rpds_hash_trie_map_insert(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds hash trie map insert", move |b| {
        b.iter(|| {
            let mut map = HashTrieMap::new();

            for i in 0..limit {
                map = map.insert(i, -(i as isize));
            }

            map
        });
    });
}

fn rpds_hash_trie_map_insert_mut(c: &mut Criterion) {
    let limit = 50_000;

    c.bench_function("rpds hash trie map insert mut", move |b| {
        b.iter(|| {
            let mut map = HashTrieMap::new();

            for i in 0..limit {
                map.insert_mut(i, -(i as isize));
            }

            map
        });
    });
}

fn rpds_hash_trie_map_remove(c: &mut Criterion) {
    let limit = 50_000;

    c.bench_function("rpds hash trie map remove", move |b| {
        b.iter_with_setup(
            || {
                let mut map = HashTrieMap::new();

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

fn rpds_hash_trie_map_remove_mut(c: &mut Criterion) {
    let limit = 100_000;

    c.bench_function("rpds hash trie map remove mut", move |b| {
        b.iter_with_setup(
            || {
                let mut map = HashTrieMap::new();

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

fn rpds_hash_trie_map_get(c: &mut Criterion) {
    let limit = 100_000;
    let mut map = HashTrieMap::new();

    for i in 0..limit {
        map.insert_mut(i, -(i as isize));
    }

    c.bench_function("rpds hash trie map get", move |b| {
        b.iter(|| {
            for i in 0..limit {
                black_box(map.get(&i));
            }
        });
    });
}

fn rpds_hash_trie_map_iterate(c: &mut Criterion) {
    let limit = 100_000;
    let mut map = HashTrieMap::new();

    for i in 0..limit {
        map.insert_mut(i, -(i as isize));
    }

    c.bench_function("rpds hash trie map iterate", move |b| {
        b.iter(|| {
            for kv in map.iter() {
                black_box(kv);
            }
        });
    });
}

criterion_group!(
    benches,
    rpds_hash_trie_map_insert,
    rpds_hash_trie_map_insert_mut,
    rpds_hash_trie_map_remove,
    rpds_hash_trie_map_remove_mut,
    rpds_hash_trie_map_get,
    rpds_hash_trie_map_iterate
);
criterion_main!(benches);
