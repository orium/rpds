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
use rpds::HashTrieMap;
use utils::BencherNoDrop;
use utils::iterations;

fn rpds_hash_trie_map_insert(bench: &mut Bencher) {
    let limit = iterations(100_000);

    bench.iter_no_drop(|| {
        let mut map = HashTrieMap::new();

        for i in 0..limit {
            map = map.insert(i, -(i as isize));
        }

        map
    });
}

fn rpds_hash_trie_map_remove(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut full_map = HashTrieMap::new();

    for i in 0..limit {
        full_map = full_map.insert(i, -(i as isize));
    }

    bench.iter_no_drop(|| {
        let mut map = full_map.clone();

        for i in 0..limit {
            map = map.remove(&i);
        }

        map
    });
}

fn rpds_hash_trie_map_get(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut map = HashTrieMap::new();

    for i in 0..limit {
        map = map.insert(i, -(i as isize));
    }

    bench.iter(|| {
        for i in 0..limit {
            black_box(map.get(&i));
        }
    });
}

fn rpds_hash_trie_map_iterate(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut map = HashTrieMap::new();

    for i in 0..limit {
        map = map.insert(i, -(i as isize));
    }

    bench.iter(|| {
        for kv in map.iter() {
            black_box(kv);
        }
    });
}

benchmark_group!(
    benches,
    rpds_hash_trie_map_insert,
    rpds_hash_trie_map_remove,
    rpds_hash_trie_map_get,
    rpds_hash_trie_map_iterate
);
benchmark_main!(benches);
