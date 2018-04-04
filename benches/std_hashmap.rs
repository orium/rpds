/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]

#[macro_use]
extern crate bencher;

mod utils;

use bencher::{black_box, Bencher};
use std::collections::HashMap;
use utils::iterations;
use utils::BencherNoDrop;

fn std_hashmap_insert(bench: &mut Bencher) {
    let limit = iterations(100_000);

    bench.iter_no_drop(|| {
        let mut map: HashMap<usize, isize> = HashMap::new();

        for i in 0..limit {
            map.insert(i, -(i as isize));
        }

        map
    });
}

// TODO implement rust_hashmap_remove in the same style as the test of `HashTrieMap::remove()` once
// we can do per-iteration initialization.

fn std_hashmap_get(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut map: HashMap<usize, isize> = HashMap::new();

    for i in 0..limit {
        map.insert(i, -(i as isize));
    }

    bench.iter(|| {
        for i in 0..limit {
            black_box(map.get(&i));
        }
    });
}

fn std_hashmap_iterate(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut map: HashMap<usize, isize> = HashMap::new();

    for i in 0..limit {
        map.insert(i, -(i as isize));
    }

    bench.iter(|| {
        for kv in &map {
            black_box(kv);
        }
    });
}

benchmark_group!(
    benches,
    std_hashmap_insert,
    std_hashmap_get,
    std_hashmap_iterate
);
benchmark_main!(benches);
