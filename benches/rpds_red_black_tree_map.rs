/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]

#[macro_use]
extern crate bencher;
extern crate rpds;

mod utils;

use rpds::RedBlackTreeMap;
use utils::BencherNoDrop;
use utils::iterations;
use bencher::{Bencher, black_box};

fn red_black_tree_map_insert(bench: &mut Bencher) -> () {
    let limit = iterations(100_000);

    bench.iter_no_drop(|| {
        let mut map = RedBlackTreeMap::new();

        for i in 0..limit {
            map = map.insert(i, -(i as isize));
        }

        map
    });
}

fn red_black_tree_map_remove(bench: &mut Bencher) -> () {
    let limit = iterations(100_000);
    let mut full_map = RedBlackTreeMap::new();

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

fn red_black_tree_map_get(bench: &mut Bencher) -> () {
    let limit = iterations(100_000);
    let mut map = RedBlackTreeMap::new();

    for i in 0..limit {
        map = map.insert(i, -(i as isize));
    }

    bench.iter(|| {
        for i in 0..limit {
            black_box(map.get(&i));
        }
    });
}

fn red_black_tree_map_iterate(bench: &mut Bencher) -> () {
    let limit = iterations(100_000);
    let mut map = RedBlackTreeMap::new();

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
    red_black_tree_map_insert, red_black_tree_map_remove, red_black_tree_map_get, red_black_tree_map_iterate
);
benchmark_main!(benches);
