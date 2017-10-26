/* This file is part of rpds.
 *
 * rpds is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * rpds is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with rpds.  If not, see <http://www.gnu.org/licenses/>.
 */

#![cfg_attr(feature = "fatal-warnings", deny(warnings))]

#[macro_use]
extern crate bencher;

mod utils;

use std::collections::HashMap;
use utils::BencherNoDrop;
use bencher::{Bencher, black_box};

fn rust_hashmap_insert(bench: &mut Bencher) -> () {
    let limit = 100_000;

    bench.iter_no_drop(|| {
        let mut map: HashMap<isize, isize> = HashMap::new();

        for i in 0..limit {
            map.insert(i, -i);
        }

        map
    });
}

// TODO implement rust_hashmap_remove in the same style as the test of `HashTrieMap::remove()` once
// we can do per-iteration initialization.

fn rust_hashmap_get(bench: &mut Bencher) -> () {
    let limit = 100_000;
    let mut map: HashMap<isize, isize> = HashMap::new();

    for i in 0..limit {
        map.insert(i, -i);
    }

    bench.iter(|| {
        for i in 0..limit {
            black_box(map.get(&i));
        }
    });
}

fn rust_hashmap_iterate(bench: &mut Bencher) -> () {
    let limit = 100_000;
    let mut map: HashMap<isize, isize> = HashMap::new();

    for i in 0..limit {
        map.insert(i, -i);
    }

    bench.iter(|| {
        for kv in &map {
            black_box(kv);
        }
    });
}

benchmark_group!(benches, rust_hashmap_insert, rust_hashmap_get, rust_hashmap_iterate);
benchmark_main!(benches);
