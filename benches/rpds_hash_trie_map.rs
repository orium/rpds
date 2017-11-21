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
extern crate rpds;

mod utils;

use rpds::HashTrieMap;
use utils::BencherNoDrop;
use utils::iterations;
use bencher::{Bencher, black_box};

fn hash_trie_map_insert(bench: &mut Bencher) -> () {
    let limit = iterations(100_000);

    bench.iter_no_drop(|| {
        let mut map = HashTrieMap::new();

        for i in 0..limit {
            map = map.insert(i, -(i as isize));
        }

        map
    });
}

fn hash_trie_map_remove(bench: &mut Bencher) -> () {
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

fn hash_trie_map_get(bench: &mut Bencher) -> () {
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

fn hash_trie_map_iterate(bench: &mut Bencher) -> () {
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
    hash_trie_map_insert, hash_trie_map_remove, hash_trie_map_get, hash_trie_map_iterate
);
benchmark_main!(benches);
