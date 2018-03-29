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
use rpds::List;
use utils::BencherNoDrop;
use utils::iterations;

fn list_push_front(bench: &mut Bencher) -> () {
    let limit = iterations(100_000);

    bench.iter_no_drop(|| {
        let mut list: List<usize> = List::new();

        for i in 0..limit {
            list = list.push_front(i);
        }

        list
    });
}

fn list_iterate(bench: &mut Bencher) -> () {
    let limit = iterations(100_000);
    let mut list: List<usize> = List::new();

    for i in 0..limit {
        list = list.push_front(i);
    }

    bench.iter(|| {
        for i in list.iter() {
            black_box(i);
        }
    });
}

benchmark_group!(benches, list_push_front, list_iterate);
benchmark_main!(benches);
