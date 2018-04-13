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
use utils::iterations;
use utils::BencherNoDrop;

fn rpds_list_push_front(bench: &mut Bencher) {
    let limit = iterations(100_000);

    bench.iter_no_drop(|| {
        let mut list: List<usize> = List::new();

        for i in 0..limit {
            list = list.push_front(i);
        }

        list
    });
}

fn rpds_list_push_front_mut(bench: &mut Bencher) {
    let limit = iterations(100_000);

    bench.iter_no_drop(|| {
        let mut list: List<usize> = List::new();

        for i in 0..limit {
            list.push_front_mut(i);
        }

        list
    });
}

fn rpds_list_drop_first(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut full_list: List<usize> = List::new();

    for i in 0..limit {
        full_list.push_front_mut(i);
    }

    bench.iter_no_drop(|| {
        let mut list: List<usize> = full_list.clone();

        for _ in 0..limit {
            list = list.drop_first().unwrap();
        }

        list
    });
}

fn rpds_list_drop_first_mut(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut full_list: List<usize> = List::new();

    for i in 0..limit {
        full_list.push_front_mut(i);
    }

    bench.iter_no_drop(|| {
        let mut list: List<usize> = full_list.clone();

        for _ in 0..limit {
            list.drop_first_mut();
        }

        list
    });
}

fn rpds_list_reverse(bench: &mut Bencher) {
    let limit = iterations(10_000);
    let mut full_list: List<usize> = List::new();

    for i in 0..limit {
        full_list.push_front_mut(i);
    }

    bench.iter_no_drop(|| {
        let mut list: List<usize> = full_list.clone();

        for _ in 0..limit {
            list = list.reverse();
        }

        list
    });
}

fn rpds_list_reverse_mut(bench: &mut Bencher) {
    let limit = iterations(10_000);
    let mut full_list: List<usize> = List::new();

    for i in 0..limit {
        full_list.push_front_mut(i);
    }

    bench.iter_no_drop(|| {
        let mut list: List<usize> = full_list.clone();

        for _ in 0..limit {
            list.reverse_mut();
        }

        list
    });
}

fn rpds_list_iterate(bench: &mut Bencher) {
    let limit = iterations(100_000);
    let mut list: List<usize> = List::new();

    for i in 0..limit {
        list.push_front_mut(i);
    }

    bench.iter(|| {
        for i in list.iter() {
            black_box(i);
        }
    });
}

benchmark_group!(
    benches,
    rpds_list_push_front,
    rpds_list_push_front_mut,
    rpds_list_drop_first,
    rpds_list_drop_first_mut,
    rpds_list_reverse,
    rpds_list_reverse_mut,
    rpds_list_iterate
);
benchmark_main!(benches);
