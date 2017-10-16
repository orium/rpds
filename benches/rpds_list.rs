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

use rpds::list::List;
use utils::BencherNoDrop;
use bencher::{Bencher, black_box};

fn list_cons(bench: &mut Bencher) -> () {
    let limit = 100_000;

    bench.iter_no_drop(|| {
        let mut list: List<isize> = List::new();

        for i in 0..limit {
            list = list.cons(i);
        }

        list
    });
}

fn list_iterate(bench: &mut Bencher) -> () {
    let limit = 100_000;
    let mut list: List<isize> = List::new();

    for i in 0..limit {
        list = list.cons(i);
    }

    bench.iter(|| {
        for i in list.iter() {
            black_box(i);
        }
    });
}

benchmark_group!(benches, list_cons, list_iterate);
benchmark_main!(benches);
