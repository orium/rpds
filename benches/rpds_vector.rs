/* This file is part of rpds.
 *
 * Foobar is free software: you can redistribute it and/or modify
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

#![cfg_attr(not(feature = "no-fatal-warnings"), deny(warnings))]

#[macro_use]
extern crate bencher;
extern crate rpds;

mod utils;

use rpds::vector::Vector;
use utils::BencherNoDrop;
use bencher::{Bencher, black_box};

fn vector_push(bench: &mut Bencher) -> () {
    let limit = 100_000;

    bench.iter_no_drop(|| {
        let mut vector: Vector<isize> = Vector::new();

        for i in 0..limit {
            vector = vector.push(i);
        }

        vector
    });
}

fn vector_drop_last(bench: &mut Bencher) -> () {
    let limit = 100_000;
    let mut full_vector: Vector<isize> = Vector::new();

    for i in 0..limit {
        full_vector = full_vector.push(i);
    }

    bench.iter_no_drop(|| {
        let mut vector: Vector<isize> = full_vector.clone();

        for _ in 0..limit {
            vector = vector.drop_last().unwrap();
        }

        vector
    });
}

fn vector_get(bench: &mut Bencher) -> () {
    let limit = 100_000;
    let mut vector: Vector<isize> = Vector::new();

    for i in 0..limit {
        vector = vector.push(i);
    }

    bench.iter(|| {
        for i in 0..limit {
            black_box(vector.get(i as usize));
        }
    });
}

fn vector_iterate(bench: &mut Bencher) -> () {
    let limit = 100_000;
    let mut vector: Vector<isize> = Vector::new();

    for i in 0..limit {
        vector = vector.push(i);
    }

    bench.iter(|| {
        for i in vector.iter() {
            black_box(i);
        }
    });
}

benchmark_group!(benches, vector_push, vector_drop_last, vector_get, vector_iterate);
benchmark_main!(benches);
