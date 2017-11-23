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

use rpds::Vector;
use utils::BencherNoDrop;
use utils::iterations;
use bencher::{Bencher, black_box};

fn vector_push_back(bench: &mut Bencher) -> () {
    let limit = iterations(100_000);

    bench.iter_no_drop(|| {
        let mut vector: Vector<usize> = Vector::new();

        for i in 0..limit {
            vector = vector.push_back(i);
        }

        vector
    });
}

fn vector_drop_last(bench: &mut Bencher) -> () {
    let limit = iterations(100_000);
    let mut full_vector: Vector<usize> = Vector::new();

    for i in 0..limit {
        full_vector = full_vector.push_back(i);
    }

    bench.iter_no_drop(|| {
        let mut vector: Vector<usize> = full_vector.clone();

        for _ in 0..limit {
            vector = vector.drop_last().unwrap();
        }

        vector
    });
}

fn vector_get(bench: &mut Bencher) -> () {
    let limit = iterations(100_000);
    let mut vector: Vector<usize> = Vector::new();

    for i in 0..limit {
        vector = vector.push_back(i);
    }

    bench.iter(|| {
        for i in 0..limit {
            black_box(vector.get(i));
        }
    });
}

fn vector_iterate(bench: &mut Bencher) -> () {
    let limit = iterations(100_000);
    let mut vector: Vector<usize> = Vector::new();

    for i in 0..limit {
        vector = vector.push_back(i);
    }

    bench.iter(|| {
        for i in vector.iter() {
            black_box(i);
        }
    });
}

benchmark_group!(benches, vector_push_back, vector_drop_last, vector_get, vector_iterate);
benchmark_main!(benches);
