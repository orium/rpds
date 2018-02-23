/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use bencher::Bencher;

pub trait BencherNoDrop {
    /// Runs the given benchmark function.  The return values of the function will be dropped
    /// outside of the benchmark iteration and therefore the drop time will not be counted.
    fn iter_no_drop<T, F>(&mut self, inner: F) -> ()
    where
        F: FnMut() -> T;
}

impl BencherNoDrop for Bencher {
    fn iter_no_drop<T, F>(&mut self, mut inner: F) -> ()
    where
        F: FnMut() -> T,
    {
        let mut to_drop = Vec::with_capacity(1_000_000);
        let initial_capacity = to_drop.capacity();

        self.iter(|| {
            to_drop.push(inner());
        });

        assert_eq!(initial_capacity, to_drop.capacity(),
                   "Vector of to-be-dropped values was resized.  This might have impacted the benchmark measurement.");
    }
}

/// To avoid long benchmarks running in the CI system we limit the iteration number to *2*.
pub fn iterations(n: usize) -> usize {
    match ::std::env::var("CI") {
        Ok(ref v) if v == "true" => 2,
        _ => n,
    }
}
