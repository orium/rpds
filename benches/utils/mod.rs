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

use bencher::Bencher;

pub trait BencherNoDrop {
    /// Runs the given benchmark function.  The return values of the function will be dropped
    /// outside of the benchmark iteration and therefore the drop time will not be counted.
    fn iter_no_drop<T, F>(&mut self, inner: F) -> ()
        where F: FnMut() -> T;
}

impl BencherNoDrop for Bencher {
    fn iter_no_drop<T, F>(&mut self, mut inner: F) -> ()
        where F: FnMut() -> T {
        let mut to_drop = Vec::with_capacity(1_000_000);
        let initial_capacity = to_drop.capacity();

        self.iter(|| {
            to_drop.push(inner());
        });

        assert_eq!(initial_capacity, to_drop.capacity(),
                   "Vector of to-be-dropped values was resized.  This might have impacted the benchmark measurement.");
    }
}
