/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

/// To avoid long benchmarks running with `QUICK_BENCH`.
/// This is used to test that the benchmarks are correctly defined without taking a lot of time,
/// which is what we want in the CI environment.
pub fn limit(n: usize) -> usize {
    match ::std::env::var("QUICK_BENCH") {
        Ok(ref v) if v == "true" => 2,
        _ => n,
    }
}
