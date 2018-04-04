/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::sync::Arc;

/// Assigns the content of `src` to `dest`.
pub fn replace<T: Clone>(dest: &mut T, mut src: Arc<T>) {
    // To avoid unnecessary cloning we do this trick.  If we have exclusive ownership of the
    // data pointed to by `src` then no clone is done.
    ::std::mem::swap(dest, Arc::make_mut(&mut src));
}

#[cfg(test)]
mod test;
