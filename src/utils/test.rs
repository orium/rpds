/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use super::*;
use archery::RcK;
use pretty_assertions::assert_eq;

#[test]
fn test_replace() {
    let src: SharedPointer<_, RcK> = SharedPointer::new(3);
    let mut dest = 0;

    replace(&mut dest, src);

    assert_eq!(dest, 3);
}
