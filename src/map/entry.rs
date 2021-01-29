/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Entry<K, V> {
    pub key: K,
    pub value: V,
}

impl<K, V> Entry<K, V> {
    #[must_use]
    pub fn new(key: K, value: V) -> Entry<K, V> {
        Entry { key, value }
    }
}
