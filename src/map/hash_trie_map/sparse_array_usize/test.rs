/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use super::*;
use pretty_assertions::assert_eq;

const USIZE_BITS: usize = usize::BITS as usize;

#[test]
fn test_new() {
    let empty_array: SparseArrayUsize<u32> = SparseArrayUsize::new();

    assert_eq!(empty_array.bitmap, 0);
    assert_eq!(empty_array.array.len(), 0);
    assert_eq!(empty_array.array.capacity(), 0, "Capacity of the branch array is wasteful");
}

#[test]
fn test_set() {
    let mut array = SparseArrayUsize::new();

    assert_eq!(array.size(), 0);
    assert_eq!(array.get(0), None);
    assert_eq!(array.get(USIZE_BITS - 1), None);

    array.set(3, 'a');
    assert_eq!(array.size(), 1);

    assert_eq!(array.get(2), None);
    assert_eq!(array.get(3), Some(&'a'));
    assert_eq!(array.get(4), None);

    array.set(USIZE_BITS - 4, 'b');
    assert_eq!(array.size(), 2);

    assert_eq!(array.get(3), Some(&'a'));
    assert_eq!(array.get(USIZE_BITS - 4), Some(&'b'));

    array.set(3, 'c');
    assert_eq!(array.size(), 2);

    assert_eq!(array.get(3), Some(&'c'));
    assert_eq!(array.get(USIZE_BITS - 4), Some(&'b'));
}

#[test]
fn test_remove() {
    let mut array = SparseArrayUsize::new();

    array.set(3, 'a');
    array.set(USIZE_BITS - 4, 'b');

    assert_eq!(array.get(3), Some(&'a'));
    assert_eq!(array.get(USIZE_BITS - 4), Some(&'b'));

    array.remove(8);

    assert_eq!(array.get(3), Some(&'a'));
    assert_eq!(array.get(USIZE_BITS - 4), Some(&'b'));
    assert_eq!(array.size(), 2);

    array.remove(3);

    assert_eq!(array.get(3), None);
    assert_eq!(array.get(USIZE_BITS - 4), Some(&'b'));
    assert_eq!(array.size(), 1);

    array.remove(USIZE_BITS - 4);

    assert_eq!(array.get(3), None);
    assert_eq!(array.get(USIZE_BITS - 4), None);
    assert_eq!(array.size(), 0);
}

#[test]
fn test_first() {
    let mut array = SparseArrayUsize::new();

    assert_eq!(array.first(), None);

    array.set(8, 'a');
    assert_eq!(array.first(), Some(&'a'));

    array.set(USIZE_BITS - 4, 'b');
    assert_eq!(array.first(), Some(&'a'));

    array.set(2, 'c');
    assert_eq!(array.first(), Some(&'c'));

    array.set(0, 'c');
    assert_eq!(array.first(), Some(&'c'));
}

#[test]
fn test_pop() {
    let mut array = SparseArrayUsize::new();

    array.set(USIZE_BITS - 4, 'b');
    array.set(8, 'a');

    assert_eq!(array.pop(), Some('b'));
    assert_eq!(array.pop(), Some('a'));
    assert_eq!(array.pop(), None);
}

#[test]
fn test_map_index() {
    for i in 0..(usize::BITS as usize) {
        assert_eq!(sparse_array_usize_utils::map_index(0, i), None);
    }

    let bitmap: usize = 0b_1110_0100_0101;

    assert_eq!(sparse_array_usize_utils::map_index(bitmap, 0), Some(0));
    assert_eq!(sparse_array_usize_utils::map_index(bitmap, 1), None);
    assert_eq!(sparse_array_usize_utils::map_index(bitmap, 2), Some(1));
    assert_eq!(sparse_array_usize_utils::map_index(bitmap, 3), None);

    assert_eq!(sparse_array_usize_utils::map_index(bitmap, 4), None);
    assert_eq!(sparse_array_usize_utils::map_index(bitmap, 5), None);
    assert_eq!(sparse_array_usize_utils::map_index(bitmap, 6), Some(2));
    assert_eq!(sparse_array_usize_utils::map_index(bitmap, 7), None);

    assert_eq!(sparse_array_usize_utils::map_index(bitmap, 8), None);
    assert_eq!(sparse_array_usize_utils::map_index(bitmap, 9), Some(3));
    assert_eq!(sparse_array_usize_utils::map_index(bitmap, 10), Some(4));
    assert_eq!(sparse_array_usize_utils::map_index(bitmap, 11), Some(5));

    assert_eq!(sparse_array_usize_utils::map_index(bitmap, 12), None);
}
