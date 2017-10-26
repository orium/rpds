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

use super::*;
use std::mem::size_of;

#[test]
fn test_new() -> () {
    let empty_array: SparseArrayUsize<u32> = SparseArrayUsize::new();

    assert_eq!(empty_array.bitmap, 0);
    assert_eq!(empty_array.array.len(), 0);
    assert_eq!(empty_array.array.capacity(), 0, "Capacity of the branch array is wasteful");
}

#[test]
fn test_set() -> () {
    let mut array = SparseArrayUsize::new();

    assert_eq!(array.size(), 0);
    assert!(array.is_empty());
    assert_eq!(array.get(0), None);
    assert_eq!(array.get(63), None);

    array = array.set(3, 'a');
    assert!(!array.is_empty());
    assert_eq!(array.size(), 1);

    assert_eq!(array.get(2), None);
    assert_eq!(array.get(3), Some(&'a'));
    assert_eq!(array.get(4), None);

    array = array.set(60, 'b');
    assert_eq!(array.size(), 2);

    assert_eq!(array.get(3), Some(&'a'));
    assert_eq!(array.get(60), Some(&'b'));

    array = array.set(3, 'c');
    assert_eq!(array.size(), 2);

    assert_eq!(array.get(3), Some(&'c'));
    assert_eq!(array.get(60), Some(&'b'));
}

#[test]
fn test_remove() -> () {
    let mut array = SparseArrayUsize::new()
        .set(3, 'a')
        .set(60, 'b');

    assert_eq!(array.get(3), Some(&'a'));
    assert_eq!(array.get(60), Some(&'b'));

    array = array.remove(32);

    assert_eq!(array.get(3), Some(&'a'));
    assert_eq!(array.get(60), Some(&'b'));
    assert_eq!(array.size(), 2);

    array = array.remove(3);

    assert_eq!(array.get(3), None);
    assert_eq!(array.get(60), Some(&'b'));
    assert_eq!(array.size(), 1);

    array = array.remove(60);

    assert_eq!(array.get(3), None);
    assert_eq!(array.get(60), None);
    assert_eq!(array.size(), 0);
    assert!(array.is_empty());
}

#[test]
fn test_first_index() -> () {
    let mut array = SparseArrayUsize::new();

    assert_eq!(array.first_index(), None);

    array = array.set(31, 'a');
    assert_eq!(array.first_index(), Some(31));

    array = array.set(60, 'b');
    assert_eq!(array.first_index(), Some(31));

    array = array.set(2, 'c');
    assert_eq!(array.first_index(), Some(2));

    array = array.set(0, 'c');
    assert_eq!(array.first_index(), Some(0));
}

#[test]
fn test_map_index() -> () {
    for i in 0..(8 * size_of::<usize>()) {
        assert_eq!(sparse_array_usize_utils::map_index(0, i), None);
    }

    let bitmap: usize = 0b_1110_0100_0101;

    assert_eq!(sparse_array_usize_utils::map_index(bitmap,  0), Some(0));
    assert_eq!(sparse_array_usize_utils::map_index(bitmap,  1), None);
    assert_eq!(sparse_array_usize_utils::map_index(bitmap,  2), Some(1));
    assert_eq!(sparse_array_usize_utils::map_index(bitmap,  3), None);

    assert_eq!(sparse_array_usize_utils::map_index(bitmap,  4), None);
    assert_eq!(sparse_array_usize_utils::map_index(bitmap,  5), None);
    assert_eq!(sparse_array_usize_utils::map_index(bitmap,  6), Some(2));
    assert_eq!(sparse_array_usize_utils::map_index(bitmap,  7), None);

    assert_eq!(sparse_array_usize_utils::map_index(bitmap,  8), None);
    assert_eq!(sparse_array_usize_utils::map_index(bitmap,  9), Some(3));
    assert_eq!(sparse_array_usize_utils::map_index(bitmap, 10), Some(4));
    assert_eq!(sparse_array_usize_utils::map_index(bitmap, 11), Some(5));

    assert_eq!(sparse_array_usize_utils::map_index(bitmap, 12), None);
}

#[test]
fn test_vec_insert_cloned() -> () {
    let empty: Vec<&str> = Vec::new();
    let vec: Vec<&str> = vec!["a", "b", "c", "d"];

    assert_eq!(SparseArrayUsize::vec_insert_cloned(&empty, "x", 0), vec!["x"]);
    assert_eq!(SparseArrayUsize::vec_insert_cloned(&vec, "x", 0), vec!["x", "a", "b", "c", "d"]);
    assert_eq!(SparseArrayUsize::vec_insert_cloned(&vec, "x", 2), vec!["a", "b", "x", "c", "d"]);
    assert_eq!(SparseArrayUsize::vec_insert_cloned(&vec, "x", 4), vec!["a", "b", "c", "d", "x"]);
}

#[test]
fn test_vec_replace_cloned() -> () {
    let vec: Vec<&str> = vec!["a", "b", "c", "d"];

    assert_eq!(SparseArrayUsize::vec_replace_cloned(&vec, "x", 0), vec!["x", "b", "c", "d"]);
    assert_eq!(SparseArrayUsize::vec_replace_cloned(&vec, "x", 2), vec!["a", "b", "x", "d"]);
    assert_eq!(SparseArrayUsize::vec_replace_cloned(&vec, "x", 3), vec!["a", "b", "c", "x"]);
}

#[test]
fn test_vec_remove_cloned() -> () {
    let vec: Vec<&str> = vec!["a", "b", "c", "d"];

    assert_eq!(SparseArrayUsize::vec_remove_cloned(&vec, 0), vec!["b", "c", "d"]);
    assert_eq!(SparseArrayUsize::vec_remove_cloned(&vec, 2), vec!["a", "b", "d"]);
    assert_eq!(SparseArrayUsize::vec_remove_cloned(&vec, 3), vec!["a", "b", "c"]);
}
