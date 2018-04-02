/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use super::*;

#[test]
fn test_cloned_set() {
    let vec: Vec<&str> = vec!["a", "b", "c", "d"];

    assert_eq!(vec.cloned_set(0, "x"), vec!["x", "b", "c", "d"]);
    assert_eq!(vec.cloned_set(2, "x"), vec!["a", "b", "x", "d"]);
    assert_eq!(vec.cloned_set(3, "x"), vec!["a", "b", "c", "x"]);
    assert_eq!(vec.cloned_set(4, "x"), vec!["a", "b", "c", "d", "x"]);
}

#[test]
fn test_cloned_insert() {
    let empty: Vec<&str> = Vec::new();
    let vec: Vec<&str> = vec!["a", "b", "c", "d"];

    assert_eq!(empty.cloned_insert(0, "x"), vec!["x"]);
    assert_eq!(vec.cloned_insert(0, "x"), vec!["x", "a", "b", "c", "d"]);
    assert_eq!(vec.cloned_insert(2, "x"), vec!["a", "b", "x", "c", "d"]);
    assert_eq!(vec.cloned_insert(4, "x"), vec!["a", "b", "c", "d", "x"]);
}

#[test]
fn test_cloned_remove() {
    let vec: Vec<&str> = vec!["a", "b", "c", "d"];

    assert_eq!(vec.cloned_remove(0), vec!["b", "c", "d"]);
    assert_eq!(vec.cloned_remove(2), vec!["a", "b", "d"]);
    assert_eq!(vec.cloned_remove(3), vec!["a", "b", "c"]);
}
