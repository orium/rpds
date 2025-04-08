# Release notes

## 1.1.1

* Updated dependencies.

## 1.1.0

* Use [triomphe](https://crates.io/crates/triomphe) reference-counting pointer by default in `Sync` data structures,
  which improves their performance.

## 1.0.1

* Fix the tests of `SparseArrayUsize` on 32-bit computers.  This issue did not affect production code which did work 
  correctly on 32-bit platforms.

## 1.0.0

* First stable version.  It’s time to commit to a stable release :).
* Improved performance of equality check for `{HashTrie,RedBlackTree}Map` and `{HashTrie,RedBlackTree}Set`, as well as
  subset and superset checks for `{HashTrie,RedBlackTree}Set` when the references are the same.

## 0.13.0

* Updated archery fixing a soundness bug.  See issue [#18](https://github.com/orium/archery/issues/18).

## 0.12.0

* Implemented `Hash` for `RedBlackTreeSet`.

## 0.11.0

* Added `{HashTrie,RedBlackTree}Map::get_key_value()` and `{HashTrie,RedBlackTree}Set::get()`.

## 0.10.0

* Improved `{HashTrieMap,HashTrieSet}` iteration performance.

## 0.9.0

* Added `{HashTrie,RedBlackTree}Map::get_mut()`.
* Improved `HashTrieMap` performance when using `Rc` pointers.

## 0.8.0

* Added support for `no_std`.

## 0.7.0

* Now the shared pointer type of all data structures use can be parameterizable.  See the
  [Thread safety](./README.md#thread-safety) section in the README for details.
  ([#7](https://github.com/orium/rpds/issues/7))
* Fix bug where dropping long lists would cause a stack overflow.  ([#46](https://github.com/orium/rpds/issues/46))

## 0.6.0

* Implemented `RedBlackTree{Map,Set}::range()` iterator.
* Implemented `IndexMut` and `Vector::get_mut()`.
* Added `#[must_use]` to the immutable methods of all data structures.
* Improved performance of `List::reverse_mut()`.
* Improved performance of `RedBlackTreeSet` serialization.

## 0.5.0

* Mutable methods galore.  Now all data structures offer mutable methods.  These are generally much faster!
* Implemented `Extend` for `Vector`.

## 0.4.0

* Added macros to create data structures with the given values (analog to `vec![]`).
* Added `{HashTrieSet,RedBlackTreeSet}::{is_disjoint(),is_subset(),is_superset()}`.

## 0.3.0
 
* Added support for serialization with serde.
* Speed-up `HashTrieMap::remove()` by ~70%.
* Speed-up `Vector::push_back()` by ~80%.

## 0.2.0

* Implemented `RedBlackTreeMap` data structure.
* Implemented `RedBlackTreeSet` data structure.

## 0.1.0

* Implemented `Queue` data structure.
* Implemented `HashTrieSet` data structure.
* Implemented `Stack` data structure.
* Implemented `List::last()` and `List::reverse()`.

## 0.0.0

* Initial release of rpds.  This release contains these data structures: `List`, `Vector`, and `HashTrieMap`.
