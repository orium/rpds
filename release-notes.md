# Release notes

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
