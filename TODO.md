* README.md
  * Show the data structures
  * Table with asymptotic complexity
* Publish crate to cargo.io
  * Add badges to `Cargo.toml`
* Trait for all collections/iterators factoring everything common there?
* Unit tests
  * Use property based tests with [quickcheck](https://github.com/BurntSushi/quickcheck)?
* Add more properties to `Cargo.toml`
* Docs
  * list
  * vector
  * hash_trie_map
* HashMap/Set
  * extend
* TreeMap/Set
* Queue
* Stack
  * wrap a list with only push, pop, peek, and size.
* Vector
  * Support `push_front()`/`drop_first()`
  * extend
* List
  * extend
* Macros like `vec!` for all collections.
* Add clippy to travis.
* impl FusedIterator for iterators when it is stable.
