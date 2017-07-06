* Write README.md
  * Table with asymptotic complexity
* Setup travis CI
  * use strict feature: `cargo check --features fatal-warnings`
* Try to create a trait for all collections/iterators factoring everything common there.
* Unit tests
  * Use property based tests with [quickcheck](https://github.com/BurntSushi/quickcheck)?
  * list
* Implement traits for iterators
  * `list::Iter`
* Add more non-fundamental methods to data structures (e.g. `.size()`)
  * list
* Add more properties to `Cargo.toml`
* Docs
  * list / list iter
