[![Build Status (master)](https://travis-ci.org/orium/rpds.svg?branch=master)](https://travis-ci.org/orium/rpds)
[![Code Coverage (master)](https://codecov.io/gh/orium/rpds/branch/master/graph/badge.svg)](https://codecov.io/gh/orium/rpds)
[![crates.io](https://img.shields.io/crates/v/rpds.svg)](https://crates.io/crates/rpds)
[![Downloads](https://img.shields.io/crates/d/rpds.svg)](https://crates.io/crates/rpds)
[![Github stars](https://img.shields.io/github/stars/orium/rpds.svg?logo=github)](https://github.com/orium/rpds/stargazers)
[![Documentation (latest)](https://docs.rs/rpds/badge.svg)](https://docs.rs/rpds/)
[![License](https://img.shields.io/crates/l/rpds.svg)](./LICENSE.md)

# Rust Persistent Data Structures

Rust Persistent Data Structures provides [fully persistent data structures](https://en.wikipedia.org/wiki/Persistent_data_structure)
with structural sharing.

## Setup

To use rpds add the following to your `Cargo.toml`:

```toml
[dependencies]
rpds = "<version>"
```

## Data Structures

This crate offers the following data structures:

  1. [`List`](#list)
  2. [`Vector`](#vector)
  3. [`Stack`](#stack)
  4. [`Queue`](#queue)
  5. [`HashTrieMap`](#hashtriemap)
  6. [`HashTrieSet`](#hashtrieset)
  7. [`RedBlackTreeMap`](#redblacktreemap)
  8. [`RedBlackTreeSet`](#redblacktreeset)

### `List`
[![List documentation](https://img.shields.io/badge/doc-List-303070.svg)](https://docs.rs/rpds/latest/rpds/list/struct.List.html)

Your classic functional list.

#### Example

```rust
use rpds::List;

let list = List::new().push_front("list");

assert_eq!(list.first(), Some(&"list"));

let a_list = list.push_front("a");

assert_eq!(a_list.first(), Some(&"a"));

let list_dropped = a_list.drop_first().unwrap();

assert_eq!(list_dropped, list);
```

### `Vector`
[![`Vector` documentation](https://img.shields.io/badge/doc-Vector-303070.svg)](https://docs.rs/rpds/latest/rpds/vector/struct.Vector.html)

A sequence that can be indexed.  The implementation is described in
[Understanding Persistent Vector Part 1](http://hypirion.com/musings/understanding-persistent-vector-pt-1)
and [Understanding Persistent Vector Part 2](http://hypirion.com/musings/understanding-persistent-vector-pt-2).

#### Example

```rust
use rpds::Vector;

let vector = Vector::new()
    .push_back("I’m")
    .push_back("a")
    .push_back("vector");

assert_eq!(vector[1], "a");

let screaming_vector = vector
    .drop_last().unwrap()
    .push_back("VECTOR!!!");

assert_eq!(screaming_vector[2], "VECTOR!!!");
```

### `Stack`
[![`Stack` documentation](https://img.shields.io/badge/doc-Stack-303070.svg)](https://docs.rs/rpds/latest/rpds/stack/struct.Stack.html)

A LIFO (last in, first out) data structure.  This is just a [`List`](#list) in disguise.

#### Example

```rust
use rpds::Stack;

let stack = Stack::new().push("stack");

assert_eq!(stack.peek(), Some(&"stack"));

let a_stack = stack.push("a");

assert_eq!(a_stack.peek(), Some(&"a"));

let stack_popped = a_stack.pop().unwrap();

assert_eq!(stack_popped, stack);
```

### `Queue`
[![`Queue` documentation](https://img.shields.io/badge/doc-Queue-303070.svg)](https://docs.rs/rpds/latest/rpds/queue/struct.Queue.html)

A FIFO (first in, first out) data structure.

#### Example

```rust
use rpds::Queue;

let queue = Queue::new()
    .enqueue("um")
    .enqueue("dois")
    .enqueue("tres");

assert_eq!(queue.peek(), Some(&"um"));

let queue_dequeued = queue.dequeue().unwrap();

assert_eq!(queue_dequeued.peek(), Some(&"dois"));
```

### `HashTrieMap`
[![`HashTrieMap` documentation](https://img.shields.io/badge/doc-HashTrieMap-303070.svg)](https://docs.rs/rpds/latest/rpds/map/hash_trie_map/struct.HashTrieMap.html)

A map implemented with a [hash array mapped trie](https://en.wikipedia.org/wiki/Hash_array_mapped_trie).
See [Ideal Hash Trees](https://infoscience.epfl.ch/record/64398/files/idealhashtrees.pdf) for
details.

#### Example

```rust
use rpds::HashTrieMap;

let map_en = HashTrieMap::new()
    .insert(0, "zero")
    .insert(1, "one");

assert_eq!(map_en.get(&1), Some(&"one"));

let map_pt = map_en
    .insert(1, "um")
    .insert(2, "dois");

assert_eq!(map_pt.get(&2), Some(&"dois"));

let map_pt_binary = map_pt.remove(&2);

assert_eq!(map_pt_binary.get(&2), None);
```

### `HashTrieSet`
[![`HashTrieSet` documentation](https://img.shields.io/badge/doc-HashTrieSet-303070.svg)](https://docs.rs/rpds/latest/rpds/set/hash_trie_set/struct.HashTrieSet.html)

A set implemented with a [`HashTrieMap`](#hashtriemap).

#### Example

```rust
use rpds::HashTrieSet;

let set = HashTrieSet::new()
    .insert("zero")
    .insert("one");

assert!(set.contains(&"one"));

let set_extended = set.insert("two");

assert!(set_extended.contains(&"two"));

let set_positive = set_extended.remove(&"zero");

assert!(!set_positive.contains(&"zero"));
```

### `RedBlackTreeMap`
[![`RedBlackTreeMap` documentation](https://img.shields.io/badge/doc-RedBlackTreeMap-303070.svg)](https://docs.rs/rpds/latest/rpds/map/red_black_tree_map/struct.RedBlackTreeMap.html)

A map implemented with a [red-black tree](https://en.wikipedia.org/wiki/Red-Black_tree).

#### Example

```rust
use rpds::RedBlackTreeMap;

let map_en = RedBlackTreeMap::new()
    .insert(0, "zero")
    .insert(1, "one");

assert_eq!(map_en.get(&1), Some(&"one"));

let map_pt = map_en
    .insert(1, "um")
    .insert(2, "dois");

assert_eq!(map_pt.get(&2), Some(&"dois"));

let map_pt_binary = map_pt.remove(&2);

assert_eq!(map_pt_binary.get(&2), None);

assert_eq!(map_pt_binary.first(), Some((&0, &"zero")));
```

### `RedBlackTreeSet`
[![`RedBlackTreeSet` documentation](https://img.shields.io/badge/doc-RedBlackTreeSet-303070.svg)](https://docs.rs/rpds/latest/rpds/set/red_black_tree_set/struct.RedBlackTreeSet.html)

A set implemented with a [`RedBlackTreeMap`](#redblacktreemap).

#### Example

```rust
use rpds::RedBlackTreeSet;

let set = RedBlackTreeSet::new()
    .insert("zero")
    .insert("one");

assert!(set.contains(&"one"));

let set_extended = set.insert("two");

assert!(set_extended.contains(&"two"));

let set_positive = set_extended.remove(&"zero");

assert!(!set_positive.contains(&"zero"));

assert_eq!(set_positive.first(), Some(&"one"));
```

## Other Features

### Mutable Methods

When you change a data structure you often do not need its previous versions.  For those cases
rpds offers you mutable methods which are generally faster:

```rust
use rpds::HashTrieSet;

let mut set = HashTrieSet::new();

set.insert_mut("zero");
set.insert_mut("one");

let set_0_1 = set.clone();
let set_0_1_2 = set.insert("two");
```

### Initialization Macros

There are convenient initialization macros for all data structures:

```rust
use rpds::*;

let vector = vector![3, 1, 4, 1, 5];
let map = ht_map!["orange" => "orange", "banana" => "yellow"];
```

Check the documentation for initialization macros of other data structures.

### Serialization

We support serialization through [serde](https://crates.io/crates/serde).  To use it
enable the `serde` feature.  To do so change the rpds dependency in your `Cargo.toml` to

```toml
[dependencies]
rpds = { version = "<version>", features = ["serde"] }
```
