[![Build Status (master)](https://travis-ci.org/orium/rpds.svg?branch=master)](https://travis-ci.org/orium/rpds)
[![Code Coverage (master)](https://codecov.io/gh/orium/rpds/branch/master/graph/badge.svg)](https://codecov.io/gh/orium/rpds)
[![crates.io](http://meritbadge.herokuapp.com/rpds)](https://crates.io/crates/rpds)
[![Documentation (latest)](https://docs.rs/rpds/badge.svg)](https://docs.rs/rpds/)
[![LGPLv3.0 licensed](https://img.shields.io/badge/license-LGPLv3-blue.svg)](./LICENSE)

# Rust Persistent Data Structures

Rust Persistent Data Structures provides [fully persistent data structures](https://en.wikipedia.org/wiki/Persistent_data_structure)
with structural sharing.

# Data Structures

This crate implements the following data structures:

  1. [`List`](#list)
  2. [`Vector`](#vector)
  3. [`Stack`](#stack)
  4. [`Queue`](#queue)
  5. [`HashTrieMap`](#hashtriemap)
  6. [`HashTrieSet`](#hashtrieset)

## `List`

Your classic functional list.

### Example

```rust
use rpds::List;

let list = List::new().push_front("list");

assert_eq!(list.first(), Some(&"list"));

let a_list = list.push_front("a");

assert_eq!(a_list.first(), Some(&"a"));

let list_dropped = a_list.drop_first().unwrap();

assert_eq!(list_dropped, list);
```

## `Vector`

An sequence that can be indexed.  The implementation is described in
[Understanding Persistent Vector Part 1](http://hypirion.com/musings/understanding-persistent-vector-pt-1)
and [Understanding Persistent Vector Part 2](http://hypirion.com/musings/understanding-persistent-vector-pt-2).

### Example

```rust
use rpds::Vector;

let vector = Vector::new()
    .push_back("I'm")
    .push_back("a")
    .push_back("vector");

assert_eq!(vector[1], "a");

let screaming_vector = vector
    .drop_last().unwrap()
    .push_back("VECTOR!!!");

assert_eq!(screaming_vector[2], "VECTOR!!!");
```

## `Stack`

A LIFO (last in, first out) data structure.  This is just a [`List`](#list) in disguise.

### Example

```rust
use rpds::Stack;

let stack = Stack::new().push("stack");

assert_eq!(stack.peek(), Some(&"stack"));

let a_stack = stack.push("a");

assert_eq!(a_stack.peek(), Some(&"a"));

let stack_popped = a_stack.pop().unwrap();

assert_eq!(stack_popped, stack);
```

## `Queue`

A FIFO (first in, first out) data structure.

### Example

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

## `HashTrieMap`

A map implemented with a hash array mapped trie.  See
[Ideal Hash Trees](https://infoscience.epfl.ch/record/64398/files/idealhashtrees.pdf) for
details.

### Example

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

## `HashTrieSet`

A set implemented with a [`HashTrieMap`](#hashtriemap).

### Example

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
