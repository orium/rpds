/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

mod sparse_array_usize;

use std::vec::Vec;
use std::slice;
use std::sync::Arc;
use std::borrow::Borrow;
use std::hash::Hash;
use std::hash::BuildHasher;
use std::collections::hash_map::RandomState;
use std::mem::size_of;
use std::ops::Index;
use std::iter::Peekable;
use std::iter::FromIterator;
use std::fmt::Display;
use sequence::list;
use List;
use super::entry::Entry;
use self::sparse_array_usize::SparseArrayUsize;

type HashValue = u64;

// TODO Use impl trait instead of this when available.
pub type Iter<'a, K, V> = ::std::iter::Map<IterArc<'a, K, V>, fn(&'a Arc<Entry<K, V>>) -> (&'a K, &'a V)>;
pub type IterKeys<'a, K, V>   = ::std::iter::Map<Iter<'a, K, V>, fn((&'a K, &V)) -> &'a K>;
pub type IterValues<'a, K, V> = ::std::iter::Map<Iter<'a, K, V>, fn((&K, &'a V)) -> &'a V>;

const DEFAULT_DEGREE: u8 = 8 * size_of::<usize>() as u8;

/// Creates a [`HashTrieMap`](map/hash_trie_map/struct.HashTrieMap.html) containing the given
/// arguments:
///
/// ```
/// # use rpds::*;
/// #
/// let m = HashTrieMap::new()
///     .insert(1, "one")
///     .insert(2, "two")
///     .insert(3, "three");
///
/// assert_eq!(ht_map![1 => "one", 2 => "two", 3 => "three"], m);
/// ```
#[macro_export]
macro_rules! ht_map {
    ($($k:expr => $v:expr),*) => {
        {
            #[allow(unused_mut)]
            let mut m = $crate::HashTrieMap::new();
            $(
                m = m.insert($k, $v);
            )*
            m
        }
    };
}

/// A persistent map with structural sharing.  This implementation uses a
/// [hash array mapped trie](https://en.wikipedia.org/wiki/Hash_array_mapped_trie) and supports
/// fast `insert()`, `remove()`, and `get()`.
///
/// # Complexity
///
/// Let *n* be the number of elements in the map.
///
/// ## Temporal complexity
///
/// | Operation                  | Best case | Average   | Worst case  |
/// |:-------------------------- | ---------:| ---------:| -----------:|
/// | `new()`                    |      Θ(1) |      Θ(1) |        Θ(1) |
/// | `insert()`                 |      Θ(1) |      Θ(1) |        Θ(n) |
/// | `remove()`                 |      Θ(1) |      Θ(1) |        Θ(n) |
/// | `get()`                    |      Θ(1) |      Θ(1) |        Θ(n) |
/// | `contains_key()`           |      Θ(1) |      Θ(1) |        Θ(n) |
/// | `size()`                   |      Θ(1) |      Θ(1) |        Θ(1) |
/// | `clone()`                  |      Θ(1) |      Θ(1) |        Θ(1) |
/// | iterator creation          |      Θ(1) |      Θ(1) |        Θ(1) |
/// | iterator step              |      Θ(1) |      Θ(1) |        Θ(1) |
/// | iterator full              |      Θ(n) |      Θ(n) |        Θ(n) |
///
/// # Implementation details
///
/// This implementation uses a [hash array mapped trie](https://en.wikipedia.org/wiki/Hash_array_mapped_trie).
/// Details can be found in [Ideal Hash Trees](https://infoscience.epfl.ch/record/64398/files/idealhashtrees.pdf).
///
/// See the `Node` documentation for details.
#[derive(Debug)]
pub struct HashTrieMap<K, V, H: BuildHasher = RandomState> {
    root: Arc<Node<K, V>>,
    size: usize,
    degree: u8,
    hasher_builder: H,
}

/// This map works like a trie that breaks the hash of the key in segments, and the segments are
/// used as the index in the trie branches.
///
/// Consider the following example, where we have a tree with degree 16 (e.g. each level uses 4
/// bits of the hash) and the following mapping between keys and their hashes:
///
/// | *key*   | *hash(key)*                       |
/// | ------- | ---------------------------------:|
/// |   *A*   | `0b_0000_0000_···_0000_0010_0110` |
/// |   *B*   | `0b_0000_0000_···_0000_0001_0110` |
/// |   *C*   | `0b_0000_0000_···_0000_0100_0010` |
/// |   *D*   | `0b_0111_0000_···_0000_0000_1000` |
/// |   *E*   | `0b_0111_0000_···_0000_0000_1000` |
///
/// Then the tree will look like this:
///
/// ```text
///        0  ···  2  ···  6  ···  8  ···
///      ├───┼───┼───┼───┼───┼───┼───┼───┤
///      │ ∅ │ ∅ │ C │ ∅ │ • │ ∅ │ • │ ∅ │                depth 0
///      └───┴───┴───┴───┴─│─┴───┴─│─┴───┘
///                       ╱         ╲
///                      ╱           ╲
///                     ╱             ╲
///         0   1   2  ···            0   1   2  ···
///       ├───┼───┼───┼───┤         ├───┼───┼───┼───┤
///       │ ∅ │ B │ A │ ∅ │         │ • │ ∅ │ ∅ │ ∅ │     depth 1
///       └───┴───┴───┴───┘         └─│─┴───┴───┴───┘
///                                   │
///                                   ·
///                                   ·
///                                   ·
///                                   │
///                            0  ···   7   ···
///                          ├───┼───┼─────┼───┤
///                          │ ∅ │ ∅ │ D E │ ∅ │          depth 16 (maximum depth)
///                          └───┴───┴─────┴───┘
/// ```
///
/// Note that we stop the insertion process early when possible.  In the example above we did not
/// had to expand the tree any further to accommodate *C*, since there is no other entry with a
/// hash that starts with `0b0010`.  The entries *A* and *B* exemplifies the case where a single
/// level is not enough because their hash both start with `0b0110`.  In case of a full hash
/// collision we dig through all the levels of the tree so we get to the final leaf where a
/// collision exists, like we can see in the case of *D* and *E*.
///
/// # Invariants
///
/// The tree has the following invariants (among others):
///
///   1. The root is the only node that can have zero children.
///   2. A node with a collision can only exist at the maximum depth of the tree.
///   3. A non-root branch always have two or more entries under it (because it could be
///      compressed).
#[derive(Debug, PartialEq, Eq)]
enum Node<K, V> {
    Branch(SparseArrayUsize<Arc<Node<K, V>>>),
    Leaf(Bucket<K, V>),
}

#[derive(Debug, PartialEq, Eq)]
enum Bucket<K, V> {
    Single(EntryWithHash<K, V>),
    Collision(List<EntryWithHash<K, V>>),
}

#[derive(Debug, PartialEq, Eq)]
struct EntryWithHash<K, V> {
    entry: Arc<Entry<K, V>>,
    key_hash: HashValue,
}

mod node_utils {
    use super::HashValue;
    use std::hash::BuildHasher;
    use std::hash::Hasher;
    use std::hash::Hash;
    use std::mem::size_of_val;

    // Returns the index of the array for the given hash on depth `depth`.
    //
    // When the hash is exhausted, meaning that we are at the maximum depth, this returns `None`.
    #[inline]
    pub fn index_from_hash(hash: HashValue, depth: usize, degree: u8) -> Option<usize> {
        debug_assert!(degree.is_power_of_two());

        let shift = depth as u32 * degree.trailing_zeros();

        if (shift as usize) < 8 * size_of_val(&hash) {
            let mask = degree as HashValue - 1;
            Some(((hash >> shift) & mask) as usize)
        } else {
            None
        }
    }

    pub fn hash<T: ?Sized + Hash, H: BuildHasher>(v: &T, hasher_builder: &H) -> HashValue {
        let mut hasher = hasher_builder.build_hasher();

        v.hash(&mut hasher);

        hasher.finish()
    }
}

impl<K, V> Node<K, V>
    where K: Eq + Hash {
    fn new_empty_branch() -> Node<K, V> {
        Node::Branch(SparseArrayUsize::new())
    }

    fn get<Q: ?Sized>(&self, key: &Q, key_hash: HashValue, depth: usize, degree: u8) -> Option<&EntryWithHash<K, V>>
        where K: Borrow<Q>,
              Q: Hash + Eq {
        match *self {
            Node::Branch(ref subtrees) => {
                let index: usize = node_utils::index_from_hash(key_hash, depth, degree)
                    .expect("hash cannot be exhausted if we are on a branch");

                subtrees.get(index)
                    .and_then(|subtree| subtree.get(key, key_hash, depth + 1, degree))
            },
            Node::Leaf(ref bucket) => bucket.get(key, key_hash),
        }
    }

    /// Returns a pair with the node with the new entry and whether the key is new.
    fn insert(&self, entry: EntryWithHash<K, V>, depth: usize, degree: u8) -> (Node<K, V>, bool) {
        match *self {
            Node::Branch(ref subtrees) => {
                let index: usize = node_utils::index_from_hash(entry.key_hash, depth, degree)
                    .expect("hash cannot be exhausted if we are on a branch");

                match subtrees.get(index) {
                    Some(subtree) => {
                        let (new_subtree, is_new_key) =
                            subtree.insert(entry, depth + 1, degree);
                        let new_subtrees =
                            subtrees.set(index, Arc::new(new_subtree));
                        let new_node = Node::Branch(new_subtrees);

                        (new_node, is_new_key)
                    },

                    None => {
                        let new_subtree = Node::Leaf(Bucket::Single(entry));
                        let new_subtrees =
                            subtrees.set(index, Arc::new(new_subtree));
                        let new_node = Node::Branch(new_subtrees);

                        (new_node, true)
                    },
                }
            },
            Node::Leaf(ref bucket) => {
                // If we are at maximum depth then the hash was totally consumed and we have a
                // collision.
                let maximum_depth =
                    node_utils::index_from_hash(entry.key_hash, depth, degree).is_none();

                match maximum_depth {
                    // We reached a bucket.  If the bucket contains the key we are inserting then
                    // we just need to replace it.
                    false if bucket.contains_key(entry.key(), entry.key_hash) => {
                        let (new_bucket, _) = bucket.insert(entry);
                        let new_node = Node::Leaf(new_bucket);

                        (new_node, false)
                    },

                    // We reached a bucket and the key we will insert is not there.  We need to
                    // create a `Node::Branch` and insert the elements of the bucket there, as well
                    // as the new element.
                    false => {
                        let old_entry: EntryWithHash<K, V> = match *bucket {
                            Bucket::Single(ref e) => EntryWithHash::clone(e),
                            Bucket::Collision(_) =>
                                unreachable!("hash is not exhausted, so there cannot be a collision here"),
                        };

                        let (new_node, _) =
                            Node::new_empty_branch()
                                .insert(old_entry, depth, degree).0
                                .insert(entry, depth, degree);

                        (new_node, true)
                    },

                    // Hash was already totally consumed.  This is a collision.
                    true => {
                        let (new_bucket, is_new_key) = bucket.insert(entry);
                        let new_node = Node::Leaf(new_bucket);

                        (new_node, is_new_key)
                    },
                }
            },
        }
    }

    /// Compresses a node.  This returns the shallowest tree that is well-formed.
    ///
    /// For branches with a single entry this will return a leaf with it.  For branches with no
    /// entries this returns `None.`
    fn compress(self) -> Option<Arc<Node<K, V>>> {
        match self {
            Node::Branch(subtrees) =>
                match subtrees.size() {
                    0 => None,

                    1 => {
                        let compress: bool = {
                            let subtree = subtrees.first().unwrap();

                            // Keep collision at the bottom of the tree.
                            match *subtree.borrow() {
                                Node::Leaf(Bucket::Single(_)) => true,
                                _ => false,
                            }
                        };

                        match compress {
                            true  => subtrees.move_first(),
                            false => Some(Arc::new(Node::Branch(subtrees))),
                        }
                    },

                    _ => Some(Arc::new(Node::Branch(subtrees))),
                },
            Node::Leaf(_) => Some(Arc::new(self)),
        }
    }

    /// Returns a pair with the node without the entry matching `key` and whether the key was present.
    ///
    /// If the node becomes empty it will return `None` in the first component of the pair.
    fn remove<Q: ?Sized>(
        node: &Arc<Node<K, V>>,
        key: &Q,
        key_hash: HashValue,
        depth: usize,
        degree: u8
    ) -> (Option<Arc<Node<K, V>>>, bool)
        where K: Borrow<Q>,
              Q: Hash + Eq {
        match **node {
            Node::Branch(ref subtrees) => {
                let index: usize = node_utils::index_from_hash(key_hash, depth, degree)
                    .expect("hash cannot be exhausted if we are on a branch");

                match subtrees.get(index) {
                    Some(subtree) => {
                        match Node::remove(subtree, key, key_hash, depth + 1, degree) {
                            (_, false) =>
                                (Some(Arc::clone(node)), false),
                            (Some(new_subtree), true) => {
                                let new_subtrees = subtrees.set(index, new_subtree);

                                // Note that we still must call compress because it is possible that
                                // we had a node with just one entry, which was not compressed because
                                // it had a collision.  Maybe now we do not have a collision and we
                                // can compress it.
                                (Node::Branch(new_subtrees).compress(), true)
                            },
                            (None, true) => {
                                let new_subtrees: SparseArrayUsize<Arc<Node<K, V>>> = subtrees.remove(index);

                                (Node::Branch(new_subtrees).compress(), true)
                            },
                        }
                    },

                    None =>
                        (Some(Arc::clone(node)), false),
                }
            },
            Node::Leaf(ref bucket) => {
                match bucket.remove(key, key_hash) {
                    (_, false) => (Some(Arc::clone(node)), false),
                    (Some(new_bucket), true) =>
                        (Some(Arc::new(Node::Leaf(new_bucket))), true),
                    (None, true) =>
                        (None, true),
                }
            },
        }
    }
}

impl<K, V> Clone for Node<K, V>
    where K: Eq + Hash {
    fn clone(&self) -> Node<K, V> {
        match *self {
            Node::Branch(ref subtrees) => Node::Branch(subtrees.clone()),
            Node::Leaf(ref bucket)     => Node::Leaf(bucket.clone()),
        }
    }
}

mod bucket_utils {
    use super::*;

    /// Returns a pair with the bucket with the new entry and whether an element was removed.
    pub fn list_remove_first<T: Clone, F: Fn(&T) -> bool>(list: &List<T>, predicate: F) -> (List<T>, bool) {
        let mut before_needle: Vec<T> = Vec::with_capacity(list.len());
        let mut remaining: List<T> = list.clone();
        let mut removed = false;

        while !remaining.is_empty() {
            let e: T = remaining.first().unwrap().clone();

            remaining = remaining.drop_first().unwrap();

            if predicate(&e) {
                removed = true;
                break;
            }

            before_needle.push(e);
        }

        let mut new_entries = remaining;

        while let Some(e) = before_needle.pop() {
            new_entries = new_entries.push_front(e);
        }

        (new_entries, removed)
    }
}

impl<K, V> Bucket<K, V>
    where K: Eq + Hash {
    fn get<Q: ?Sized>(&self, key: &Q, key_hash: HashValue) -> Option<&EntryWithHash<K, V>>
        where K: Borrow<Q>,
              Q: Hash + Eq {
        match *self {
            Bucket::Single(ref entry) if entry.matches(key, key_hash) => Some(entry.borrow()),
            Bucket::Single(_) => None,
            Bucket::Collision(ref entries) =>
                entries.iter()
                    .find(|e| e.matches(key, key_hash))
                    .map(|e| e.borrow()),
        }
    }

    #[inline]
    fn contains_key<Q: ?Sized>(&self, key: &Q, key_hash: HashValue) -> bool
        where K: Borrow<Q>,
              Q: Hash + Eq {
        self.get(key, key_hash).is_some()
    }

    /// Returns a pair with the bucket with the new entry and whether the key is new.
    ///
    /// If there is a collision then `entry` will be put on the front of the entries list to
    /// improve performance with high temporal locality (since `get()` will try to match according
    /// to the list order).  The order of the rest of the list must be preserved for the same
    /// reason.
    fn insert(&self, entry: EntryWithHash<K, V>) -> (Bucket<K, V>, bool) {
        match *self {
            Bucket::Single(ref existing_entry) if existing_entry.matches(entry.key(), entry.key_hash) =>
                (Bucket::Single(entry), false),
            Bucket::Single(ref existing_entry) => {
                let entries: List<EntryWithHash<K, V>> = List::new()
                    .push_front(EntryWithHash::clone(existing_entry))
                    .push_front(entry);

                (Bucket::Collision(entries), true)
            },
            Bucket::Collision(ref entries) => {
                let (mut new_entries, key_existed) =
                    bucket_utils::list_remove_first(
                        entries,
                        |e| e.matches(entry.key(), entry.key_hash)
                    );

                new_entries = new_entries.push_front(entry);

                (Bucket::Collision(new_entries), !key_existed)
            }
        }
    }

    /// Returns a pair with the bucket without the entry matching `key` and whether the key was present.
    ///
    /// If the bucket becomes empty it will return `None` in the first component of the pair.
    fn remove<Q: ?Sized>(&self, key: &Q, key_hash: HashValue) -> (Option<Bucket<K, V>>, bool)
        where K: Borrow<Q>,
              Q: Hash + Eq {
        match *self {
            Bucket::Single(ref existing_entry) if existing_entry.matches(key, key_hash) =>
                (None, true),
            Bucket::Single(_) =>
                (Some(self.clone()), false),
            Bucket::Collision(ref entries) => {
                let (new_entries, removed) =
                    bucket_utils::list_remove_first(
                        entries,
                        |e|  e.matches(key, key_hash)
                    );

                let new_bucket = match new_entries.len() {
                    0 => unreachable!("impossible to have collision with a single or no entry"),
                    1 => Bucket::Single(EntryWithHash::clone(new_entries.first().unwrap())),
                    _ => Bucket::Collision(new_entries),
                };

                (Some(new_bucket), removed)
            }
        }
    }
}

impl<K, V> Clone for Bucket<K, V>
    where K: Eq + Hash {
    fn clone(&self) -> Bucket<K, V> {
        match *self {
            Bucket::Single(ref entry)      => Bucket::Single(EntryWithHash::clone(entry)),
            Bucket::Collision(ref entries) => Bucket::Collision(List::clone(entries)),
        }
    }
}

impl<K, V> EntryWithHash<K, V>
    where K: Eq + Hash {
    fn new<H: BuildHasher>(key: K, value : V, hash_builder: &H) -> EntryWithHash<K, V> {
        let key_hash = node_utils::hash(&key, hash_builder);

        EntryWithHash {
            entry: Arc::new(Entry::new(key, value)),
            key_hash,
        }
    }

    fn key(&self) -> &K {
        &self.entry.key
    }

    fn value(&self) -> &V {
        &self.entry.value
    }

    #[inline]
    fn matches<Q: ?Sized>(&self, key: &Q, key_hash: HashValue) -> bool
        where K: Borrow<Q>,
              Q: Hash + Eq {
        self.key_hash == key_hash && self.key().borrow() == key
    }
}

impl<K, V> Clone for EntryWithHash<K, V>
    where K: Eq + Hash {
    fn clone(&self) -> EntryWithHash<K, V> {
        EntryWithHash {
            entry: Arc::clone(&self.entry),
            key_hash: self.key_hash
        }
    }
}

impl<K, V> HashTrieMap<K, V, RandomState>
    where K: Eq + Hash {
    pub fn new() -> HashTrieMap<K, V> {
        HashTrieMap::new_with_degree(DEFAULT_DEGREE)
    }

    pub fn new_with_degree(degree: u8) -> HashTrieMap<K, V> {
        HashTrieMap::new_with_hasher_and_degree(RandomState::new(), degree)
    }
}

impl<K, V, H: BuildHasher> HashTrieMap<K, V, H>
    where K: Eq + Hash,
          H: Clone {
    pub fn new_with_hasher(hasher_builder: H) -> HashTrieMap<K, V, H> {
        HashTrieMap::new_with_hasher_and_degree(hasher_builder, DEFAULT_DEGREE)
    }

    pub fn new_with_hasher_and_degree(hasher_builder: H, degree: u8) -> HashTrieMap<K, V, H> {
        assert!(degree.is_power_of_two(), "degree must be a power of two");
        assert!(degree <= DEFAULT_DEGREE, format!("degree must not exceed {}", DEFAULT_DEGREE));

        HashTrieMap {
            root: Arc::new(Node::new_empty_branch()),
            size: 0,
            degree,
            hasher_builder,
        }
    }

    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
        where K: Borrow<Q>,
              Q: Hash + Eq {
        let key_hash = node_utils::hash(key, &self.hasher_builder);

        self.root.get(key, key_hash, 0, self.degree)
            .map(|e| e.value())
    }

    pub fn insert(&self, key: K, value: V) -> HashTrieMap<K, V, H> {
        let entry = EntryWithHash::new(key, value, &self.hasher_builder);
        let (new_root, is_new_key) =
            self.root.insert(entry, 0, self.degree);

        HashTrieMap {
            root: Arc::new(new_root),
            size: self.size + if is_new_key { 1 } else { 0 },
            hasher_builder: self.hasher_builder.clone(),
            degree: self.degree,
        }
    }

    pub fn remove<Q: ?Sized>(&self, key: &Q) -> HashTrieMap<K, V, H>
        where K: Borrow<Q>,
              Q: Hash + Eq {
        let key_hash = node_utils::hash(key, &self.hasher_builder);
        let (new_root, removed) = Node::remove(&self.root, key, key_hash, 0, self.degree);

        HashTrieMap {
            root: new_root.unwrap_or_else(|| Arc::new(Node::new_empty_branch())),
            size: self.size - if removed { 1 } else { 0 },
            hasher_builder: self.hasher_builder.clone(),
            degree: self.degree,
        }
    }

    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool
        where K: Borrow<Q>,
              Q: Hash + Eq {
        self.get(key).is_some()
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.size
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.size() == 0
    }

    pub fn iter(&self) -> Iter<K, V> {
        self.iter_arc().map(|e| (&e.key, &e.value))
    }

    fn iter_arc(&self) -> IterArc<K, V> {
        IterArc::new(self)
    }

    pub fn keys(&self) -> IterKeys<K, V> {
        self.iter().map(|(k, _)| k)
    }

    pub fn values(&self) -> IterValues<K, V> {
        self.iter().map(|(_, v)| v)
    }
}

impl<'a, K, Q: ?Sized, V, H: BuildHasher> Index<&'a Q> for HashTrieMap<K, V, H>
    where K: Eq + Hash + Borrow<Q>,
          Q: Hash + Eq,
          H: Clone {
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key)
            .expect("no entry found for key")
    }
}

impl<K, V, H: BuildHasher> Clone for HashTrieMap<K, V, H>
    where K: Eq + Hash,
          H: Clone {
    fn clone(&self) -> HashTrieMap<K, V, H> {
        HashTrieMap {
            root: Arc::clone(&self.root),
            size: self.size,
            degree: self.degree,
            hasher_builder: self.hasher_builder.clone(),
        }
    }
}

impl<K, V, H: BuildHasher> Default for HashTrieMap<K, V, H>
    where K: Eq + Hash,
          H: Default + Clone {
    fn default() -> HashTrieMap<K, V, H> {
        HashTrieMap::new_with_hasher(H::default())
    }
}

impl<K: Eq, V: PartialEq, H: BuildHasher> PartialEq for HashTrieMap<K, V, H>
    where K: Hash,
          H: Clone {
    fn eq(&self, other: &HashTrieMap<K, V, H>) -> bool {
        self.size() == other.size() && self.iter().all(|(key, value)|
            other.get(key).map_or(false, |v| *value == *v)
        )
    }
}

impl<K: Eq, V: Eq, H: BuildHasher> Eq for HashTrieMap<K, V, H>
    where K: Hash,
          H: Clone {}

impl<K, V, H: BuildHasher> Display for HashTrieMap<K, V, H>
    where K: Eq + Hash + Display,
          V: Display,
          H: Clone {
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        let mut first = true;

        fmt.write_str("{")?;

        for (k, v) in self.iter() {
            if !first {
                fmt.write_str(", ")?;
            }
            k.fmt(fmt)?;
            fmt.write_str(": ")?;
            v.fmt(fmt)?;
            first = false;
        }

        fmt.write_str("}")
    }
}

impl<'a, K, V, H: BuildHasher> IntoIterator for &'a HashTrieMap<K, V, H>
    where K: Eq + Hash,
          H: Default + Clone {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<K, V, H> FromIterator<(K, V)> for HashTrieMap<K, V, H> where
    K: Eq + Hash,
    H: BuildHasher + Clone + Default {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(into_iter: I) -> HashTrieMap<K, V, H> {
        let mut map = HashTrieMap::new_with_hasher(Default::default());

        for (k, v) in into_iter {
            map = map.insert(k, v);
        }

        map
    }
}

#[derive(Debug)]
pub struct IterArc<'a, K: 'a, V: 'a> {
    stack: Vec<IterStackElement<'a, K, V>>,
    size: usize,
}

#[derive(Debug)]
enum IterStackElement<'a, K: 'a, V: 'a> {
    Branch(Peekable<slice::Iter<'a, Arc<Node<K, V>>>>),
    LeafSingle(&'a EntryWithHash<K, V>),
    LeafCollision(Peekable<list::Iter<'a, EntryWithHash<K, V>>>),
}

impl<'a, K, V> IterStackElement<'a, K, V>
    where K: Eq + Hash {

    fn new(node: &Node<K, V>) -> IterStackElement<K, V> {
        match *node {
            Node::Branch(ref children) =>
                IterStackElement::Branch(children.iter().peekable()),
            Node::Leaf(Bucket::Single(ref entry)) =>
                IterStackElement::LeafSingle(entry),
            Node::Leaf(Bucket::Collision(ref entries)) =>
                IterStackElement::LeafCollision(entries.iter().peekable()),
        }
    }

    fn current_elem(&mut self) -> &'a Arc<Entry<K, V>> {
        match *self {
            IterStackElement::Branch(_) =>
                panic!("called current element of a branch"),
            IterStackElement::LeafSingle(entry) => &entry.entry,
            IterStackElement::LeafCollision(ref mut iter) => &iter.peek().unwrap().entry,
        }
    }

    /// Advance and returns `true` if finished.
    #[inline]
    fn advance(&mut self) -> bool {
        match *self {
            IterStackElement::Branch(ref mut iter) => {
                iter.next();
                iter.peek().is_none()
            },
            IterStackElement::LeafSingle(_) => true,
            IterStackElement::LeafCollision(ref mut iter) => {
                iter.next();
                iter.peek().is_none()
            },
        }
    }
}

mod iter_utils {
    use std::mem::size_of;
    use super::HashValue;

    pub fn trie_max_height(degree: u8) -> usize {
        let bits_per_level = (degree - 1).count_ones() as  usize;
        let hash_bits = 8 * size_of::<HashValue>();

        (hash_bits / bits_per_level) + if hash_bits % bits_per_level > 0 { 1 } else { 0 }
    }
}

impl<'a, K, V> IterArc<'a, K, V>
    where K: Eq + Hash {
    fn new<H: BuildHasher + Clone>(map: &HashTrieMap<K, V, H>) -> IterArc<K, V> {
        let mut stack: Vec<IterStackElement<K, V>> =
            Vec::with_capacity(iter_utils::trie_max_height(map.degree) + 1);

        if map.size() > 0 {
            stack.push(IterStackElement::new(map.root.borrow()));
        }

        let mut iter = IterArc {
            stack,
            size: map.size(),
        };

        iter.dig();

        iter
    }

    fn dig(&mut self) -> () {
        let next_stack_elem: Option<IterStackElement<K, V>> =
            self.stack.last_mut().and_then(|stack_top| {
                match *stack_top {
                    IterStackElement::Branch(ref mut iter) =>
                        iter.peek().map(|node| IterStackElement::new(node)),
                    _ => None,
                }
            });

        // TODO use for_each when stable.
        next_stack_elem.map(|e| {
            self.stack.push(e);
            self.dig();
        });
    }

    fn advance(&mut self) -> () {
        match self.stack.pop() {
            Some(mut stack_element) => {
                let finished = stack_element.advance();

                if finished {
                    self.advance();
                } else {
                    self.stack.push(stack_element);

                    self.dig();
                }
            },
            None => (), // Reached the end.  Nothing to do.
        }
    }

    fn current(&mut self) -> Option<&'a Arc<Entry<K, V>>> {
        self.stack.last_mut().map(|e| {
            e.current_elem()
        })
    }
}

impl<'a, K, V> Iterator for IterArc<'a, K, V>
    where K: Eq + Hash {
    type Item = &'a Arc<Entry<K, V>>;

    fn next(&mut self) -> Option<&'a Arc<Entry<K, V>>> {
        let current = self.current();

        self.advance();

        if current.is_some() {
            self.size -= 1;
        }

        current
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.size, Some(self.size))
    }
}

impl<'a, K: Eq + Hash, V> ExactSizeIterator for IterArc<'a, K, V> {}

#[cfg(feature = "serde")]
pub mod serde {
    use super::*;
    use serde::ser::{Serialize, Serializer};
    use serde::de::{Deserialize, Deserializer, MapAccess, Visitor};
    use std::marker::PhantomData;
    use std::fmt;

    impl<K, V, H> Serialize for HashTrieMap<K, V, H>
        where K: Eq + Hash + Serialize,
              V: Serialize,
              H: BuildHasher + Clone + Default {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.collect_map(self)
        }
    }

    impl<'de, K, V, H> Deserialize<'de> for HashTrieMap<K, V, H>
        where K: Eq + Hash + Deserialize<'de>,
              V: Deserialize<'de>,
              H: BuildHasher + Clone + Default {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<HashTrieMap<K, V, H>, D::Error> {
            deserializer.deserialize_map(HashTrieMapVisitor { phantom: PhantomData } )
        }
    }

    struct HashTrieMapVisitor<K, V, H> {
        phantom: PhantomData<(K, V, H)>
    }

    impl<'de, K, V, H> Visitor<'de> for HashTrieMapVisitor<K, V, H>
        where K: Eq + Hash + Deserialize<'de>,
              V: Deserialize<'de>,
              H: BuildHasher + Clone + Default {
        type Value = HashTrieMap<K, V, H>;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("a map")
        }

        fn visit_map<A>(self, mut map: A) -> Result<HashTrieMap<K, V, H>, A::Error>
            where A: MapAccess<'de> {
            let mut hashtriemap = HashTrieMap::new_with_hasher(Default::default());

            while let Some((k, v)) = map.next_entry()? {
                hashtriemap = hashtriemap.insert(k, v);
            }

            Ok(hashtriemap)
        }
    }
}

#[cfg(test)]
mod test;
