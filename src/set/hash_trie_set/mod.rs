/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::hash::Hash;
use std::hash::BuildHasher;
use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::fmt::Display;
use std::iter::FromIterator;
use map::hash_trie_map;
use HashTrieMap;

// TODO Use impl trait instead of this when available.
pub type Iter<'a, T> = hash_trie_map::IterKeys<'a, T, ()>;

/// A persistent set with structural sharing.  This implementation uses a
/// [hash array mapped trie](https://en.wikipedia.org/wiki/Hash_array_mapped_trie)
/// and supports fast `insert()`, `remove()`, and `contains()`.
///
/// # Complexity
///
/// Let *n* be the number of elements in the set.
///
/// ## Temporal complexity
///
/// | Operation         | Best case | Average | Worst case  |
/// |:----------------- | ---------:| -------:| -----------:|
/// | `new()`           |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `insert()`        |      Θ(1) |    Θ(1) |        Θ(n) |
/// | `remove()`        |      Θ(1) |    Θ(1) |        Θ(n) |
/// | `contains()`      |      Θ(1) |    Θ(1) |        Θ(n) |
/// | `size()`          |      Θ(1) |    Θ(1) |        Θ(1) |
/// | `clone()`         |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator creation |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator step     |      Θ(1) |    Θ(1) |        Θ(1) |
/// | iterator full     |      Θ(n) |    Θ(n) |        Θ(n) |
///
/// # Implementation details
///
/// This is a thin wrapper around a [HashTrieMap](../../map/hash_trie_map/struct.HashTrieMap.html).
#[derive(Debug)]
pub struct HashTrieSet<T, H: BuildHasher = RandomState>
    where T: Eq + Hash,
          H: Clone {
    map: HashTrieMap<T, (), H>,
}

impl<T> HashTrieSet<T, RandomState>
    where T: Eq + Hash {
    pub fn new() -> HashTrieSet<T> {
        HashTrieSet {
            map: HashTrieMap::new(),
        }
    }

    pub fn new_with_degree(degree: u8) -> HashTrieSet<T> {
        HashTrieSet::new_with_hasher_and_degree(RandomState::new(), degree)
    }
}

impl<T, H: BuildHasher> HashTrieSet<T, H>
    where T: Eq + Hash,
          H: Clone {
    pub fn new_with_hasher(hasher_builder: H) -> HashTrieSet<T, H> {
        HashTrieSet {
            map: HashTrieMap::new_with_hasher(hasher_builder),
        }
    }

    pub fn new_with_hasher_and_degree(hasher_builder: H, degree: u8) -> HashTrieSet<T, H> {
        HashTrieSet {
            map: HashTrieMap::new_with_hasher_and_degree(hasher_builder, degree),
        }
    }

    pub fn insert(&self, v: T) -> HashTrieSet<T, H> {
        HashTrieSet {
            map: self.map.insert(v, ()),
        }
    }

    pub fn remove<V: ?Sized>(&self, v: &V) -> HashTrieSet<T, H>
        where T: Borrow<V>,
              V: Hash + Eq {
        HashTrieSet {
            map: self.map.remove(v),
        }
    }

    pub fn contains<V: ?Sized>(&self, v: &V) -> bool
        where T: Borrow<V>,
              V: Hash + Eq {
        self.map.contains_key(v)
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.map.size()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.size() == 0
    }

    pub fn iter(&self) -> Iter<T> {
        self.map.keys()
    }
}

impl<T, H: BuildHasher> Clone for HashTrieSet<T, H>
    where T: Eq + Hash,
          H: Clone {
    fn clone(&self) -> HashTrieSet<T, H> {
        HashTrieSet {
            map: self.map.clone(),
        }
    }
}

impl<T, H: BuildHasher> Default for HashTrieSet<T, H>
    where T: Eq + Hash,
          H: Default + Clone {
    fn default() -> HashTrieSet<T, H> {
        HashTrieSet::new_with_hasher(H::default())
    }
}

impl<T: Eq, H: BuildHasher> PartialEq for HashTrieSet<T, H>
    where T: Hash,
          H: Clone {
    fn eq(&self, other: &HashTrieSet<T, H>) -> bool {
        self.map.eq(&other.map)
    }
}

impl<T: Eq, H: BuildHasher> Eq for HashTrieSet<T, H>
    where T: Hash,
          H: Clone {}

impl<T, H: BuildHasher> Display for HashTrieSet<T, H>
    where T: Eq + Hash + Display,
          H: Clone {
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        let mut first = true;

        fmt.write_str("{")?;

        for v in self.iter() {
            if !first {
                fmt.write_str(", ")?;
            }
            v.fmt(fmt)?;
            first = false;
        }

        fmt.write_str("}")
    }
}

impl<'a, T, H: BuildHasher> IntoIterator for &'a HashTrieSet<T, H>
    where T: Eq + Hash,
          H: Default + Clone {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<T, H> FromIterator<T> for HashTrieSet<T, H> where
    T: Eq + Hash,
    H: BuildHasher + Clone + Default {
    fn from_iter<I: IntoIterator<Item = T>>(into_iter: I) -> HashTrieSet<T, H> {
        let mut map = HashTrieSet::new_with_hasher(Default::default());

        for v in into_iter {
            map = map.insert(v);
        }

        map
    }
}

#[cfg(feature = "serde")]
mod serde_impl {
    use super::*;
    use serde::ser::{Serialize, Serializer};
    use serde::de::{Deserialize, Deserializer, SeqAccess, Visitor};
    use std::marker::PhantomData;
    use std::fmt;

    impl<T, H> Serialize for HashTrieSet<T, H>
        where T: Eq + Hash + Serialize,
              H: BuildHasher + Clone + Default {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.collect_seq(self)
        }
    }

    impl<'de, T, H> Deserialize<'de> for HashTrieSet<T, H>
        where T: Eq + Hash + Deserialize<'de>,
              H: BuildHasher + Clone + Default {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<HashTrieSet<T, H>, D::Error> {
            deserializer.deserialize_seq(HashTrieSetVisitor { phantom: PhantomData } )
        }
    }

    struct HashTrieSetVisitor<T, H> {
        phantom: PhantomData<(T, H)>
    }

    impl<'de, T, H> Visitor<'de> for HashTrieSetVisitor<T, H>
        where T: Eq + Hash + Deserialize<'de>,
              H: BuildHasher + Clone + Default {
        type Value = HashTrieSet<T, H>;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("a sequence")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<HashTrieSet<T, H>, A::Error>
            where A: SeqAccess<'de> {
            let mut hashtrieset = HashTrieSet::new_with_hasher(Default::default());

            while let Some(value) = seq.next_element()? {
                hashtrieset = hashtrieset.insert(value);
            }

            Ok(hashtrieset)
        }
    }
}

#[cfg(test)]
mod test;
