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

/// A persistent set with structural sharing.  This implementation uses a hash array mapped trie
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
/// ## Space complexity
///
/// The space complexity is *Θ(n)*.
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

    // TODO Use impl trait for return value when available
    pub fn iter(&self) -> hash_trie_map::IterKeys<T, ()> {
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

#[cfg(test)]
mod test;
