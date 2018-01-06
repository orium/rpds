/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::borrow::Borrow;
use std::fmt::Display;
use std::iter::FromIterator;
use map::red_black_tree_map;
use RedBlackTreeMap;

// TODO Use impl trait instead of this when available.
pub type Iter<'a, T> = red_black_tree_map::IterKeys<'a, T, ()>;

/// A persistent set with structural sharing.  This implementation uses a
/// [red-black tree](https://en.wikipedia.org/wiki/Red-Black_tree)
/// and supports fast `insert()`, `remove()`, and `contains()`.
///
/// # Complexity
///
/// Let *n* be the number of elements in the set.
///
/// ## Temporal complexity
///
/// | Operation                  | Best case | Average   | Worst case  |
/// |:-------------------------- | ---------:| ---------:| -----------:|
/// | `new()`                    |      Θ(1) |      Θ(1) |        Θ(1) |
/// | `insert()`                 |      Θ(1) | Θ(log(n)) |   Θ(log(n)) |
/// | `remove()`                 |      Θ(1) | Θ(log(n)) |   Θ(log(n)) |
/// | `get()`                    |      Θ(1) | Θ(log(n)) |   Θ(log(n)) |
/// | `contains()`               |      Θ(1) | Θ(log(n)) |   Θ(log(n)) |
/// | `size()`                   |      Θ(1) |      Θ(1) |        Θ(1) |
/// | `clone()`                  |      Θ(1) |      Θ(1) |        Θ(1) |
/// | iterator creation          |      Θ(1) |      Θ(1) |        Θ(1) |
/// | iterator step              |      Θ(1) |      Θ(1) |   Θ(log(n)) |
/// | iterator full              |      Θ(n) |      Θ(n) |        Θ(n) |
///
/// # Implementation details
///
/// This is a thin wrapper around a [RedBlackTreeMap](../../map/red_black_tree_map/struct.RedBlackTreeMap.html).
#[derive(Debug)]
pub struct RedBlackTreeSet<T>
    where T: Ord {
    map: RedBlackTreeMap<T, ()>,
}

impl<T> RedBlackTreeSet<T>
    where T: Ord {
    pub fn new() -> RedBlackTreeSet<T> {
        RedBlackTreeSet {
            map: RedBlackTreeMap::new(),
        }
    }

    pub fn insert(&self, v: T) -> RedBlackTreeSet<T> {
        RedBlackTreeSet {
            map: self.map.insert(v, ()),
        }
    }

    pub fn remove<V: ?Sized>(&self, v: &V) -> RedBlackTreeSet<T>
        where T: Borrow<V>,
              V: Ord {
        RedBlackTreeSet {
            map: self.map.remove(v),
        }
    }

    pub fn contains<V: ?Sized>(&self, v: &V) -> bool
        where T: Borrow<V>,
              V: Ord {
        self.map.contains_key(v)
    }

    pub fn first(&self) -> Option<&T> {
        self.map.first().map(|(k, _)| k)
    }

    pub fn last(&self) -> Option<&T> {
        self.map.last().map(|(k, _)| k)
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

impl<T> Clone for RedBlackTreeSet<T>
    where T: Ord {
    fn clone(&self) -> RedBlackTreeSet<T> {
        RedBlackTreeSet {
            map: self.map.clone(),
        }
    }
}

impl<T> Default for RedBlackTreeSet<T>
    where T: Ord {
    fn default() -> RedBlackTreeSet<T> {
        RedBlackTreeSet::new()
    }
}

impl<T> PartialEq for RedBlackTreeSet<T>
    where T: Ord {
    fn eq(&self, other: &RedBlackTreeSet<T>) -> bool {
        self.map.eq(&other.map)
    }
}

impl<T> Eq for RedBlackTreeSet<T>
    where T: Ord {}

impl<T> Display for RedBlackTreeSet<T>
    where T: Ord + Display {
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

impl<'a, T> IntoIterator for &'a RedBlackTreeSet<T>
    where T: Ord {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

// TODO This can be improved to create a perfectly balanced tree.
impl<T> FromIterator<T> for RedBlackTreeSet<T> where
    T: Ord {
    fn from_iter<I: IntoIterator<Item = T>>(into_iter: I) -> RedBlackTreeSet<T> {
        let mut map = RedBlackTreeSet::new();

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

    impl<T> Serialize for RedBlackTreeSet<T>
        where T: Ord + Serialize {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.collect_seq(self)
        }
    }

    impl<'de, T> Deserialize<'de> for RedBlackTreeSet<T>
        where T: Ord + Deserialize<'de> {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<RedBlackTreeSet<T>, D::Error> {
            deserializer.deserialize_seq(RedBlackTreeSetVisitor { phantom: PhantomData } )
        }
    }

    struct RedBlackTreeSetVisitor<T> {
        phantom: PhantomData<T>
    }

    impl<'de, T> Visitor<'de> for RedBlackTreeSetVisitor<T>
        where T: Ord + Deserialize<'de> {
        type Value = RedBlackTreeSet<T>;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("a sequence")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<RedBlackTreeSet<T>, A::Error>
            where A: SeqAccess<'de> {
            let mut rbtreeset = RedBlackTreeSet::new();

            while let Some(value) = seq.next_element()? {
                rbtreeset = rbtreeset.insert(value);
            }

            Ok(rbtreeset)
        }
    }
}

#[cfg(test)]
mod test;
