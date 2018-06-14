/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use map::red_black_tree_map;
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt::Display;
use std::iter::FromIterator;
use RedBlackTreeMap;

// TODO Use impl trait instead of this when available.
pub type Iter<'a, T> = red_black_tree_map::IterKeys<'a, T, ()>;

/// Creates a [`RedBlackTreeSet`](set/red_black_tree_set/struct.RedBlackTreeSet.html) containing the
/// given arguments:
///
/// ```
/// # use rpds::*;
/// #
/// let s = RedBlackTreeSet::new()
///     .insert(1)
///     .insert(2)
///     .insert(3);
///
/// assert_eq!(rbt_set![1, 2, 3], s);
/// ```
#[macro_export]
macro_rules! rbt_set {
    ($($e:expr),*) => {
        {
            #[allow(unused_mut)]
            let mut s = $crate::RedBlackTreeSet::new();
            $(
                s.insert_mut($e);
            )*
            s
        }
    };
}

/// A persistent set with structural sharing.  This implementation uses a
/// [red-black tree](https://en.wikipedia.org/wiki/Red-Black_tree).
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
/// This is a thin wrapper around a [`RedBlackTreeMap`](../../map/red_black_tree_map/struct.RedBlackTreeMap.html).
#[derive(Debug)]
pub struct RedBlackTreeSet<T>
where
    T: Ord,
{
    map: RedBlackTreeMap<T, ()>,
}

impl<T> RedBlackTreeSet<T>
where
    T: Ord,
{
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

    pub fn insert_mut(&mut self, v: T) {
        self.map.insert_mut(v, ());
    }

    pub fn remove<V: ?Sized>(&self, v: &V) -> RedBlackTreeSet<T>
    where
        T: Borrow<V>,
        V: Ord,
    {
        RedBlackTreeSet {
            map: self.map.remove(v),
        }
    }

    pub fn remove_mut<V: ?Sized>(&mut self, v: &V) -> bool
    where
        T: Borrow<V>,
        V: Ord,
    {
        self.map.remove_mut(v)
    }

    pub fn contains<V: ?Sized>(&self, v: &V) -> bool
    where
        T: Borrow<V>,
        V: Ord,
    {
        self.map.contains_key(v)
    }

    pub fn first(&self) -> Option<&T> {
        self.map.first().map(|(k, _)| k)
    }

    pub fn last(&self) -> Option<&T> {
        self.map.last().map(|(k, _)| k)
    }

    pub fn is_disjoint(&self, other: &RedBlackTreeSet<T>) -> bool {
        let mut self_it = self.iter();
        let mut other_it = other.iter();

        let mut v_opt = self_it.next();
        let mut u_opt = other_it.next();

        while let (Some(v), Some(u)) = (v_opt, u_opt) {
            match v.cmp(u) {
                Ordering::Less => v_opt = self_it.next(),
                Ordering::Equal => return false,
                Ordering::Greater => u_opt = other_it.next(),
            }
        }

        true
    }

    pub fn is_subset(&self, other: &RedBlackTreeSet<T>) -> bool {
        let mut other_it = other.iter();

        for v in self.iter() {
            loop {
                match other_it.next() {
                    Some(u) => match u.cmp(v) {
                        Ordering::Less => (),
                        Ordering::Equal => break,
                        Ordering::Greater => return false,
                    },
                    None => return false,
                }
            }
        }

        true
    }

    pub fn is_superset(&self, other: &RedBlackTreeSet<T>) -> bool {
        other.is_subset(self)
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
where
    T: Ord,
{
    fn clone(&self) -> RedBlackTreeSet<T> {
        RedBlackTreeSet {
            map: self.map.clone(),
        }
    }
}

impl<T> Default for RedBlackTreeSet<T>
where
    T: Ord,
{
    fn default() -> RedBlackTreeSet<T> {
        RedBlackTreeSet::new()
    }
}

impl<T> PartialEq for RedBlackTreeSet<T>
where
    T: Ord,
{
    fn eq(&self, other: &RedBlackTreeSet<T>) -> bool {
        self.map.eq(&other.map)
    }
}

impl<T> Eq for RedBlackTreeSet<T> where T: Ord {}

impl<T> Display for RedBlackTreeSet<T>
where
    T: Ord + Display,
{
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
where
    T: Ord,
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

// TODO This can be improved to create a perfectly balanced tree.
impl<T> FromIterator<T> for RedBlackTreeSet<T>
where
    T: Ord,
{
    fn from_iter<I: IntoIterator<Item = T>>(into_iter: I) -> RedBlackTreeSet<T> {
        let mut set = RedBlackTreeSet::new();

        for v in into_iter {
            set.insert_mut(v);
        }

        set
    }
}

#[cfg(feature = "serde")]
pub mod serde {
    use super::*;
    use serde::de::{Deserialize, Deserializer, SeqAccess, Visitor};
    use serde::ser::{Serialize, Serializer};
    use std::fmt;
    use std::marker::PhantomData;

    impl<T> Serialize for RedBlackTreeSet<T>
    where
        T: Ord + Serialize,
    {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.collect_seq(self)
        }
    }

    impl<'de, T> Deserialize<'de> for RedBlackTreeSet<T>
    where
        T: Ord + Deserialize<'de>,
    {
        fn deserialize<D: Deserializer<'de>>(
            deserializer: D,
        ) -> Result<RedBlackTreeSet<T>, D::Error> {
            deserializer.deserialize_seq(RedBlackTreeSetVisitor {
                phantom: PhantomData,
            })
        }
    }

    struct RedBlackTreeSetVisitor<T> {
        phantom: PhantomData<T>,
    }

    impl<'de, T> Visitor<'de> for RedBlackTreeSetVisitor<T>
    where
        T: Ord + Deserialize<'de>,
    {
        type Value = RedBlackTreeSet<T>;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("a sequence")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<RedBlackTreeSet<T>, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let mut set = RedBlackTreeSet::new();

            while let Some(value) = seq.next_element()? {
                set.insert_mut(value);
            }

            Ok(set)
        }
    }
}

#[cfg(test)]
mod test;
