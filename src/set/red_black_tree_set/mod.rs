/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use crate::RedBlackTreeMap;
use crate::map::red_black_tree_map;
use archery::{ArcTK, RcK, SharedPointerKind};
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt::Display;
use core::hash::{Hash, Hasher};
use core::iter::FromIterator;
use core::ops::RangeBounds;

// TODO Use impl trait instead of this when available.
pub type Iter<'a, T, P> = red_black_tree_map::IterKeys<'a, T, (), P>;
pub type RangeIter<'a, T, RB, Q, P> =
    core::iter::Map<red_black_tree_map::RangeIter<'a, T, (), RB, Q, P>, fn((&'a T, &())) -> &'a T>;

/// Creates a [`RedBlackTreeSet`](crate::RedBlackTreeSet) containing the given arguments:
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

/// Creates a [`RedBlackTreeSet`](crate::RedBlackTreeSet) containing the given arguments:
///
/// ```
/// # use rpds::*;
/// #
/// let s = RedBlackTreeSet::new_sync()
///     .insert(1)
///     .insert(2)
///     .insert(3);
///
/// assert_eq!(rbt_set_sync![1, 2, 3], s);
/// ```
#[macro_export]
macro_rules! rbt_set_sync {
    ($($e:expr),*) => {
        {
            #[allow(unused_mut)]
            let mut s = $crate::RedBlackTreeSet::new_sync();
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
/// | Operation                  | Average   | Worst case  |
/// |:-------------------------- | ---------:| -----------:|
/// | `new()`                    |      Θ(1) |        Θ(1) |
/// | `insert()`                 | Θ(log(n)) |   Θ(log(n)) |
/// | `remove()`                 | Θ(log(n)) |   Θ(log(n)) |
/// | `get()`                    | Θ(log(n)) |   Θ(log(n)) |
/// | `contains()`               | Θ(log(n)) |   Θ(log(n)) |
/// | `size()`                   |      Θ(1) |        Θ(1) |
/// | `clone()`                  |      Θ(1) |        Θ(1) |
/// | iterator creation          | Θ(log(n)) |   Θ(log(n)) |
/// | iterator step              |      Θ(1) |   Θ(log(n)) |
/// | iterator full              |      Θ(n) |        Θ(n) |
///
/// # Implementation details
///
/// This is a thin wrapper around a [`RedBlackTreeMap`](crate::RedBlackTreeMap).
#[derive(Debug)]
pub struct RedBlackTreeSet<T, P = RcK>
where
    T: Ord,
    P: SharedPointerKind,
{
    map: RedBlackTreeMap<T, (), P>,
}

pub type RedBlackTreeSetSync<T> = RedBlackTreeSet<T, ArcTK>;

impl<T> RedBlackTreeSetSync<T>
where
    T: Ord,
{
    #[must_use]
    pub fn new_sync() -> RedBlackTreeSetSync<T> {
        RedBlackTreeSet::new_with_ptr_kind()
    }
}

impl<T> RedBlackTreeSet<T>
where
    T: Ord,
{
    #[must_use]
    pub fn new() -> RedBlackTreeSet<T> {
        RedBlackTreeSet { map: RedBlackTreeMap::new_with_ptr_kind() }
    }
}

impl<T, P> RedBlackTreeSet<T, P>
where
    T: Ord,
    P: SharedPointerKind,
{
    #[must_use]
    pub fn new_with_ptr_kind() -> RedBlackTreeSet<T, P> {
        RedBlackTreeSet { map: RedBlackTreeMap::new_with_ptr_kind() }
    }

    #[must_use]
    pub fn insert(&self, v: T) -> RedBlackTreeSet<T, P> {
        RedBlackTreeSet { map: self.map.insert(v, ()) }
    }

    pub fn insert_mut(&mut self, v: T) {
        self.map.insert_mut(v, ());
    }

    #[must_use]
    pub fn remove<V: ?Sized>(&self, v: &V) -> RedBlackTreeSet<T, P>
    where
        T: Borrow<V>,
        V: Ord,
    {
        RedBlackTreeSet { map: self.map.remove(v) }
    }

    pub fn remove_mut<V: ?Sized>(&mut self, v: &V) -> bool
    where
        T: Borrow<V>,
        V: Ord,
    {
        self.map.remove_mut(v)
    }

    #[must_use]
    pub fn get<V: ?Sized>(&self, v: &V) -> Option<&T>
    where
        T: Borrow<V>,
        V: Ord,
    {
        self.map.get_key_value(v).map(|(k, ())| k)
    }

    #[must_use]
    pub fn contains<V: ?Sized>(&self, v: &V) -> bool
    where
        T: Borrow<V>,
        V: Ord,
    {
        self.map.contains_key(v)
    }

    #[must_use]
    pub fn first(&self) -> Option<&T> {
        self.map.first().map(|(k, ())| k)
    }

    #[must_use]
    pub fn last(&self) -> Option<&T> {
        self.map.last().map(|(k, ())| k)
    }

    #[must_use]
    pub fn is_disjoint<PO>(&self, other: &RedBlackTreeSet<T, PO>) -> bool
    where
        PO: SharedPointerKind,
    {
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

    /// Test whether the two sets refer to the same content in memory.
    ///
    /// This would return true if you’re comparing a set to itself,
    /// or if you’re comparing a set to a fresh clone of itself.
    fn ptr_eq<PO: SharedPointerKind>(&self, other: &RedBlackTreeSet<T, PO>) -> bool {
        self.map.ptr_eq(&other.map)
    }

    #[must_use]
    pub fn is_subset<PO>(&self, other: &RedBlackTreeSet<T, PO>) -> bool
    where
        PO: SharedPointerKind,
    {
        if self.ptr_eq(other) {
            return true;
        }
        if self.size() > other.size() {
            return false;
        }
        let mut other_it = other.iter();

        for v in self {
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

    #[must_use]
    pub fn is_superset<PO>(&self, other: &RedBlackTreeSet<T, PO>) -> bool
    where
        PO: SharedPointerKind,
    {
        other.is_subset(self)
    }

    #[must_use]
    #[inline]
    pub fn size(&self) -> usize {
        self.map.size()
    }

    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.size() == 0
    }

    pub fn iter(&self) -> Iter<'_, T, P> {
        self.map.keys()
    }

    pub fn range<Q, RB>(&self, range: RB) -> RangeIter<'_, T, RB, Q, P>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        RB: RangeBounds<Q>,
    {
        self.map.range(range).map(|(k, ())| k)
    }
}

impl<T, P> Clone for RedBlackTreeSet<T, P>
where
    T: Ord,
    P: SharedPointerKind,
{
    fn clone(&self) -> RedBlackTreeSet<T, P> {
        RedBlackTreeSet { map: self.map.clone() }
    }
}

impl<T, P> Default for RedBlackTreeSet<T, P>
where
    T: Ord,
    P: SharedPointerKind,
{
    fn default() -> RedBlackTreeSet<T, P> {
        RedBlackTreeSet::new_with_ptr_kind()
    }
}

impl<T, P, PO> PartialEq<RedBlackTreeSet<T, PO>> for RedBlackTreeSet<T, P>
where
    T: Ord,
    P: SharedPointerKind,
    PO: SharedPointerKind,
{
    fn eq(&self, other: &RedBlackTreeSet<T, PO>) -> bool {
        self.map.eq(&other.map)
    }
}

impl<T, P> Eq for RedBlackTreeSet<T, P>
where
    T: Ord,
    P: SharedPointerKind,
{
}

impl<T: Ord, P, PO> PartialOrd<RedBlackTreeSet<T, PO>> for RedBlackTreeSet<T, P>
where
    P: SharedPointerKind,
    PO: SharedPointerKind,
{
    fn partial_cmp(&self, other: &RedBlackTreeSet<T, PO>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T: Ord, P> Ord for RedBlackTreeSet<T, P>
where
    P: SharedPointerKind,
{
    fn cmp(&self, other: &RedBlackTreeSet<T, P>) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T: Hash, P: SharedPointerKind> Hash for RedBlackTreeSet<T, P>
where
    T: Ord,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Add the hash of length so that if two collections are added one after the other it
        // doesn't hash to the same thing as a single collection with the same elements in the same
        // order.
        self.size().hash(state);

        for e in self {
            e.hash(state);
        }
    }
}

impl<T, P> Display for RedBlackTreeSet<T, P>
where
    T: Ord + Display,
    P: SharedPointerKind,
{
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut first = true;

        fmt.write_str("{")?;

        for v in self {
            if !first {
                fmt.write_str(", ")?;
            }
            v.fmt(fmt)?;
            first = false;
        }

        fmt.write_str("}")
    }
}

impl<'a, T, P> IntoIterator for &'a RedBlackTreeSet<T, P>
where
    T: Ord,
    P: SharedPointerKind,
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T, P>;

    fn into_iter(self) -> Iter<'a, T, P> {
        self.iter()
    }
}

// TODO This can be improved to create a perfectly balanced tree.
impl<T, P> FromIterator<T> for RedBlackTreeSet<T, P>
where
    T: Ord,
    P: SharedPointerKind,
{
    fn from_iter<I: IntoIterator<Item = T>>(into_iter: I) -> RedBlackTreeSet<T, P> {
        let mut set = RedBlackTreeSet::new_with_ptr_kind();

        for v in into_iter {
            set.insert_mut(v);
        }

        set
    }
}

#[cfg(feature = "serde")]
pub mod serde {
    use super::*;
    use ::serde::de::{Deserialize, Deserializer, SeqAccess, Visitor};
    use ::serde::ser::{Serialize, Serializer};
    use core::fmt;
    use core::marker::PhantomData;

    impl<T, P> Serialize for RedBlackTreeSet<T, P>
    where
        T: Ord + Serialize,
        P: SharedPointerKind,
    {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.collect_seq(self)
        }
    }

    impl<'de, T, P> Deserialize<'de> for RedBlackTreeSet<T, P>
    where
        T: Ord + Deserialize<'de>,
        P: SharedPointerKind,
    {
        fn deserialize<D: Deserializer<'de>>(
            deserializer: D,
        ) -> Result<RedBlackTreeSet<T, P>, D::Error> {
            deserializer.deserialize_seq(RedBlackTreeSetVisitor {
                _phantom_t: PhantomData,
                _phantom_p: PhantomData,
            })
        }
    }

    struct RedBlackTreeSetVisitor<T, P> {
        _phantom_t: PhantomData<T>,
        _phantom_p: PhantomData<P>,
    }

    impl<'de, T, P> Visitor<'de> for RedBlackTreeSetVisitor<T, P>
    where
        T: Ord + Deserialize<'de>,
        P: SharedPointerKind,
    {
        type Value = RedBlackTreeSet<T, P>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("a sequence")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<RedBlackTreeSet<T, P>, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let mut set = RedBlackTreeSet::new_with_ptr_kind();

            while let Some(value) = seq.next_element()? {
                set.insert_mut(value);
            }

            Ok(set)
        }
    }
}

#[cfg(test)]
mod test;
