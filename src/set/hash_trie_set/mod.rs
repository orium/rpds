/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use crate::HashTrieMap;
use crate::map::hash_trie_map;
use crate::utils::DefaultBuildHasher;
use archery::{ArcTK, RcK, SharedPointerKind};
use core::borrow::Borrow;
use core::fmt::Display;
use core::hash::BuildHasher;
use core::hash::Hash;
use core::iter::FromIterator;

// TODO Use impl trait instead of this when available.
pub type Iter<'a, T, P> = hash_trie_map::IterKeys<'a, T, (), P>;

/// Creates a [`HashTrieSet`](crate::HashTrieSet) containing the given arguments:
///
/// ```
/// # use rpds::*;
/// #
/// let s = HashTrieSet::new()
///     .insert(1)
///     .insert(2)
///     .insert(3);
///
/// assert_eq!(ht_set![1, 2, 3], s);
/// ```
#[macro_export]
macro_rules! ht_set {
    ($($e:expr),*) => {
        {
            #[allow(unused_mut)]
            let mut s = $crate::HashTrieSet::new();
            $(
                s.insert_mut($e);
            )*
            s
        }
    };
}

/// Creates a [`HashTrieSet`](crate::HashTrieSet) that implements `Sync`, containing the given
/// arguments:
///
/// ```
/// # use rpds::*;
/// #
/// let s = HashTrieSet::new_sync()
///     .insert(1)
///     .insert(2)
///     .insert(3);
///
/// assert_eq!(ht_set_sync![1, 2, 3], s);
/// ```
#[macro_export]
macro_rules! ht_set_sync {
    ($($e:expr),*) => {
        {
            #[allow(unused_mut)]
            let mut s = $crate::HashTrieSet::new_sync();
            $(
                s.insert_mut($e);
            )*
            s
        }
    };
}

/// A persistent set with structural sharing.  This implementation uses a
/// [hash array mapped trie](https://en.wikipedia.org/wiki/Hash_array_mapped_trie).
///
/// # Complexity
///
/// Let *n* be the number of elements in the set.
///
/// ## Temporal complexity
///
/// | Operation         | Average | Worst case  |
/// |:----------------- | -------:| -----------:|
/// | `new()`           |    Θ(1) |        Θ(1) |
/// | `insert()`        |    Θ(1) |        Θ(n) |
/// | `remove()`        |    Θ(1) |        Θ(n) |
/// | `get()`           |    Θ(1) |        Θ(n) |
/// | `contains()`      |    Θ(1) |        Θ(n) |
/// | `size()`          |    Θ(1) |        Θ(1) |
/// | `clone()`         |    Θ(1) |        Θ(1) |
/// | iterator creation |    Θ(1) |        Θ(1) |
/// | iterator step     |    Θ(1) |        Θ(1) |
/// | iterator full     |    Θ(n) |        Θ(n) |
///
/// # Implementation details
///
/// This is a thin wrapper around a [`HashTrieMap`](crate::HashTrieMap).
#[derive(Debug)]
pub struct HashTrieSet<T, P = RcK, H: BuildHasher = DefaultBuildHasher>
where
    T: Eq + Hash,
    H: Clone,
    P: SharedPointerKind,
{
    map: HashTrieMap<T, (), P, H>,
}

pub type HashTrieSetSync<T, H = DefaultBuildHasher> = HashTrieSet<T, ArcTK, H>;

impl<T> HashTrieSet<T, RcK, DefaultBuildHasher>
where
    T: Eq + Hash,
{
    #[must_use]
    pub fn new() -> HashTrieSet<T> {
        HashTrieSet {
            map: HashTrieMap::new_with_hasher_and_ptr_kind(DefaultBuildHasher::default()),
        }
    }

    #[must_use]
    pub fn new_with_degree(degree: u8) -> HashTrieSet<T> {
        HashTrieSet::new_with_hasher_and_degree_and_ptr_kind(DefaultBuildHasher::default(), degree)
    }
}

impl<T> HashTrieSetSync<T>
where
    T: Eq + Hash,
{
    #[must_use]
    pub fn new_sync() -> HashTrieSetSync<T> {
        HashTrieSet {
            map: HashTrieMap::new_with_hasher_and_ptr_kind(DefaultBuildHasher::default()),
        }
    }

    #[must_use]
    pub fn new_with_degree_sync(degree: u8) -> HashTrieSetSync<T> {
        HashTrieSet::new_with_hasher_and_degree_and_ptr_kind(DefaultBuildHasher::default(), degree)
    }
}

impl<T, P, H: BuildHasher> HashTrieSet<T, P, H>
where
    T: Eq + Hash,
    H: Clone,
    P: SharedPointerKind,
{
    #[must_use]
    pub fn new_with_hasher_with_ptr_kind(hasher_builder: H) -> HashTrieSet<T, P, H> {
        HashTrieSet { map: HashTrieMap::new_with_hasher_and_ptr_kind(hasher_builder) }
    }

    #[must_use]
    pub fn new_with_hasher_and_degree_and_ptr_kind(
        hasher_builder: H,
        degree: u8,
    ) -> HashTrieSet<T, P, H> {
        HashTrieSet {
            map: HashTrieMap::new_with_hasher_and_degree_and_ptr_kind(hasher_builder, degree),
        }
    }

    #[must_use]
    pub fn insert(&self, v: T) -> HashTrieSet<T, P, H> {
        HashTrieSet { map: self.map.insert(v, ()) }
    }

    pub fn insert_mut(&mut self, v: T) {
        self.map.insert_mut(v, ());
    }

    #[must_use]
    pub fn remove<V: ?Sized>(&self, v: &V) -> HashTrieSet<T, P, H>
    where
        T: Borrow<V>,
        V: Hash + Eq,
    {
        HashTrieSet { map: self.map.remove(v) }
    }

    pub fn remove_mut<V: ?Sized>(&mut self, v: &V) -> bool
    where
        T: Borrow<V>,
        V: Hash + Eq,
    {
        self.map.remove_mut(v)
    }

    #[must_use]
    pub fn get<V: ?Sized>(&self, v: &V) -> Option<&T>
    where
        T: Borrow<V>,
        V: Hash + Eq,
    {
        self.map.get_key_value(v).map(|(k, ())| k)
    }

    #[must_use]
    pub fn contains<V: ?Sized>(&self, v: &V) -> bool
    where
        T: Borrow<V>,
        V: Hash + Eq,
    {
        self.map.contains_key(v)
    }

    #[must_use]
    pub fn is_disjoint<HO: BuildHasher + Clone>(&self, other: &HashTrieSet<T, P, HO>) -> bool {
        self.iter().all(|v| !other.contains(v))
    }

    /// Test whether the two sets refer to the same content in memory.
    ///
    /// This would return true if you’re comparing a set to itself,
    /// or if you’re comparing a set to a fresh clone of itself.
    fn ptr_eq<PO: SharedPointerKind, HO: BuildHasher + Clone>(
        &self,
        other: &HashTrieSet<T, PO, HO>,
    ) -> bool {
        self.map.ptr_eq(&other.map)
    }

    #[must_use]
    pub fn is_subset<HO: BuildHasher + Clone>(&self, other: &HashTrieSet<T, P, HO>) -> bool {
        if self.ptr_eq(other) {
            return true;
        }

        self.size() <= other.size() && self.iter().all(|v| other.contains(v))
    }

    #[must_use]
    pub fn is_superset<HO: BuildHasher + Clone>(&self, other: &HashTrieSet<T, P, HO>) -> bool {
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

    #[allow(clippy::iter_without_into_iter)]
    pub fn iter(&self) -> Iter<'_, T, P> {
        self.map.keys()
    }
}

impl<T, P, H: BuildHasher> Clone for HashTrieSet<T, P, H>
where
    T: Eq + Hash,
    H: Clone,
    P: SharedPointerKind,
{
    fn clone(&self) -> HashTrieSet<T, P, H> {
        HashTrieSet { map: self.map.clone() }
    }
}

impl<T, P, H: BuildHasher> Default for HashTrieSet<T, P, H>
where
    T: Eq + Hash,
    H: Default + Clone,
    P: SharedPointerKind,
{
    fn default() -> HashTrieSet<T, P, H> {
        HashTrieSet::new_with_hasher_with_ptr_kind(H::default())
    }
}

impl<T: Eq, P, PO, H: BuildHasher> PartialEq<HashTrieSet<T, PO, H>> for HashTrieSet<T, P, H>
where
    T: Hash,
    H: Clone,
    P: SharedPointerKind,
    PO: SharedPointerKind,
{
    fn eq(&self, other: &HashTrieSet<T, PO, H>) -> bool {
        self.map.eq(&other.map)
    }
}

impl<T: Eq, P, H: BuildHasher> Eq for HashTrieSet<T, P, H>
where
    T: Hash,
    H: Clone,
    P: SharedPointerKind,
{
}

impl<T, P, H: BuildHasher> Display for HashTrieSet<T, P, H>
where
    T: Eq + Hash + Display,
    H: Clone,
    P: SharedPointerKind,
{
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
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

impl<'a, T, P, H: BuildHasher> IntoIterator for &'a HashTrieSet<T, P, H>
where
    T: Eq + Hash,
    H: Default + Clone,
    P: SharedPointerKind,
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T, P>;

    fn into_iter(self) -> Iter<'a, T, P> {
        self.iter()
    }
}

impl<T, P, H> FromIterator<T> for HashTrieSet<T, P, H>
where
    T: Eq + Hash,
    H: BuildHasher + Clone + Default,
    P: SharedPointerKind,
{
    fn from_iter<I: IntoIterator<Item = T>>(into_iter: I) -> HashTrieSet<T, P, H> {
        let mut set = HashTrieSet::new_with_hasher_with_ptr_kind(Default::default());

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

    impl<T, P, H> Serialize for HashTrieSet<T, P, H>
    where
        T: Eq + Hash + Serialize,
        H: BuildHasher + Clone + Default,
        P: SharedPointerKind,
    {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.collect_seq(self)
        }
    }

    impl<'de, T, P, H> Deserialize<'de> for HashTrieSet<T, P, H>
    where
        T: Eq + Hash + Deserialize<'de>,
        H: BuildHasher + Clone + Default,
        P: SharedPointerKind,
    {
        fn deserialize<D: Deserializer<'de>>(
            deserializer: D,
        ) -> Result<HashTrieSet<T, P, H>, D::Error> {
            deserializer.deserialize_seq(HashTrieSetVisitor {
                _phantom_t: PhantomData,
                _phantom_h: PhantomData,
                _phantom_p: PhantomData,
            })
        }
    }

    struct HashTrieSetVisitor<T, P, H> {
        _phantom_t: PhantomData<T>,
        _phantom_h: PhantomData<H>,
        _phantom_p: PhantomData<P>,
    }

    impl<'de, T, P, H> Visitor<'de> for HashTrieSetVisitor<T, P, H>
    where
        T: Eq + Hash + Deserialize<'de>,
        H: BuildHasher + Clone + Default,
        P: SharedPointerKind,
    {
        type Value = HashTrieSet<T, P, H>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("a sequence")
        }

        fn visit_seq<A>(self, mut seq: A) -> Result<HashTrieSet<T, P, H>, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let mut set = HashTrieSet::new_with_hasher_with_ptr_kind(Default::default());

            while let Some(value) = seq.next_element()? {
                set.insert_mut(value);
            }

            Ok(set)
        }
    }
}

#[cfg(test)]
mod test;
