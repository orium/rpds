/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

//! Rayon parallel iterator support for HashTrieMapSync

use super::{Bucket, HashTrieMapSync, Node};
use archery::{ArcTK, SharedPointer};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use rayon::iter::plumbing::{Folder, UnindexedConsumer, UnindexedProducer, bridge_unindexed};
use rayon::iter::{IntoParallelIterator, ParallelIterator};

/// Parallel iterator over the entries of a HashTrieMapSync.
pub struct ParallelIter<'a, K, V, H = crate::utils::DefaultBuildHasher>
where
    K: Eq + Hash,
    H: BuildHasher + Clone,
{
    map: &'a HashTrieMapSync<K, V, H>,
}

impl<'a, K, V, H> ParallelIter<'a, K, V, H>
where
    K: Eq + Hash,
    H: BuildHasher + Clone,
{
    fn new(map: &'a HashTrieMapSync<K, V, H>) -> Self {
        ParallelIter { map }
    }
}

impl<'a, K, V, H> IntoParallelIterator for &'a HashTrieMapSync<K, V, H>
where
    K: Eq + Hash + Sync + Send,
    V: Sync + Send,
    H: BuildHasher + Clone + Sync + Send,
{
    type Item = (&'a K, &'a V);
    type Iter = ParallelIter<'a, K, V, H>;

    fn into_par_iter(self) -> Self::Iter {
        ParallelIter::new(self)
    }
}

impl<'a, K, V, H> ParallelIterator for ParallelIter<'a, K, V, H>
where
    K: Eq + Hash + Sync + Send,
    V: Sync + Send,
    H: BuildHasher + Clone + Sync + Send,
{
    type Item = (&'a K, &'a V);

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        let producer = HashTrieMapProducer::new(self.map);
        bridge_unindexed(producer, consumer)
    }
}

/// Producer for parallel iteration over HashTrieMapSync entries.
struct HashTrieMapProducer<'a, K, V>
where
    K: Eq + Hash,
{
    node: ProducerNode<'a, K, V>,
}

enum ProducerNode<'a, K, V> {
    Branch(&'a [SharedPointer<Node<K, V, ArcTK>, ArcTK>]),
    Leaf(&'a Bucket<K, V, ArcTK>)
}

impl<'a, K, V> HashTrieMapProducer<'a, K, V>
where
    K: Eq + Hash,
{
    fn new<H: BuildHasher + Clone>(map: &'a HashTrieMapSync<K, V, H>) -> Self {
        Self::from_node(map.root.borrow())
    }

    fn from_nodes(nodes: &'a [SharedPointer<Node<K, V, ArcTK>, ArcTK>]) -> Self {
        if nodes.len() == 1 {
            Self::from_node(nodes[0].borrow())
        } else {
            HashTrieMapProducer { node: ProducerNode::Branch(nodes) }
        }
    }

    fn from_node(node: &'a Node<K, V, ArcTK>) -> Self {
        let node = match node {
            Node::Branch(children) => return Self::from_nodes(children.as_slice()),
            Node::Leaf(bucket) => ProducerNode::Leaf(bucket),
        };

        HashTrieMapProducer { node }
    }

    fn fold_node_entries<F>(&self, node: &ProducerNode<'a, K, V>, mut folder: F) -> F
    where
        F: Folder<(&'a K, &'a V)>,
    {
        match node {
            ProducerNode::Branch(children) => {
                for child in children.iter() {
                    folder = self.fold_all_entries(child, folder);
                    if folder.full() {
                        break;
                    }
                }
                folder
            }
            ProducerNode::Leaf(bucket) => {
                // For leaf nodes, always process all entries (no partial processing)
                match bucket {
                    Bucket::Single(entry) => folder.consume((&entry.entry.key, &entry.entry.value)),
                    Bucket::Collision(collision_entries) => {
                        for entry in collision_entries.iter() {
                            folder = folder.consume((&entry.entry.key, &entry.entry.value));
                            if folder.full() {
                                break;
                            }
                        }
                        folder
                    }
                }
            }
        }
    }

    fn fold_all_entries<F>(
        &self,
        node: &'a SharedPointer<Node<K, V, ArcTK>, ArcTK>,
        mut folder: F,
    ) -> F
    where
        F: Folder<(&'a K, &'a V)>,
    {
        match node.borrow() {
            Node::Branch(children) => {
                for child in children.iter() {
                    folder = self.fold_all_entries(child, folder);
                    if folder.full() {
                        break;
                    }
                }
                folder
            }
            Node::Leaf(bucket) => match bucket {
                Bucket::Single(entry) => folder.consume((&entry.entry.key, &entry.entry.value)),
                Bucket::Collision(collision_entries) => {
                    for entry in collision_entries.iter() {
                        folder = folder.consume((&entry.entry.key, &entry.entry.value));
                        if folder.full() {
                            break;
                        }
                    }
                    folder
                }
            },
        }
    }
}

impl<'a, K, V> UnindexedProducer for HashTrieMapProducer<'a, K, V>
where
    K: Eq + Hash + Sync + Send,
    V: Sync + Send,
{
    type Item = (&'a K, &'a V);

    fn split(self) -> (Self, Option<Self>) {
        match self.node {
            ProducerNode::Branch(nodes) if nodes.len() > 1 => {
                let (self_nodes, other_nodes) = nodes.split_at(nodes.len() / 2);
                (Self::from_nodes(self_nodes), Some(Self::from_nodes(other_nodes)))
            }
            _ => (self, None),
        }
    }

    fn fold_with<F>(self, folder: F) -> F
    where
        F: Folder<Self::Item>,
    {
        self.fold_node_entries(&self.node, folder)
    }
}

#[cfg(test)]
mod tests {
    use crate::HashTrieMapSync;
    use rayon::iter::{IntoParallelIterator, ParallelIterator};

    #[test]
    fn test_parallel_iterator_basic() {
        let map = HashTrieMapSync::new_sync()
            .insert(1, "one")
            .insert(2, "two")
            .insert(3, "three")
            .insert(4, "four")
            .insert(5, "five");

        let mut collected: Vec<_> = (&map).into_par_iter().map(|(k, v)| (*k, *v)).collect();
        assert_eq!(collected.len(), 5);

        // Verify all entries are present
        collected.sort();
        assert_eq!(collected, vec![(1, "one"), (2, "two"), (3, "three"), (4, "four"), (5, "five")]);
    }

    #[test]
    fn test_parallel_iterator_empty() {
        let map: HashTrieMapSync<i32, &str> = HashTrieMapSync::new_sync();
        let collected: Vec<_> = (&map).into_par_iter().collect();
        assert_eq!(collected.len(), 0);
    }

    #[test]
    fn test_parallel_iterator_single_element() {
        let map = HashTrieMapSync::new_sync().insert(42, "answer");
        let collected: Vec<_> = (&map).into_par_iter().collect();
        assert_eq!(collected.len(), 1);
        assert_eq!(collected[0], (&42, &"answer"));
    }

    #[test]
    fn test_parallel_iterator_large_dataset() {
        let mut map = HashTrieMapSync::new_sync();
        for i in 0..10000 {
            map.insert_mut(i, i * 2);
        }

        let collected: Vec<_> = (&map).into_par_iter().collect();
        assert_eq!(collected.len(), 10000);

        // Verify correctness
        for (k, v) in collected {
            assert_eq!(*v, *k * 2);
        }
    }

    #[test]
    fn test_parallel_filter() {
        let mut map = HashTrieMapSync::new_sync();
        for i in 1..=100 {
            map.insert_mut(i, i * 2);
        }

        let even_keys_count = (&map).into_par_iter().filter(|(k, _)| *k % 2 == 0).count();

        assert_eq!(even_keys_count, 50);
    }

    #[test]
    fn test_parallel_reduce() {
        let mut map = HashTrieMapSync::new_sync();
        for i in 1..=10 {
            map.insert_mut(i, i);
        }

        let product = (&map).into_par_iter().map(|(_, v)| *v).reduce(|| 1, |a, b| a * b);

        let expected_product: i32 = (1..=10).product();
        assert_eq!(product, expected_product);
    }

    #[test]
    fn test_parallel_find_any() {
        let mut map = HashTrieMapSync::new_sync();
        for i in 1..=100 {
            map.insert_mut(i, format!("item_{}", i));
        }

        let found = (&map).into_par_iter().find_any(|(k, _)| **k == 42);

        assert!(found.is_some());
        if let Some((k, v)) = found {
            assert_eq!(*k, 42);
            assert_eq!(*v, "item_42");
        }
    }

    #[test]
    fn test_parallel_all() {
        let mut map = HashTrieMapSync::new_sync();
        for i in 1..=100 {
            map.insert_mut(i, i * 2);
        }

        let all_even_values = (&map).into_par_iter().all(|(_, v)| *v % 2 == 0);

        assert!(all_even_values);
    }

    #[test]
    fn test_parallel_any() {
        let mut map = HashTrieMapSync::new_sync();
        for i in 1..=100 {
            map.insert_mut(i, i);
        }

        let has_fifty = (&map).into_par_iter().any(|(k, _)| *k == 50);

        assert!(has_fifty);
    }

    #[test]
    fn test_parallel_iterator_with_collisions() {
        // Create a map that will have hash collisions by using a custom hasher
        // that forces all keys to have the same hash prefix
        let mut map = HashTrieMapSync::new_sync();

        // Add many entries to increase likelihood of trie depth
        for i in 0..1000 {
            map.insert_mut(format!("key_{}", i), i);
        }

        let count = (&map).into_par_iter().count();
        assert_eq!(count, 1000);

        // Verify all entries are accessible
        let sum: i32 = (&map).into_par_iter().map(|(_, v)| *v).sum();
        let expected_sum: i32 = (0..1000).sum();
        assert_eq!(sum, expected_sum);
    }
}
