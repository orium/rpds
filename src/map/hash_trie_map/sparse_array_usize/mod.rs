/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::vec::Vec;
use std::slice;
use std::mem::size_of_val;

/// Sparse array of size `8⋅size_of::<usize>()`.  The space used is proportional to the number of
/// elements set.
#[derive(Debug, PartialEq, Eq)]
pub struct SparseArrayUsize<T: Clone> {
    bitmap: usize,
    array: Vec<T>,
}

mod sparse_array_usize_utils {
    #[inline]
    pub fn map_index(bitmap: usize, virtual_index: usize) -> Option<usize> {
        if bitmap & (1usize << virtual_index) == 0 {
            None
        } else {
            let mask = (1usize << virtual_index) - 1;

            Some((bitmap & mask).count_ones() as usize)
        }
    }
}

impl<T: Clone> SparseArrayUsize<T> {
    pub fn new() -> SparseArrayUsize<T> {
        SparseArrayUsize {
            bitmap: 0,
            array: Vec::new(),
        }
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        debug_assert!(index < 8 * size_of_val(&self.bitmap));

        sparse_array_usize_utils::map_index(self.bitmap, index).map(|i| &self.array[i])
    }

    #[inline]
    pub fn first_index(&self) -> Option<usize> {
        if self.is_empty() {
            None
        } else {
            Some(self.bitmap.trailing_zeros() as usize)
        }
    }

    fn vec_insert_cloned(vec: &Vec<T>, value: T, index: usize) -> Vec<T> {
        let mut cloned_vec = Vec::with_capacity(vec.len() + 1);

        debug_assert!(index <= vec.len());

        cloned_vec.extend_from_slice(&vec[0..index]);
        cloned_vec.push(value);
        cloned_vec.extend_from_slice(&vec[index..vec.len()]);

        cloned_vec
    }

    fn vec_replace_cloned(vec: &Vec<T>, value: T, index: usize) -> Vec<T> {
        let mut cloned_vec = Vec::with_capacity(vec.len());

        debug_assert!(index < vec.len());

        cloned_vec.extend_from_slice(&vec[0..index]);
        cloned_vec.push(value);
        cloned_vec.extend_from_slice(&vec[(index + 1)..vec.len()]);

        cloned_vec
    }

    fn vec_remove_cloned(vec: &Vec<T>, index: usize) -> Vec<T> {
        let mut cloned_vec = Vec::with_capacity(vec.len() - 1);

        debug_assert!(index < vec.len());

        cloned_vec.extend_from_slice(&vec[0..index]);
        cloned_vec.extend_from_slice(&vec[(index + 1)..vec.len()]);

        cloned_vec
    }

    pub fn set(&self, index: usize, value: T) -> SparseArrayUsize<T> {
        debug_assert!(index < 8 * size_of_val(&self.bitmap));

        match sparse_array_usize_utils::map_index(self.bitmap, index) {
            Some(i) =>
                SparseArrayUsize {
                    bitmap: self.bitmap,
                    array: SparseArrayUsize::vec_replace_cloned(&self.array, value, i),
                },
            None => {
                let new_bitmap = self.bitmap | (1 << index);
                let i = sparse_array_usize_utils::map_index(new_bitmap, index).unwrap();

                SparseArrayUsize {
                    bitmap: new_bitmap,
                    array:  SparseArrayUsize::vec_insert_cloned(&self.array, value, i),
                }
            },
        }
    }

    pub fn remove(&self, index: usize) -> SparseArrayUsize<T> {
        match sparse_array_usize_utils::map_index(self.bitmap, index) {
            Some(i) =>
                SparseArrayUsize {
                    bitmap: self.bitmap ^ (1 << index),
                    array: SparseArrayUsize::vec_remove_cloned(&self.array, i),
                },
            None => self.clone(),
        }
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.bitmap.count_ones() as usize
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.bitmap == 0
    }

    pub fn iter(&self) -> slice::Iter<T> {
        self.array.iter()
    }
}

impl<T: Clone> Clone for SparseArrayUsize<T> {
    fn clone(&self) -> SparseArrayUsize<T> {
        SparseArrayUsize {
            bitmap: self.bitmap,
            array: Vec::clone(&self.array),
        }
    }
}

#[cfg(test)]
mod test;
