use core::fmt::{Debug, Formatter, Result as FmtResult};
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::ops::Bound;

use crate::entries::{Entries, Entry};
use crate::generic::GenericSlab;
use crate::key::Key;
use crate::INVALID_INDEX;

#[derive(Debug, Clone)]
pub struct GenericRangeIter<TInner> {
    front: Bound<usize>,
    back: Bound<usize>,
    inner: TInner,
}

impl<TInner> GenericRangeIter<TInner> {
    pub(crate) fn new(front: Bound<usize>, back: Bound<usize>, inner: TInner) -> Self {
        let front = match front {
            Bound::Excluded(index) | Bound::Included(index) if index == INVALID_INDEX => {
                Bound::Unbounded
            }
            front => front,
        };

        let back = match back {
            Bound::Excluded(index) | Bound::Included(index) if index == INVALID_INDEX => {
                Bound::Unbounded
            }
            back => back,
        };

        let (front, back) = match (front, back) {
            (Bound::Unbounded, _) | (_, Bound::Unbounded) => (Bound::Unbounded, Bound::Unbounded),
            (front, back) => (front, back),
        };

        Self { front, back, inner }
    }
}

impl<TInner> Iterator for GenericRangeIter<TInner>
where
    TInner: IterImpl,
{
    type Item = TInner::Item;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (front, skip) = match self.front {
                Bound::Unbounded => return None,
                Bound::Included(front) => (front, false),
                Bound::Excluded(front) => (front, true),
            };

            // This is safe because we do not use `inner` until `item` is dropped
            let (next, item) = self.inner.get_next(front);

            match self.back {
                Bound::Unbounded => return None,
                Bound::Excluded(back) if front == back => {
                    self.front = Bound::Unbounded;
                    self.back = Bound::Unbounded;

                    return None;
                }
                Bound::Included(back) if front == back => {
                    self.front = Bound::Unbounded;
                    self.back = Bound::Unbounded;
                }
                _ => (),
            }

            self.front = Bound::Included(next);

            if !skip {
                return Some(item);
            }
        }
    }
}

impl<TInner> DoubleEndedIterator for GenericRangeIter<TInner>
where
    TInner: IterImpl,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            let (back, skip) = match self.back {
                Bound::Unbounded => return None,
                Bound::Included(back) => (back, false),
                Bound::Excluded(back) => (back, true),
            };

            // This is safe because we do not use `inner` until `item` is dropped
            let (next, item) = self.inner.get_prev(back);

            match self.front {
                Bound::Unbounded => return None,
                Bound::Excluded(front) if front == back => {
                    self.front = Bound::Unbounded;
                    self.back = Bound::Unbounded;

                    return None;
                }
                Bound::Included(front) if front == back => {
                    self.front = Bound::Unbounded;
                    self.back = Bound::Unbounded;
                }
                _ => (),
            }

            self.back = Bound::Included(next);

            if !skip {
                return Some(item);
            }
        }
    }
}

impl<TInner> FusedIterator for GenericRangeIter<TInner> where TInner: IterImpl {}

pub trait IterImpl: Sized {
    type Item;

    /// Try to get the item stored at `index` and the index of the next item.
    ///
    /// # Returns
    /// - `Some((prev, item))` - If the item at `index` is valid.
    /// - `None` - If the item at `index` is not valid.
    fn get_next(&mut self, index: usize) -> (usize, Self::Item);

    /// Try to get the item stored at `index` and the index of the previous item.
    ///
    /// # Returns
    /// - `Some((prev, item))` - If the item at `index` is valid.
    /// - `None` - If the item at `index` is not valid.
    fn get_prev(&mut self, index: usize) -> (usize, Self::Item);
}

/* EntriesRef */

pub struct EntriesRef<'a, T, TKey, TEntries>
where
    TKey: Key<T>,
{
    slab: &'a GenericSlab<T, TKey, TEntries>,
    key: PhantomData<TKey>,
    value: PhantomData<T>,
}

impl<'a, T, TKey, TEntries> EntriesRef<'a, T, TKey, TEntries>
where
    TKey: Key<T>,
{
    pub fn new(slab: &'a GenericSlab<T, TKey, TEntries>) -> Self {
        Self {
            slab,
            key: PhantomData,
            value: PhantomData,
        }
    }
}

impl<'a, T, TKey, TEntries> IterImpl for EntriesRef<'a, T, TKey, TEntries>
where
    TKey: Key<T>,
    TEntries: Entries<T, TKey>,
{
    type Item = (TKey, &'a T);

    fn get_next(&mut self, index: usize) -> (usize, Self::Item) {
        match &self.slab.entries.as_ref()[index] {
            Entry::Occupied {
                value,
                key_data,
                range,
            } => {
                let key = TKey::new_occupied(&self.slab.meta.key_context, index, key_data);

                (range.next, (key, value))
            }
            _ => unimplemented!(),
        }
    }

    fn get_prev(&mut self, index: usize) -> (usize, Self::Item) {
        match &self.slab.entries.as_ref()[index] {
            Entry::Occupied {
                value,
                key_data,
                range,
            } => {
                let key = TKey::new_occupied(&self.slab.meta.key_context, index, key_data);

                (range.prev, (key, value))
            }
            _ => unimplemented!(),
        }
    }
}

impl<'a, T, TKey, TEntries> Debug for EntriesRef<'a, T, TKey, TEntries>
where
    TKey: Key<T>,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "EntriesRef")
    }
}

/* EntriesMutRef */

pub struct EntriesMutRef<'a, T, TKey, TEntries>
where
    TKey: Key<T>,
{
    slab: &'a mut GenericSlab<T, TKey, TEntries>,
    key: PhantomData<TKey>,
    value: PhantomData<T>,
}

impl<'a, T, TKey, TEntries> EntriesMutRef<'a, T, TKey, TEntries>
where
    TKey: Key<T>,
{
    pub fn new(slab: &'a mut GenericSlab<T, TKey, TEntries>) -> Self {
        Self {
            slab,
            key: PhantomData,
            value: PhantomData,
        }
    }
}

impl<'a, T, TKey, TEntries> IterImpl for EntriesMutRef<'a, T, TKey, TEntries>
where
    TKey: Key<T>,
    TEntries: Entries<T, TKey>,
{
    type Item = (TKey, &'a mut T);

    fn get_next(&mut self, index: usize) -> (usize, Self::Item) {
        match &mut self.slab.entries.as_mut()[index] {
            Entry::Occupied {
                value,
                key_data,
                range,
            } => {
                let key = TKey::new_occupied(&self.slab.meta.key_context, index, key_data);
                let value = unsafe { &mut *(value as *mut _) };

                (range.next, (key, value))
            }
            _ => unimplemented!(),
        }
    }

    fn get_prev(&mut self, index: usize) -> (usize, Self::Item) {
        match &mut self.slab.entries.as_mut()[index] {
            Entry::Occupied {
                value,
                key_data,
                range,
            } => {
                let key = TKey::new_occupied(&self.slab.meta.key_context, index, key_data);
                let value = unsafe { &mut *(value as *mut _) };

                (range.prev, (key, value))
            }
            _ => unimplemented!(),
        }
    }
}

impl<'a, T, TKey, TEntries> Debug for EntriesMutRef<'a, T, TKey, TEntries>
where
    TKey: Key<T>,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "EntriesMutRef")
    }
}
