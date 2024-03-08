use core::borrow::{Borrow, BorrowMut};
use core::iter::FusedIterator;
use core::mem::replace;

use crate::entries::Entry;
use crate::generic::Meta;
use crate::key::Key;

/* GenericIter */

#[derive(Debug)]
pub struct GenericIter<TInner, TMapper>
where
    TInner: Iterator,
    TMapper: Mapper<TInner::Item>,
{
    len: usize,
    inner: TInner,
    mapper: TMapper,
}

impl<TInner, TMapper> GenericIter<TInner, TMapper>
where
    TInner: Iterator,
    TMapper: Mapper<TInner::Item>,
{
    pub(crate) fn new(len: usize, inner: TInner, mapper: TMapper) -> Self {
        Self { len, inner, mapper }
    }
}

impl<TInner, TMapper> Iterator for GenericIter<TInner, TMapper>
where
    TInner: Iterator,
    TMapper: Mapper<TInner::Item>,
{
    type Item = TMapper::Item;

    fn next(&mut self) -> Option<Self::Item> {
        for item in self.inner.by_ref() {
            if let Some(item) = self.mapper.map(item) {
                self.len -= 1;

                return Some(item);
            }
        }

        debug_assert_eq!(self.len, 0);

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<TInner, TMapper> DoubleEndedIterator for GenericIter<TInner, TMapper>
where
    TInner: DoubleEndedIterator,
    TMapper: Mapper<TInner::Item>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        while let Some(item) = self.inner.next_back() {
            if let Some(item) = self.mapper.map(item) {
                self.len -= 1;

                return Some(item);
            }
        }

        debug_assert_eq!(self.len, 0);

        None
    }
}

impl<TInner, TMapper> ExactSizeIterator for GenericIter<TInner, TMapper>
where
    TInner: Iterator,
    TMapper: Mapper<TInner::Item>,
{
    fn len(&self) -> usize {
        self.len
    }
}

impl<TInner, TMapper> FusedIterator for GenericIter<TInner, TMapper>
where
    TInner: FusedIterator,
    TMapper: Mapper<TInner::Item>,
{
}

impl<TInner, TMapper> Drop for GenericIter<TInner, TMapper>
where
    TInner: Iterator,
    TMapper: Mapper<TInner::Item>,
{
    fn drop(&mut self) {
        self.mapper.finish(&mut self.inner);
    }
}

/* Mapper */

pub trait Mapper<T> {
    type Item;

    fn map(&mut self, value: T) -> Option<Self::Item>;

    fn finish<I>(&mut self, iter: &mut I)
    where
        I: Iterator<Item = T>,
    {
        let _iter = iter;
    }
}

/* KeyMapper */

#[derive(Default, Debug)]
pub struct KeyMapper<TMeta> {
    meta: TMeta,
}

impl<TMeta> KeyMapper<TMeta> {
    pub fn new(meta: TMeta) -> Self {
        Self { meta }
    }
}

impl<'a, T, TKey, TMeta> Mapper<(usize, &'a Entry<T, TKey>)> for KeyMapper<TMeta>
where
    TKey: Key<T>,
    TMeta: Borrow<Meta<T, TKey>>,
{
    type Item = TKey;

    #[inline]
    fn map(&mut self, item: (usize, &'a Entry<T, TKey>)) -> Option<Self::Item> {
        let (index, entry) = item;

        match entry {
            Entry::Occupied { key_data, .. } => Some(TKey::new_occupied(
                &self.meta.borrow().key_context,
                index,
                key_data,
            )),
            _ => None,
        }
    }
}

/* ValueMapper */

#[derive(Default, Debug)]
pub struct ValueMapper;

impl<T, TKey> Mapper<Entry<T, TKey>> for ValueMapper
where
    TKey: Key<T>,
{
    type Item = T;

    #[inline]
    fn map(&mut self, item: Entry<T, TKey>) -> Option<Self::Item> {
        match item {
            Entry::Occupied { value, .. } => Some(value),
            _ => None,
        }
    }
}

impl<'a, T, TKey> Mapper<&'a Entry<T, TKey>> for ValueMapper
where
    TKey: Key<T>,
{
    type Item = &'a T;

    #[inline]
    fn map(&mut self, item: &'a Entry<T, TKey>) -> Option<Self::Item> {
        match item {
            Entry::Occupied { value, .. } => Some(value),
            _ => None,
        }
    }
}

impl<'a, T, TKey> Mapper<&'a mut Entry<T, TKey>> for ValueMapper
where
    TKey: Key<T>,
{
    type Item = &'a mut T;

    #[inline]
    fn map(&mut self, item: &'a mut Entry<T, TKey>) -> Option<Self::Item> {
        match item {
            Entry::Occupied { value, .. } => Some(value),
            _ => None,
        }
    }
}

/* KeyValueMapper */

#[derive(Default, Debug)]
pub struct KeyValueMapper<TMeta> {
    meta: TMeta,
}

impl<TMeta> KeyValueMapper<TMeta> {
    pub fn new(meta: TMeta) -> Self {
        Self { meta }
    }
}

impl<T, TKey, TMeta> Mapper<(usize, Entry<T, TKey>)> for KeyValueMapper<TMeta>
where
    TKey: Key<T>,
    TMeta: Borrow<Meta<T, TKey>>,
{
    type Item = (TKey, T);

    #[inline]
    fn map(&mut self, item: (usize, Entry<T, TKey>)) -> Option<Self::Item> {
        let (index, entry) = item;

        match entry {
            Entry::Occupied {
                value, key_data, ..
            } => {
                let key = TKey::new_occupied(&self.meta.borrow().key_context, index, &key_data);

                Some((key, value))
            }
            _ => None,
        }
    }
}

impl<'a, T, TKey, TMeta> Mapper<(usize, &'a Entry<T, TKey>)> for KeyValueMapper<TMeta>
where
    TKey: Key<T>,
    TMeta: Borrow<Meta<T, TKey>>,
{
    type Item = (TKey, &'a T);

    #[inline]
    fn map(&mut self, item: (usize, &'a Entry<T, TKey>)) -> Option<Self::Item> {
        let (index, entry) = item;

        match entry {
            Entry::Occupied {
                value, key_data, ..
            } => {
                let key = TKey::new_occupied(&self.meta.borrow().key_context, index, key_data);

                Some((key, value))
            }
            _ => None,
        }
    }
}

impl<'a, T, TKey, TMeta> Mapper<(usize, &'a mut Entry<T, TKey>)> for KeyValueMapper<TMeta>
where
    TKey: Key<T>,
    TMeta: Borrow<Meta<T, TKey>>,
{
    type Item = (TKey, &'a mut T);

    #[inline]
    fn map(&mut self, item: (usize, &'a mut Entry<T, TKey>)) -> Option<Self::Item> {
        let (index, entry) = item;

        match entry {
            Entry::Occupied {
                value, key_data, ..
            } => {
                let key = TKey::new_occupied(&self.meta.borrow().key_context, index, key_data);

                Some((key, value))
            }
            _ => None,
        }
    }
}

/* DrainMapper */

#[derive(Debug)]
pub struct DrainMapper<TMeta> {
    meta: TMeta,
}

impl<TMeta> DrainMapper<TMeta> {
    #[inline]
    pub fn new(meta: TMeta) -> Self {
        Self { meta }
    }
}

impl<'a, T, TKey, TMeta> Mapper<(usize, &'a mut Entry<T, TKey>)> for DrainMapper<TMeta>
where
    T: 'a,
    TKey: Key<T> + 'a,
    TMeta: BorrowMut<Meta<T, TKey>>,
{
    type Item = T;

    #[inline]
    fn map(&mut self, item: (usize, &'a mut Entry<T, TKey>)) -> Option<Self::Item> {
        let (index, entry) = item;

        match replace(entry, Entry::Unknown) {
            Entry::Occupied {
                value, key_data, ..
            } => {
                let meta = self.meta.borrow_mut();
                let key_data = TKey::convert_into_vacant(&meta.key_context, key_data);

                *entry = Entry::Vacant {
                    next: meta.first_vacant,
                    key_data,
                };

                meta.len -= 1;
                meta.first_vacant = index;

                Some(value)
            }
            Entry::Vacant { next, key_data } => {
                *entry = Entry::Vacant { next, key_data };

                None
            }
            Entry::Unknown => unreachable!(),
        }
    }

    #[inline]
    fn finish<I>(&mut self, iter: &mut I)
    where
        I: Iterator<Item = (usize, &'a mut Entry<T, TKey>)>,
    {
        for item in iter.by_ref() {
            self.map(item);
        }
    }
}
