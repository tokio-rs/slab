use core::cmp::Ordering;
use core::fmt::{Debug, Formatter, Result as FmtResult};
use core::marker::PhantomData;

/// Trait that represents any type that can be used as key for the [`GenericSlab`](crate::generic::GenericSlab).
pub trait Key<T> {
    /// Key related data that is stored in vacant entries.
    type VacantData: Default;

    /// Key related data that is stored in occupied entries.
    type OccupiedData: Default;

    /// Create a new key from an index and the vacant entry key data.
    fn new_vacant(index: usize, data: Option<&Self::VacantData>) -> Self;

    /// Create a new key from an index and the occupied entry key data.
    fn new_occupied(index: usize, data: &Self::OccupiedData) -> Self;

    /// Convert occupied key data into vacant key data.
    ///
    /// This is mainly called when an item was removed from the slab.
    fn convert_into_vacant(data: Self::OccupiedData) -> Self::VacantData;

    /// Convert vacant key data into occupied key data.
    ///
    /// This is mainly called when an item is inserted in an vacant entry.
    fn convert_into_occupied(data: Self::VacantData) -> Self::OccupiedData;

    /// Return the index of the key
    fn index(&self) -> usize;

    /// Verify that the key is valid.
    fn verify(&self, data: &Self::OccupiedData) -> bool;
}

#[derive(Default, Debug, Clone, Copy)]
pub struct NoData;

impl<T> Key<T> for usize {
    type VacantData = NoData;
    type OccupiedData = NoData;

    #[inline]
    fn new_vacant(index: usize, data: Option<&Self::VacantData>) -> Self {
        let _data = data;

        index
    }

    #[inline]
    fn new_occupied(index: usize, data: &Self::OccupiedData) -> Self {
        let _data = data;

        index
    }

    #[inline]
    fn convert_into_vacant(data: Self::OccupiedData) -> Self::VacantData {
        data
    }

    #[inline]
    fn convert_into_occupied(data: Self::VacantData) -> Self::OccupiedData {
        data
    }

    #[inline]
    fn index(&self) -> usize {
        *self
    }

    #[inline]
    fn verify(&self, data: &Self::OccupiedData) -> bool {
        let _data = data;

        true
    }
}

/* Handle */

/// Strong type safe handle that can be used as key for the [`GenericSlab`](crate::GenericSlab).
pub struct Handle<T> {
    index: usize,
    count: usize,
    marker: PhantomData<T>,
}

unsafe impl<T> Send for Handle<T> {}
unsafe impl<T> Sync for Handle<T> {}

impl<T> Eq for Handle<T> {}

impl<T> PartialEq<Self> for Handle<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index && self.count == other.count
    }
}

impl<T> Ord for Handle<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match self.count.cmp(&other.count) {
            Ordering::Equal => (),
            o => return o,
        }

        match self.index.cmp(&other.index) {
            Ordering::Equal => (),
            o => return o,
        }

        Ordering::Equal
    }
}

impl<T> PartialOrd<Self> for Handle<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Copy for Handle<T> {}

impl<T> Clone for Handle<T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Debug for Handle<T> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        f.debug_struct("Handle")
            .field("count", &self.count)
            .field("index", &self.index)
            .finish()
    }
}

impl<T> Key<T> for Handle<T> {
    type VacantData = usize;
    type OccupiedData = usize;

    #[inline]
    fn new_vacant(index: usize, data: Option<&Self::VacantData>) -> Self {
        Self {
            index,
            count: data.copied().unwrap_or_default(),
            marker: PhantomData,
        }
    }

    #[inline]
    fn new_occupied(index: usize, data: &Self::OccupiedData) -> Self {
        Self {
            index,
            count: *data,
            marker: PhantomData,
        }
    }

    #[inline]
    fn convert_into_vacant(data: Self::OccupiedData) -> Self::VacantData {
        data
    }

    #[inline]
    fn convert_into_occupied(data: Self::VacantData) -> Self::OccupiedData {
        data
    }

    #[inline]
    fn index(&self) -> usize {
        self.index
    }

    #[inline]
    fn verify(&self, data: &Self::OccupiedData) -> bool {
        self.count == *data
    }
}
