use core::fmt::{Debug, Formatter, Result as FmtResult};

use alloc::vec::Vec;

use crate::key::Key;

/* Entries */

/// Trait that represents any type of collection that can store slab entries.
pub trait Entries<T, TKey>: AsRef<[Entry<T, TKey>]> + AsMut<[Entry<T, TKey>]>
where
    TKey: Key<T>,
{
    /// Get the capacity of the collection.
    fn capacity(&self) -> usize;

    /// Add a new element at the end of the the collection.
    fn push(&mut self, entry: Entry<T, TKey>);

    /// Remove an element from the end of the collection.
    fn pop(&mut self) -> Option<Entry<T, TKey>>;

    /// Remove all elements in the collection.
    fn clear(&mut self);

    /// Shrink the collection to fit all existing items.
    fn shrink_to_fit(&mut self) {}
}

/// Trait that represents any type of collection that can grow in size.
pub trait DynamicEntries<T, TKey>: Entries<T, TKey>
where
    TKey: Key<T>,
{
    /// Create a new collection with the given capacity.
    fn with_capacity(capacity: usize) -> Self;

    /// Reserve additional entries.
    fn reserve(&mut self, additional: usize);

    /// Reserve an exact amount of entries.
    fn reserve_exact(&mut self, additional: usize);
}

impl<T, TKey> Entries<T, TKey> for Vec<Entry<T, TKey>>
where
    TKey: Key<T>,
{
    #[inline]
    fn capacity(&self) -> usize {
        Vec::capacity(self)
    }

    #[inline]
    fn push(&mut self, entry: Entry<T, TKey>) {
        Vec::push(self, entry);
    }

    #[inline]
    fn pop(&mut self) -> Option<Entry<T, TKey>> {
        Vec::pop(self)
    }

    #[inline]
    fn clear(&mut self) {
        Vec::clear(self)
    }

    #[inline]
    fn shrink_to_fit(&mut self) {
        Vec::shrink_to_fit(self);
    }
}

impl<T, TKey> DynamicEntries<T, TKey> for Vec<Entry<T, TKey>>
where
    TKey: Key<T>,
{
    fn with_capacity(capacity: usize) -> Self {
        Vec::with_capacity(capacity)
    }

    fn reserve(&mut self, additional: usize) {
        Vec::reserve(self, additional);
    }

    fn reserve_exact(&mut self, additional: usize) {
        Vec::reserve_exact(self, additional);
    }
}

/* Entry */

/// Represents the entry that is used internally to store the items
pub enum Entry<T, TKey>
where
    TKey: Key<T>,
{
    /// Represents a vacant entry
    Vacant {
        /// Index of the next vacant entry
        next: usize,

        /// Key related data for this entry
        key_data: TKey::VacantData,
    },

    /// Represents an occupied entry
    Occupied {
        /// Value that is stored in this entry
        value: T,

        /// Key related data for this entry
        key_data: TKey::OccupiedData,
    },

    /// Unknown state for this entry
    Unknown,
}

impl<T, TKey> Clone for Entry<T, TKey>
where
    T: Clone,
    TKey: Key<T>,
    TKey::VacantData: Clone,
    TKey::OccupiedData: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Entry::Unknown => unreachable!(),
            Entry::Vacant { next, key_data } => Self::Vacant {
                next: *next,
                key_data: key_data.clone(),
            },
            Entry::Occupied { value, key_data } => Self::Occupied {
                value: value.clone(),
                key_data: key_data.clone(),
            },
        }
    }
}

impl<T, TKey> Debug for Entry<T, TKey>
where
    T: Debug,
    TKey: Key<T>,
    TKey::VacantData: Debug,
    TKey::OccupiedData: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self::Unknown => write!(f, "Unknown"),
            Self::Vacant { next, key_data } => f
                .debug_struct("Vacant")
                .field("next", next)
                .field("key_data", key_data)
                .finish(),
            Self::Occupied { value, key_data } => f
                .debug_struct("Occupied")
                .field("value", value)
                .field("key_data", key_data)
                .finish(),
        }
    }
}
