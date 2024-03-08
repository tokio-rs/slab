use core::cmp::Ordering;
use core::fmt::{Debug, Formatter, Result as FmtResult};
use core::marker::PhantomData;
use core::sync::atomic::AtomicUsize;

use crate::key::Key;

/* Handle */

/// Strong typed, safe handle that can be used as key for the [`GenericSlab`](crate::GenericSlab).
///
/// To ensure a [`Handle`] is valid, it uses a `id` that is generated once for each slab instance
/// and a `count` that is updated every time a new values was inserted at a particular index.
/// Using this method it is very unlikely to use old key, or keys from a different slab instance.
pub struct Handle<T> {
    id: usize,
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
    type Context = Context;
    type VacantData = usize;
    type OccupiedData = usize;

    #[inline]
    fn index(&self, cx: &Self::Context) -> usize {
        let _cx = cx;

        self.index
    }

    #[inline]
    fn verify(&self, cx: &Self::Context, data: &Self::OccupiedData) -> bool {
        self.id == cx.id && self.count == *data
    }

    #[inline]
    fn new_vacant(cx: &Self::Context, index: usize, data: Option<&Self::VacantData>) -> Self {
        Self {
            id: cx.id,
            index,
            count: data.map(Clone::clone).unwrap_or_default(),
            marker: PhantomData,
        }
    }

    #[inline]
    fn new_occupied(cx: &Self::Context, index: usize, data: &Self::OccupiedData) -> Self {
        Self {
            id: cx.id,
            index,
            count: *data,
            marker: PhantomData,
        }
    }

    #[inline]
    fn convert_into_vacant(cx: &Self::Context, data: Self::OccupiedData) -> Self::VacantData {
        let _cx = cx;

        data
    }

    #[inline]
    fn convert_into_occupied(cx: &Self::Context, data: Self::VacantData) -> Self::OccupiedData {
        let _cx = cx;

        data
    }

    #[inline]
    fn into_occupied_data(self) -> Self::OccupiedData {
        self.count
    }
}

/* Context */

#[derive(Debug, Clone)]
pub struct Context {
    id: usize,
}

impl Default for Context {
    fn default() -> Self {
        Self {
            id: NEXT_ID.fetch_add(1, core::sync::atomic::Ordering::Relaxed),
        }
    }
}

static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
