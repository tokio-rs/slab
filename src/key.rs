/// Trait that represents any type that can be used as key for the [`GenericSlab`](crate::generic::GenericSlab).
pub trait Key<T> {
    /// Context to store key related data in.
    /// The context is created once for each slab.
    type Context: Default;

    /// Key related data that is stored in vacant entries.
    type VacantData: Default;

    /// Key related data that is stored in occupied entries.
    type OccupiedData: Default;

    /// Return the index of the key
    fn index(&self, cx: &Self::Context) -> usize;

    /// Verify that the key is valid.
    fn verify(&self, cx: &Self::Context, data: &Self::OccupiedData) -> bool;

    /// Create a new key from an index and the vacant entry key data.
    fn new_vacant(cx: &Self::Context, index: usize, data: Option<&Self::VacantData>) -> Self;

    /// Create a new key from an index and the occupied entry key data.
    fn new_occupied(cx: &Self::Context, index: usize, data: &Self::OccupiedData) -> Self;

    /// Convert occupied key data into vacant key data.
    ///
    /// This is mainly called when an item was removed from the slab.
    fn convert_into_vacant(cx: &Self::Context, data: Self::OccupiedData) -> Self::VacantData;

    /// Convert vacant key data into occupied key data.
    ///
    /// This is mainly called when an item is inserted in an vacant entry.
    fn convert_into_occupied(cx: &Self::Context, data: Self::VacantData) -> Self::OccupiedData;
}

#[derive(Default, Debug, Clone, Copy)]
pub struct NoData;

impl<T> Key<T> for usize {
    type Context = NoData;
    type VacantData = NoData;
    type OccupiedData = NoData;

    #[inline]
    fn index(&self, cx: &Self::Context) -> usize {
        let _cx = cx;

        *self
    }

    #[inline]
    fn verify(&self, cx: &Self::Context, data: &Self::OccupiedData) -> bool {
        let _cx = cx;
        let _data = data;

        true
    }

    #[inline]
    fn new_vacant(cx: &Self::Context, index: usize, data: Option<&Self::VacantData>) -> Self {
        let _cx = cx;
        let _data = data;

        index
    }

    #[inline]
    fn new_occupied(cx: &Self::Context, index: usize, data: &Self::OccupiedData) -> Self {
        let _cx = cx;
        let _data = data;

        index
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
}
