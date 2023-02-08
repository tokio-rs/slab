use slab::Slab;

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
// bincode struct is transparent by design
#[cfg_attr(feature = "bincode", derive(bincode::Encode, bincode::Decode))]
pub struct SlabPartialEq<T>(pub Slab<T>);

impl<T: PartialEq> PartialEq for SlabPartialEq<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0.len() == other.0.len()
            && self
                .0
                .iter()
                .zip(other.0.iter())
                .all(|(this, other)| this.0 == other.0 && this.1 == other.1)
    }
}
