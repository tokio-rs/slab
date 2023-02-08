#![cfg(feature = "bincode")]
#![warn(rust_2018_idioms)]

mod partial_eq;

use bincode::{Decode, Encode};
use partial_eq::SlabPartialEq;
use slab::Slab;
use std::fmt::Debug;

fn assert_bytes<T: Encode + Decode + PartialEq + Debug>(val: &T, bytes: &[u8]) {
    let config = bincode::config::standard();

    let encoded = bincode::encode_to_vec(val, config).unwrap();
    assert_eq!(encoded, bytes);

    let (decoded, decoded_len) = bincode::decode_from_slice::<T, _>(bytes, config).unwrap();
    assert_eq!(decoded_len, bytes.len());
    assert_eq!(&decoded, val);
}

#[test]
fn test_bincode_empty() {
    let slab = Slab::<usize>::new();
    assert_bytes(&SlabPartialEq(slab), &[0]);
}

#[test]
fn test_bincode() {
    let slab = [(1, 2), (3, 4), (5, 6)]
        .iter()
        .copied()
        .collect::<Slab<_>>();
    assert_bytes(&SlabPartialEq(slab), &[3, 1, 4, 3, 8, 5, 12]);
}
