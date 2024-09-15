#![cfg(feature = "serde")]
#![warn(rust_2018_idioms)]

mod partial_eq;

use partial_eq::SlabPartialEq;
use serde_test::{assert_tokens, Token};
use slab::Slab;

#[test]
fn test_serde_empty() {
    let slab = Slab::<usize>::new();
    assert_tokens(
        &SlabPartialEq(slab),
        &[Token::Map { len: Some(0) }, Token::MapEnd],
    );
}

#[test]
fn test_serde() {
    let vec = vec![(1, 2), (3, 4), (5, 6)];
    let slab: Slab<_> = vec.iter().cloned().collect();
    assert_tokens(
        &SlabPartialEq(slab),
        &[
            Token::Map { len: Some(3) },
            Token::U64(1),
            Token::I32(2),
            Token::U64(3),
            Token::I32(4),
            Token::U64(5),
            Token::I32(6),
            Token::MapEnd,
        ],
    );
}
