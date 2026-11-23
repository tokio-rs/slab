#![cfg(feature = "serde")]
#![warn(rust_2018_idioms)]

use serde::{Deserialize, Serialize};
use serde_test::{assert_tokens, Token};
use slab::Slab;

#[derive(Debug, Serialize, Deserialize)]
#[serde(transparent)]
struct SlabPartialEq<T>(Slab<T>);

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

#[test]
fn test_serde_untrusted_len_hint() {
    use serde::de::value::{Error, MapDeserializer};

    // Claims a huge length but yields one pair.
    struct Lying(Option<(usize, u64)>);
    impl Iterator for Lying {
        type Item = (usize, u64);
        fn next(&mut self) -> Option<Self::Item> {
            self.0.take()
        }
        fn size_hint(&self) -> (usize, Option<usize>) {
            (1 << 24, Some(1 << 24))
        }
    }

    let de = MapDeserializer::<_, Error>::new(Lying(Some((0, 7))));
    let slab = Slab::<u64>::deserialize(de).unwrap();
    assert_eq!(slab.len(), 1);
    assert_eq!(slab[0], 7);
    assert!(slab.capacity() < 1 << 24);
}
