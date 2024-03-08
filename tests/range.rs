#![cfg(feature = "range")]
#![warn(rust_2018_idioms)]

use std::ops::Bound;

use generic_slab::Slab;

#[derive(Eq, PartialEq, Debug)]
struct Data(pub usize);

macro_rules! range_test {
    ($name:ident, $start:expr, $end:expr, $expected:expr) => {
        #[test]
        fn $name() {
            let lookup = test_lookup_large();

            let range: (Bound<usize>, Bound<usize>) = ($start.into(), $end.into());
            let expected: Vec<usize> = $expected;
            let actual = lookup.range(range).map(|(_, d)| d.0).collect::<Vec<_>>();
            assert_eq!(expected, actual);
        }
    };
}

range_test!(
    range_unbound_unbound,
    Bound::Unbounded,
    Bound::Unbounded,
    vec![0, 1, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15]
);

range_test!(
    range_included_unbound,
    Bound::Included(7),
    Bound::Unbounded,
    vec![7, 8, 9, 10, 11, 12, 13, 14, 15]
);

range_test!(
    range_excluded_unbound,
    Bound::Excluded(7),
    Bound::Unbounded,
    vec![8, 9, 10, 11, 12, 13, 14, 15]
);

range_test!(
    range_unbound_included,
    Bound::Unbounded,
    Bound::Included(7),
    vec![0, 1, 3, 4, 7]
);

range_test!(
    range_unbound_excluded,
    Bound::Unbounded,
    Bound::Excluded(7),
    vec![0, 1, 3, 4]
);

range_test!(
    range_included_included,
    Bound::Included(7),
    Bound::Included(10),
    vec![7, 8, 9, 10, 11, 12, 13]
);

range_test!(
    range_excluded_excluded,
    Bound::Excluded(7),
    Bound::Excluded(10),
    vec![8, 9, 10, 11, 12]
);

range_test!(
    range_included_excluded,
    Bound::Included(7),
    Bound::Excluded(10),
    vec![7, 8, 9, 10, 11, 12]
);

range_test!(
    range_excluded_included,
    Bound::Excluded(7),
    Bound::Included(10),
    vec![8, 9, 10, 11, 12, 13]
);

range_test!(
    range_included_excluded_edge_case,
    Bound::Included(7),
    Bound::Excluded(7),
    vec![]
);

range_test!(
    range_included_included_reverse,
    Bound::Included(10),
    Bound::Included(7),
    vec![13, 14, 15, 0, 1, 3, 4, 7]
);

/// Create a large lookup with the following data layout
/// - [ 0] Occupied  data=0  next=1  prev=5     first_occupied
/// - [ 1] Occupied  data=1  next=3  prev=0
/// - [ 2] Occupied  data=10 next=6  prev=5
/// - [ 3] Occupied  data=3  next=4  prev=1
/// - [ 4] Occupied  data=4  next=7  prev=3
/// - [ 5] Occupied  data=9  next=2  prev=8
/// - [ 6] Occupied  data=11 next=9  prev=2
/// - [ 7] Occupied  data=7  next=8  prev=4
/// - [ 8] Occupied  data=8  next=5  prev=7
/// - [ 9] Occupied  data=12 next=10 prev=6
/// - [10] Occupied  data=13 next=11 prev=9
/// - [11] Occupied  data=14 next=12 prev=10
/// - [12] Occupied  data=15 next=0  prev=11    last_occupied
fn test_lookup_large() -> Slab<Data> {
    let mut lookup = Slab::<Data>::new();
    lookup.insert(Data(0));
    lookup.insert(Data(1));
    let handle2 = lookup.insert(Data(2));
    lookup.insert(Data(3));
    lookup.insert(Data(4));
    let handle5 = lookup.insert(Data(5));
    let handle6 = lookup.insert(Data(6));
    lookup.insert(Data(7));
    lookup.insert(Data(8));

    lookup.remove(handle5);
    lookup.remove(handle2);
    lookup.remove(handle6);

    lookup.insert(Data(9));
    lookup.insert(Data(10));
    lookup.insert(Data(11));
    lookup.insert(Data(12));
    lookup.insert(Data(13));
    lookup.insert(Data(14));
    lookup.insert(Data(15));

    lookup
}
