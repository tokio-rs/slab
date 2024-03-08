# Generic Slab

`generic_slab` is a fork of [`slab`](https://github.com/tokio-rs/slab) that provides more control over the key and storage types. Using a generic approach you can for example implement strong typed keys that must fit the data type stored in the slab, or you can use a fixed size array as backing storage for the slab data.

[![Crates.io][crates-badge]][crates-url]
[![Build Status][ci-badge]][ci-url]

[crates-badge]: https://img.shields.io/crates/v/generic_slab
[crates-url]: https://crates.io/crates/generic_slab
[ci-badge]: https://img.shields.io/github/actions/workflow/status/Bergmann89/generic_slab/ci.yml?branch=master
[ci-url]: https://github.com/Bergmann89/generic_slab/actions

[Documentation](https://docs.rs/generic_slab)

## Usage

To use `generic_slab`, first add this to your `Cargo.toml`:

```toml
[dependencies]
generic_slab = "0.1"
```

Next, add this to your crate:

```rust
use generic_slab::Slab;

let mut slab = Slab::new();

let hello = slab.insert("hello");
let world = slab.insert("world");

assert_eq!(slab[hello], "hello");
assert_eq!(slab[world], "world");

slab[world] = "earth";
assert_eq!(slab[world], "earth");
```

See [documentation](https://docs.rs/generic_slab) for more details.

## License

This project is licensed under the [MIT license](LICENSE).

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in `generic_slab` by you, shall be licensed as MIT, without any additional
terms or conditions.
