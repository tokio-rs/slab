# Slab

Pre-allocated storage for a uniform data type.

[![Crates.io](https://img.shields.io/crates/v/slab.svg?maxAge=2592000)](https://crates.io/crates/slab)
[![Build Status](https://travis-ci.org/carllerche/slab.svg?branch=master)](https://travis-ci.org/carllerche/slab)

[Documentation](https://docs.rs/slab)

## Usage

To use `slab`, first add this to your `Cargo.toml`:

```toml
[dependencies]
slab = "0.4"
```

Next, add this to your crate:

```rust
extern crate slab;

use slab::Slab;

let mut slab = Slab::new();

let hello = slab.insert("hello");
let world = slab.insert("world");

assert_eq!(slab[hello], "hello");
assert_eq!(slab[world], "world");

slab[world] = "earth";
assert_eq!(slab[world], "earth");
```

See [documentation](https://docs.rs/slab) for more details.

# License

`slab` is primarily distributed under the terms of both the MIT license and the
Apache License (Version 2.0), with portions covered by various BSD-like
licenses.

See LICENSE-APACHE, and LICENSE-MIT for details.
