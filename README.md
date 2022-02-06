# rust-hmac-sha256

A small, self-contained SHA256, HMAC-SHA256, and HKDF-SHA256 implementation in Rust.

Optional features:

* `traits`: enable support for the `Digest` trait from the `digest` crate.
* `opt_size`: enable size optimizations. Based on benchmarks, the `.text`
  section size is reduced by 75%, at the cost of approximately 16% performance.
