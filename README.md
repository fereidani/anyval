# anyval

[![crates.io](https://img.shields.io/crates/v/anyval.svg?style=for-the-badge)](https://crates.io/crates/anyval)
[![docs.rs](https://img.shields.io/docsrs/anyval.svg?style=for-the-badge)](https://docs.rs/anyval)
[![license](https://img.shields.io/crates/l/anyval.svg?style=for-the-badge)](https://github.com/fereidani/anyval/blob/main/LICENSE)

A lightweight, dynamically‑typed value container for Rust.

`anyval` provides **Map**, **Array**, and **Value** types that let you store heterogeneous data (numbers, strings, booleans, nested maps/arrays) with a simple, ergonomic API. It’s ideal for configuration handling, scripting, or any situation where you need a flexible data model without pulling in a full‑blown JSON library.

## Features

- **Dynamic typing** – `Value` can hold floats, ints, bools, strings, maps, arrays, or `None`.
- **Zero‑allocation on creation** – containers allocate only when needed.
- **Serde support** – optional `serde` integration for (de)serialization.
- **Convenient macros** – `map!` and `array!` for quick literal construction.
- **Optional JSON helpers** – `to_json` / `from_json` behind the `json` feature.

## Quick start

```bash
# Add anyval with the desired features
cargo add anyval

# Add anyval without the default features (no json & serde)
cargo add anyval --no-default-features
```

```rust
use anyval::{map, array, Value};

fn main() {
    // Build a map with mixed types
    let cfg = map! {
        "host" => "localhost",
        "port" => 8080,
        "debug" => true,
        "paths" => array!["/api", "/static"],
    };

    // Access values
    println!("Host: {}", cfg["host"].as_str());
    println!("Port: {}", cfg["port"].as_int());

    // Serialize to JSON (requires the `json` feature)
    #[cfg(feature = "json")]
    println!("JSON: {}", cfg.to_json().unwrap());
}
```

## Documentation

For full API details, examples, and feature flags, see the crate documentation:

<https://docs.rs/anyval>
