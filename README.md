![Pipeline](https://github.com/rustne-kretser/critical-once-cell/actions/workflows/rust.yml/badge.svg)
[![Crates.io](https://img.shields.io/crates/v/critical-once-cell.svg)](https://crates.io/crates/critical-once-cell)
[![API reference](https://docs.rs/critical-once-cell/badge.svg)](https://docs.rs/critical-once-cell/)

# critical-once-cell

Drop-in replacements for [`core::lazy::OnceCell`] and
[`core::lazy::Lazy`], backed by [`critical_section`].

### Examples
#### `CriticalOnceCell`

```rust
use critical_once_cell::CriticalOnceCell;

static CELL: CriticalOnceCell<String> = CriticalOnceCell::new();

fn main() {
    CELL.set("Hello, World!".to_owned()).unwrap();

    assert_eq!(*CELL.get().unwrap(), "Hello, World!");
}
```

#### `CriticalLazy`

```rust
use critical_once_cell::CriticalLazy;

static LAZY: CriticalLazy<String> = CriticalLazy::new(|| "Hello, World!".to_owned());

fn main() {
    assert_eq!(*LAZY, "Hello, World!");
}
```

For more details, see [docs](https://docs.rs/critical-once-cell/).

# Usage

Add this to your Cargo.toml:

```toml
[dependencies]
critical-once-cell = "0.2.0"
```

# License

MPL-2.0
