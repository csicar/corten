# Corten

A Refinement Type System for Rust.
This is an early research prototype and not ready for use.


## Getting started

Corten uses tiny compile-time library to add the necessary macros. Add this to your project's `Cargo.toml`:

```toml
[dependencies]
runtime-library = {path = "<path to corten>/runtime-library"}
```

Now you can use the refinement type system. 
In Corten, a type `i32` is refined to `ty!{v : i32 | v > 0}`, meaning this type may only contain values `> 2`.
For example `increment` specifies that the argument `a` must be non-negative and promises to return an integer that is greater than the input:

```rust
use runtime_library::*; // import the corten macros (e.g. ty!)

fn increment(
  a : ty!{ v : i32 | v > 0 }
) -> ty!{ r : i32 | r > v } {
  a + 1
}
```

Running `cargo b` confirms that this is correct:
```bash
$ cargo b
...
warning: function is never used: `increment`
 --> src/lib.rs:4:4
  |
4 | fn increment(
  |    ^^^^^^^^^
  |
  = note: `#[warn(dead_code)]` on by default

warning: `tutorial` (lib) generated 1 warning
    Finished dev [unoptimized + debuginfo] target(s) in 0.08s
                                                                     
```

Lets say we accidentally decremented the value instead of incrementing it.
Now, `cargo b` will complain that there is a refinement types conflict:


```bash
$ cat src/lib.rs
use runtime_library::*;
fn increment(
  a : ty!{ v : i32 | v > 0 }
) -> ty!{ r : i32 | r > v } {
  a - 1
}

$ cargo b
...
   Compiling tutorial v0.1.0 (/home/.../examples/tutorial)
...
error: Subtyping judgement failed: ty!{ _0 : i32 | (v - 1) == _0 } is not a sub_ty of ty!{ r : i32 | r > v }
 --> src/lib.rs:6:29
  |
6 |   ) -> ty!{ r : i32 | r > v } {
  |  _____________________________^
7 | |     a - 1
8 | | }
  | |_^
  |
help: Counter-Example: _0 = 0, v = 1
 --> src/lib.rs:6:29
  |
6 |   ) -> ty!{ r : i32 | r > v } {
  |  _____________________________^
7 | |     a - 1
8 | | }
  | |_^

warning: `tutorial` (lib) generated 1 warning
error: could not compile `tutorial` due to previous error; 1 warning emitted
```

Corten tells us that it could not match the type `ty!{ _0 : i32 | (v - 1) == _0 }` to `ty!{ r : i32 | r > v }` meaning `v - 1` is not `> v`. Corten gives an example where this is the case: For the return value `_0 = 0` and the argument `v = 1`, our types can not be satisfied.


Corten can recognize path conditions (like `a > b` in the if-statement below) and act accordingly:


```rust
fn max(
  a : ty!{ av: i32 | true },
  b: ty!{ bv: i32 | true }
) -> ty!{ v: i32 | v >= av && v >= bv } {
  if a > b { 
    a as ty!{ x : i32 | x >= av && x >= bv }
  } else { 
    b
  }
}
```

Corten can also handle mutable references:

```rust
fn inc(
  p : &mut ty!{ a : i32 | true => b | b == a + 1 }
) -> ty!{ v : () } {
    *p = *p + 1; ()
}
```

More examples can be found in the [thesis](https://github.com/csicar/corten/blob/main/docs/master-thesis/thesis.pdf) under `5.1 Features` and `7 Evaluation`.


## Installing


```bash
$ git clone ...
$ cargo b
```

Corten replaces the rust compiler (Corten calls the rust compiler internally), so we need to tell cargo about that:

### In `rustc`

Set Corten as the rust compiler:

```bash
$ export RUSTC="$(pwd)/corten.sh"
```

then `cargo` can be used just like normal:

```bash
$ cargo c
```

### Configure Rust Analyzer

`.vscode/settings.json`

```json
"rust-analyzer.server.extraEnv": {
  "RUSTC": "<path to corten>/corten.sh",
  "RUSTUP_TOOLCHAIN": "nightly-2022-02-17",
},
"rust-analyzer.checkOnSave.command": "check"
```

## Documentation

- [Presentation on Corten](https://github.com/csicar/corten/blob/main/docs/presentation/presentation.pdf)
- [Masterthesis](https://github.com/csicar/corten/blob/main/docs/master-thesis/thesis.pdf) or [published version](https://publikationen.bibliothek.kit.edu/1000152005)

## Tests

```bash
cargo t # run test-cases
```