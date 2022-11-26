# LiquidRust

Refinement Type System for Rust.
This is an early research prototype and not ready for use.


## Getting started

Corten uses tiny compile-time library to add the necessary macros. Add this to your project's `Cargo.toml`:

```toml
[dependencies]
runtime-library = {path = "<path to corten>/runtime-library"}
```

Now you can use the refinement type system. For example:

```rust
fn inc(
  p : &mut ty!{ a : i32 | true => b | b == a + 1 }
) -> ty!{ v : () } {
    *p = *p - 1; ()
}
```

Running `cargo b`, `corten` will recognize that the implementation does not match the type:

Output from `cargo b`:

```bash
$ cargo b
...
error: RContext {
           // formulas
           // types
           src/lib.rs:21:3: 21:4 (#0) p : ty!{ _0 : &mut i32 | _0 == & arg (0usize) }
           <anon decl from argument 0> : ty!{ _2 : i32 | (a - 1) == _2 }
           <dangling> : ty!{ a : &mut i32 | true }
       }
        is not a sub context of RContext {
           // formulas
           // types
           <anon decl from argument 0> : ty!{ b : &mut i32 | b == a + 1 }
       }
       , which is required here
  --> src/lib.rs:20:1
   |
20 | / fn inc(
21 | |   p : &mut ty!{ a : i32 | true => b | b == a + 1 }
22 | | ) -> ty!{ v : () } {
23 | |     *p = *p - 1; ()
24 | | }
   | |_^
   |
help: Counter-Example: _0 = (- 1), _2 = (- 1), a = 0, b = 0, ref = 0
  --> src/lib.rs:20:1
   |
20 | / fn inc(
21 | |   p : &mut ty!{ a : i32 | true => b | b == a + 1 }
22 | | ) -> ty!{ v : () } {
23 | |     *p = *p - 1; ()
24 | | }
   | |_^
```

## Usage

Corten replaces the rust compiler (Corten calls the rust compiler internally)

### In `rustc`

Set corten as the rust compiler:


```bash
$ export RUSTC="$(pwd)/corten.sh"
```

then `cargo` can be used just like normal:

```bash
$ cargo c
```

For an example see `example/clamp`

For more information see [https://github.com/csicar/corten/blob/main/docs/presentation/presentation.pdf](presentation).


### Configure Rust Analyzer

`.vscode/settings.json`

```json
"rust-analyzer.server.extraEnv": {
  "RUSTC": "<path to corten>/corten.sh",
  "RUSTUP_TOOLCHAIN": "nightly-2022-02-17",
},
"rust-analyzer.checkOnSave.command": "check"
```

## Building

```bash
cargo b # build corten
cargo t # also run test-cases
```