# LiquidRust



## Getting started

```bash
cargo r -- -L crate=./target/debug/ --sysroot /home/csicar/.rustup/toolchains/nightly-2022-02-17-x86_64-unknown-linux-gnu ./verification/examples/macro.rs -o /tmp/macro
```

### Diff Output to Graph

```bash
> wl-paste | str replace -a "<   " "" | dot -T svg | save /tmp/graph.svg; firefox /tmp/graph.svg
```


### Rustc IR dump

```bash
> cargo +nightly rustc --example macro -- -Zunpretty=hir-tree | bat -l rust --plain
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
