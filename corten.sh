#!/bin/sh
export RUSTUP_TOOLCHAIN="nightly-2022-02-17"
export LD_LIBRARY_PATH="$(realpath ~/.rustup/toolchains/nightly-2022-02-17-x86_64-unknown-linux-gnu/lib)"
echo ${@} > /tmp/r
export CORTEN_LOG="trace"
$(dirname "$0")/target/debug/liquid-rust --sysroot /home/csicar/.rustup/toolchains/nightly-2022-02-17-x86_64-unknown-linux-gnu "${@}"
