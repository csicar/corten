FROM rustdocker/rust:nightly

RUN  . ~/.cargo/env \
    && rustup default nightly-2022-02-17  \
    && rustup component add rustc-dev llvm-tools-preview \
    && apt-get update \
    && apt-get install -y \
        z3 \
    && rm -rf /var/lib/apt/lists/*
