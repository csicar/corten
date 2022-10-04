```
let-env PATH = ($env.PATH | append '/home/csicar/.elan/toolchains/leanprover--lean4---nightly/bin')
lake +leanprover/lean4:nightly --verbose build
```