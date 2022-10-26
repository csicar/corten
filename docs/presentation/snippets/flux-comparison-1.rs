// Flux
//@ ensures *self: i32<n+1>;
fn increment(&strg v : i32<n>) -> ()
//@ requires n > 0
//@ ensures *self: i32<n-1>;
fn decrement(&strg v : i32<n>) -> ()