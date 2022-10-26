struct Mutex<P, T> = ...;

impl Mutex<P, T> {
  fn lock() -> MutexLock<P, T> {
    ...
  }
}

struct MutexLock<P, T> = ...;

impl MutexLock<P, T> {
  fn drop(self : ty!{ v : T | P v }) {
    ...
  }
}