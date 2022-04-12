use rsmt2::SmtRes;

use anyhow::anyhow;

pub trait SmtResExt<T> {
  fn into_anyhow(self: Self) -> anyhow::Result<T>;
}

impl<T> SmtResExt<T> for SmtRes<T> {
    fn into_anyhow(self) -> anyhow::Result<T> {
        self.map_err(|err| anyhow!(err.to_ml_string()))
    }
}