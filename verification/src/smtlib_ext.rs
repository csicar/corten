use rsmt2::{SmtRes, Solver};

use anyhow::anyhow;

pub trait SmtResExt<T> {
    fn into_anyhow(self) -> anyhow::Result<T>;
}

impl<T> SmtResExt<T> for SmtRes<T> {
    fn into_anyhow(self) -> anyhow::Result<T> {
        self.map_err(|err| anyhow!(err.to_ml_string()))
    }
}

pub trait SolverExt {
    fn add_prelude(&mut self) -> SmtRes<()>;
}

impl<P> SolverExt for Solver<P> {
    fn add_prelude(&mut self)  -> SmtRes<()>{
        self.declare_fun("ref", &["String"], "Int")?;
        self.declare_fun("anon_loc_ref_by", &["String"], "Int")
    }
}