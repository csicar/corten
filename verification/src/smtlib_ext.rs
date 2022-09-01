use std::io::Write;

use anyhow::anyhow;
use rsmt2;
use rsmt2::{
    print::{AdtDecl, Sym2Smt},
    SmtRes, Solver,
};

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
    fn add_prelude(&mut self) -> SmtRes<()> {
        self.write_all(b"(declare-datatypes () ((Unit unit)))\n\n")?;
        self.declare_fun("ref", &["String"], "Int")
    }
}
