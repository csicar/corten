use std::fmt::Display;
use std::io::Write;

use anyhow::anyhow;
use rsmt2;
use rsmt2::print::{IdentParser, ModelParser, Sort2Smt};
use rsmt2::{
    print::{AdtDecl, Sym2Smt},
    SmtRes, Solver,
};
use tracing::error;

use crate::refinement_context::TypeTarget;

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

    fn declare_const_esc(&mut self, name: &str, ty: impl Sort2Smt) -> SmtRes<()>;
}

impl<P> SolverExt for Solver<P> {
    fn add_prelude(&mut self) -> SmtRes<()> {
        self.write_all(b"(declare-datatypes () ((Unit unit)))\n\n")?;
        self.declare_fun("ref", &["String"], "Int")
    }

    fn declare_const_esc(&mut self, name: &str, ty: impl Sort2Smt) -> SmtRes<()> {
        self.declare_const(format!("|{name}|"), ty)
    }
}

#[derive(Clone, Copy)]
pub struct Parser;

impl<'a> IdentParser<String, String, &'a str> for Parser {
    // Idents ~~~~~~~^^^^^^  ^^^^^^  ^^^^^^^^~~~~ Input
    //     Types ~~~~~~~~~~~~|
    fn parse_ident(self, input: &'a str) -> SmtRes<String> {
        Ok(input.into())
    }
    fn parse_type(self, input: &'a str) -> SmtRes<String> {
        Ok(input.into())
    }
}

impl<'a> ModelParser<String, String, String, &'a str> for Parser {
    // Idents ~~~~~~~^^^^^^  ^^^^^^  ^^^^^^  ^^^^^^^^~~~~ Input
    //         Types ~~~~~~~~|            |~~~~~ Values
    fn parse_value(
        self,
        input: &'a str,
        ident: &String,
        params: &[(String, String)],
        typ: &String,
    ) -> SmtRes<String> {
        Ok(input.into())
    }
}

pub struct ValueAssignment {
    logic_var: String,
    program_var: Option<TypeTarget<String>>,
    value: String,
}

impl Display for ValueAssignment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let program = if let Some(target) = &self.program_var {
            format!("{:?}", target)
        } else {
            "<dangling>".to_string()
        };
        write!(f, "{} = {}", self.logic_var, self.value)
    }
}

pub fn extract_model_diagnostics(solver: &mut Solver<Parser>) -> Option<String> {
    if let Ok(model) = solver.get_model() {
        let diag: String = model
            .into_iter()
            .map(|line| ValueAssignment {
                logic_var: line.0,
                value: line.3,
                program_var: None,
            })
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        error!(
            "For the assignment, the property could not be shown: \n    {{{}}}",
            diag
        );
        Some(diag)
    } else {
        None
    }
}
