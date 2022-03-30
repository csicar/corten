use std::fmt::Display;

use proc_macro2::{Group, TokenTree};
use quote::{format_ident, quote, ToTokens, TokenStreamExt};
use syn::{
    self, parenthesized,
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    Expr, GenericParam, Ident, Macro, Result, Token, Type, TypeParam,
};
use syn_serde::json;

#[derive(Debug)]
pub struct Refinement {
    pub ty: Type,
    pub binder: Ident,
    pub refinement: Expr,
}

impl Parse for Refinement {
    /// Parses `{ a: Int | a > 20 }`
    fn parse(input: ParseStream) -> Result<Self> {
        let binder : Ident = input.parse()?;
        input.parse::<Token![:]>()?;
        println!("input  {}", input);
        let ty: Type = input.parse()?;
        println!("ty  {}", ty.to_token_stream());

        input.parse::<Token![|]>()?;
        let refinement = input.parse()?;
        Ok(Refinement { ty, binder, refinement })
    }
}

pub struct RefinementInMacro(pub Refinement);

impl Parse for RefinementInMacro {
    /// Parses `ty!{ a: Int | a > 20 }`
    fn parse(input: ParseStream) -> Result<Self> {
        let mac: Macro = input.parse()?;
        let refinement: Refinement = syn::parse2(mac.tokens.to_token_stream())?;
        Ok(RefinementInMacro(refinement))
    }
}

#[derive(Debug)]
pub struct RefinedParam {
    pub name: Ident,
    pub refinement: Refinement,
}

impl Parse for RefinedParam {
    /// ```
    /// use refinement_language::*;
    /// let parsed = syn::parse_str::<RefinedParam>("a : ty!{v : i32 | v > 0}").unwrap();
    /// println!("{:#?}", parsed);
    /// ```
    fn parse(input: ParseStream) -> Result<Self> {
        let name = input.parse()?;
        input.parse::<Token![:]>()?;
        println!("refined param macro: {}", input);
        let RefinementInMacro(refinement) = input.parse()?;
        // let mac: Macro = input.parse()?;
        // let refinement: Refinement = syn::parse2(mac.tokens.to_token_stream())?;

        Ok(RefinedParam { name, refinement })
    }
}

#[test]
fn test_parse_refined_param() {
    let s = "a : ty!(&mut i32 | a > 2)";
    let res = syn::parse_str::<RefinedParam>(s).unwrap();
    dbg!(res.refinement.ty.to_token_stream());
    dbg!(res.refinement.refinement.to_token_stream());
}

pub struct Parameters(pub Punctuated<RefinedParam, Token![,]>);

impl Parse for Parameters {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Parameters(input.parse_terminated(RefinedParam::parse)?))
    }
}

#[test]
fn test_parse_refined_multiple() {
    let s = "a : ty!(i32 | a > 2), b: ty!(i32 | b > 2)";

    let Parameters(res) = syn::parse_str::<Parameters>(s).unwrap();
    dbg!(res
        .iter()
        .map(|a| a.refinement.ty.to_token_stream())
        .collect::<Vec<_>>());
    dbg!(res
        .iter()
        .map(|a| a.refinement.refinement.to_token_stream())
        .collect::<Vec<_>>());
}

pub struct RefinedFunction {
    pub name: Ident,
    pub body: Expr,
    pub parameters: Parameters,
    pub return_type: Refinement,
}

// fn max(a : i32<p>, b : i32<p>) -> i32<p> {

// }
impl Parse for RefinedFunction {
    fn parse(input: ParseStream) -> Result<Self> {
        input.parse::<Token![fn]>()?;
        let name = input.parse()?;
        // input.parse::<Token![fn]>()?;
        let content;
        parenthesized!(content in input);
        let params = content.parse_terminated(RefinedParam::parse)?;

        input.parse::<Token![->]>()?;
        let RefinementInMacro(return_type) = input.parse()?;
        // input.parse::<Token![=>]>()?;
        let body = input.parse()?;
        Ok(RefinedFunction {
            name,
            body,
            parameters: Parameters(params),
            return_type,
        })
    }
}
