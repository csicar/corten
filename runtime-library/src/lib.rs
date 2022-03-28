extern crate proc_macro;

use std::fmt::Display;

use proc_macro::TokenStream;
use proc_macro2::{Group, TokenTree};
use quote::{quote, ToTokens, format_ident, TokenStreamExt};
use syn::{
    self, parenthesized,
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    Expr, GenericParam, Ident, Macro, Result, Token, TypeParam, Type,
};
use syn_serde::json;


struct Refinement {
    ty: Type,
    refinement: Expr,
}

impl Parse for Refinement {
    /// Parses `{ a: Int | a > 20 }`
    fn parse(input: ParseStream) -> Result<Self> {
        println!("input  {}", input);
        let ty : Type = input.parse()?;
        println!("ty  {}", ty.to_token_stream());

        input.parse::<Token![|]>()?;
        let refinement = input.parse()?;
        Ok(Refinement { ty, refinement })
    }
}

impl ToTokens for Refinement {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let Refinement {ty, refinement} = self;
        let expanded = (quote! {
            (#ty, #refinement)
        });
        let group : TokenTree = Group::new(proc_macro2::Delimiter::Parenthesis, expanded).into();
        tokens.append(group)
    }
}

struct RefinementInMacro(Refinement);

impl Parse for RefinementInMacro {
    /// Parses `ty!{ a: Int | a > 20 }`
    fn parse(input: ParseStream) -> Result<Self> {
        let mac: Macro = input.parse()?;
        let refinement: Refinement = syn::parse2(mac.tokens.to_token_stream())?;
        Ok(RefinementInMacro(refinement))
    }
}

/// ```
///
///
/// ```
struct RefinedParam {
    name: Ident,
    refinement: Refinement,
}

impl Parse for RefinedParam {
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

struct Parameters(Punctuated<RefinedParam, Token![,]>);
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

struct RefinedFunction {
    name: Ident,
    body: Expr,
    parameters: Parameters,
    return_type: Refinement,
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

#[test]
fn test_parse_full() {
    let s = "fn test(a : ty!{i32 | a > 2}, b: ty!{i32 | b > 2}) -> ty!{i32 | true} {}";
    let fun = syn::parse_str::<RefinedFunction>(s).unwrap();
    // dbg!(res.iter().map(|a| a.ty.to_token_stream()).collect::<Vec<_>>());
    // dbg!(res.iter().map(|a| a.refinement.to_token_stream()).collect::<Vec<_>>());
}

#[proc_macro_attribute]
pub fn refined(attr: TokenStream, item: TokenStream) -> TokenStream {
    println!("attr: \"{}\"", attr.to_string());
    println!("item: \"{}\"", item.to_string());

    let RefinedFunction {
        name,
        body,
        parameters: Parameters(params),
        return_type,
    } = parse_macro_input!(item as RefinedFunction);

    let base_return_type = return_type.ty.clone();

    let raw_args: Punctuated<_, Token![,]> =
        params.into_iter().map(|arg| {
            
            let ty = arg.refinement.ty;
            let name = arg.name;

            quote! { #name : #ty }
        }).collect();
    println!("ref: {}", name);

    let return_type_serial = json::to_string_pretty(&return_type.ty);
    let refinement_name = format_ident!("refinement_spec_for_{}", name);
    let expanded = quote! {
        const #refinement_name : &str = #return_type_serial;

        fn #name(#raw_args) -> #base_return_type #body
    };
    println!("expanded: {}", expanded.to_string());
    TokenStream::from(expanded)
}

#[proc_macro]
pub fn refined2(item: TokenStream) -> TokenStream {
    println!("item: \"{}\"", item.to_string());

    let RefinedFunction {
        name,
        body,
        parameters: Parameters(params),
        return_type,
    } = parse_macro_input!(item as RefinedFunction);

    let base_return_type = return_type.ty;


    let raw_args: Punctuated<Type, Token![,]> =
        params.into_iter().map(|arg| arg.refinement.ty).collect();
    println!("ref: {}", name);
    let expanded = quote! {
        fn #name(#raw_args) -> #base_return_type #body
    };
    println!("exp: {}", expanded.to_string());
    TokenStream::from(expanded)
}
