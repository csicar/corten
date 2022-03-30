extern crate proc_macro;

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use refinement_language::{self, Parameters, RefinedFunction, Refinement};
use syn::{self, parse_macro_input, punctuated::Punctuated, Token};
use syn_serde::json;

fn refinement_to_refinement_alias(refinement: &Refinement) -> proc_macro2::TokenStream {
    let ty = refinement.ty.clone();
    let refinement_expr = refinement.refinement.clone();
    let refinement_expr = quote! { #refinement_expr }.to_string();
    let binder = refinement.binder.to_string();

    quote! { Refinement<#ty, #binder, #refinement_expr> }
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

    let converted_return_type = refinement_to_refinement_alias(&return_type);

    let raw_args: Punctuated<_, Token![,]> = params
        .into_iter()
        .map(|arg| {
            let name = arg.name;
            let refinement_type = refinement_to_refinement_alias(&arg.refinement);

            quote! { #name : #refinement_type }
        })
        .collect();
    println!("ref: {}", name);

    let return_type_serial = json::to_string_pretty(&return_type.ty);
    let refinement_name = format_ident!("refinement_spec_for_{}", name);

    let expanded = quote! {
        const #refinement_name : &str = #return_type_serial;

        fn #name(#raw_args) -> #converted_return_type #body
    };
    println!("expanded: {}", expanded.to_string());
    TokenStream::from(expanded)
}
