
extern crate proc_macro;

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use refinement_language::{self, RefinedFunction, Parameters};
use syn::{self, parse_macro_input, punctuated::Punctuated, Token};
use syn_serde::json;

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

    let raw_args: Punctuated<_, Token![,]> = params
        .into_iter()
        .map(|arg| {
            let ty = arg.refinement.ty;
            let name = arg.name;
            let refinement_expr = arg.refinement.refinement;
            let refinement_expr = quote! { #refinement_expr }.to_string();
            let binder = arg.refinement.binder.to_string();

            quote! { #name : Refinement<#ty, #binder, #refinement_expr> }
        })
        .collect();
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
