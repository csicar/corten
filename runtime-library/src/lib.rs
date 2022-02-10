extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;
use syn;

#[proc_macro]
pub fn ty(_item: TokenStream) -> TokenStream {
    println!("{}", _item);
    "()".parse().unwrap()
}
