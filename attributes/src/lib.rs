#![feature(proc_macro_diagnostic)]
#![feature(proc_macro_span)]

extern crate syn;

use proc_macro::*;
use syn::{parse_macro_input, ItemFn, spanned::Spanned};

macro_rules! declare_attribute {
    ($id:ident, $msg: expr) => {
        #[proc_macro_attribute]
        pub fn $id(attr: TokenStream, item: TokenStream) -> TokenStream {
            let item_copy = item.clone();
            let func = parse_macro_input!(item as ItemFn);
            let name = match attr.into_iter().next().unwrap_or_else(|| {
                panic!("Expecting an argument to the attribute")
            }) {
                TokenTree::Ident(ident) => ident,
                _ => panic!(),
            };
            Diagnostic::new(
                Level::Note,
                format!("{} ({}): {} {}", $msg, name, func.sig.ident, {
                    let file = func.sig.span().unwrap().source_file().path();
                    let start = func.sig.span().start();
                    format!("in file {}, line {}", file.to_str().unwrap(), start.line)
                }),
            )
            .emit();
            item_copy
        }
    };
}

declare_attribute!(primitive, "Primitive function");
declare_attribute!(forbidden, "Forbidden function");
