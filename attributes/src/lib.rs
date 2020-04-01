#![feature(proc_macro_diagnostic)]
#![feature(proc_macro_span)]

extern crate ansi_term;
extern crate syn;

use ansi_term::Colour::{Green, Purple, Red, Yellow};
use proc_macro::*;
use syn::{parse_macro_input, spanned::Spanned, ItemFn};

macro_rules! declare_attribute {
    ($id:ident, $msg: expr) => {
        #[proc_macro_attribute]
        pub fn $id(attr: TokenStream, item: TokenStream) -> TokenStream {
            let item_copy = item.clone();
            let func = parse_macro_input!(item as ItemFn);
            let name = match attr
                .into_iter()
                .next()
                .unwrap_or_else(|| panic!("Expecting an argument to the attribute"))
            {
                TokenTree::Ident(ident) => ident,
                _ => panic!(),
            };
            if cfg!(feature = "print_attributes") {
                Diagnostic::new(
                    Level::Note,
                    format!(
                        "{} ({}): {} {}",
                        $msg,
                        name,
                        Green.paint(format!("{}", func.sig.ident)),
                        {
                            let file = func.sig.span().unwrap().source_file().path();
                            let start = func.sig.span().start();
                            format!(
                                "in file {}, line {}",
                                Yellow.paint(file.to_str().unwrap()),
                                Yellow.paint(format!("{}", start.line))
                            )
                        }
                    ),
                )
                .emit()
            }
            item_copy
        }
    };
}

declare_attribute!(primitive, Purple.paint("Primitive function"));
declare_attribute!(to_remove, Red.paint("Function to be removed"));
