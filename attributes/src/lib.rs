#![cfg_attr(feature="print_attributes", feature(proc_macro_diagnostic))]
#![cfg_attr(feature="print_attributes", feature(proc_macro_span))]

extern crate ansi_term;
extern crate quote;
extern crate syn;

#[cfg(feature="print_attributes")]
use ansi_term::Colour::{Blue, Cyan, Green, Purple, Red, Yellow};
#[cfg(feature="print_attributes")]
use proc_macro::*;
#[cfg(feature="print_attributes")]
use quote::quote;
#[cfg(feature="print_attributes")]
use syn::{parse_macro_input, spanned::Spanned, ItemFn};

macro_rules! declare_attribute {
    ($id:ident, $msg: expr, $doc:tt) => {
        #[cfg(feature="print_attributes")]
        #[doc=$doc]
        #[proc_macro_attribute]
        pub fn $id(attr: TokenStream, item: TokenStream) -> TokenStream {
            let item_copy = proc_macro2::TokenStream::from(item.clone());
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
            let doc_msg = format!("_{}_\n", $doc);
            let output = quote! {
                #[doc=#doc_msg]
                #item_copy
             };
            output.into()
        }
    };
}

declare_attribute!(
    primitive,
    Purple.paint("Primitive function"),
    "**Primitive function**, part of the formalization of the language."
);
declare_attribute!(
    to_remove,
    Red.paint("Function to be removed"),
    "Function that should be **removed** from the library."
);
declare_attribute!(
    external,
    Yellow.paint("External function"),
    "Function that is not part of the language but is offered as a **helper** for tests, etc."
);
declare_attribute!(
    library,
    Blue.paint("Library function"),
    "**Library** function that is part of the language but implemented only \
with primitives and other library functions. As such, it does not need to be \
formalized as a primitive."
);
declare_attribute!(
    internal,
    Cyan.paint("Internal function"),
    "**Internal** function used in primitive implementations but that is not part of the language."
);
