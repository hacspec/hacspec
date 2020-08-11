#![cfg_attr(feature = "print_attributes", feature(proc_macro_diagnostic))]
#![cfg_attr(feature = "print_attributes", feature(proc_macro_span))]

extern crate ansi_term;
extern crate quote;
extern crate serde;
extern crate serde_json;
extern crate syn;

#[cfg(feature = "print_attributes")]
use ansi_term::Colour::{Blue, Cyan, Green, Purple, Red, Yellow};
#[cfg(feature = "print_attributes")]
use proc_macro::*;
#[cfg(feature = "print_attributes")]
use quote::quote;
#[cfg(feature = "print_attributes")]
use syn::{parse_macro_input, spanned::Spanned, ItemFn};

use std::collections::{HashMap, HashSet};
use std::fs::OpenOptions;

const ITEM_LIST_LOCATION: &'static str = "./allowed_item_list.json";

macro_rules! declare_attribute {
    ($id:ident, $key: expr, $msg: expr, $doc:tt) => {
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
                let mut file = OpenOptions::new()
                    .read(true)
                    .open(ITEM_LIST_LOCATION)
                    .unwrap();
                let key_s = String::from($key);
                let crate_s = String::from(format!("{}", name));
                let mut item_list : HashMap<String, HashMap<String, HashSet<(String, Option<String>)>>> = serde_json::from_reader(&file).unwrap();
                let item_list_type = match item_list.get_mut(&key_s) {
                    None => {
                      item_list.insert(key_s.clone(), HashMap::new());
                      item_list.get_mut(&key_s).unwrap()
                    }
                    Some(items) => items
                };
                let item_list_type_crate = match item_list_type.get_mut(&crate_s) {
                    None => {
                      item_list_type.insert(crate_s.clone(), HashSet::new());
                      item_list_type.get_mut(&crate_s).unwrap()
                    }
                    Some(items) => items
                };
                item_list_type_crate.insert((format!("{}", func.sig.ident), None));
                let mut file = OpenOptions::new()
                    .truncate(true)
                    .write(true)
                    .open(ITEM_LIST_LOCATION)
                    .unwrap();
                serde_json::to_writer(&file, &item_list);
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
    "primitive",
    Purple.paint("Primitive function"),
    "**Primitive function**, part of the formalization of the language."
);
declare_attribute!(
    to_remove,
    "to_remove",
    Red.paint("Function to be removed"),
    "Function that should be **removed** from the library."
);
declare_attribute!(
    external,
    "external",
    Yellow.paint("External function"),
    "Function that is not part of the language but is offered as a **helper** for tests, etc."
);
declare_attribute!(
    library,
    "library",
    Blue.paint("Library function"),
    "**Library** function that is part of the language but implemented only \
with primitives and other library functions. As such, it does not need to be \
formalized as a primitive."
);
declare_attribute!(
    internal,
    "internal",
    Cyan.paint("Internal function"),
    "**Internal** function used in primitive implementations but that is not part of the language."
);
