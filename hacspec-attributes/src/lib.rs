#![cfg_attr(feature = "print_attributes", feature(proc_macro_diagnostic))]
#![cfg_attr(feature = "print_attributes", feature(proc_macro_span))]

extern crate ansi_term;
extern crate hacspec_sig;
extern crate quote;
extern crate serde;
extern crate serde_json;
extern crate syn;

#[cfg(feature = "print_attributes")]
use ansi_term::Colour::{Blue, Cyan, Green, Purple, Red, Yellow};
#[cfg(feature = "print_attributes")]
use hacspec_sig::{syn_sig_to_reduced, Signature};
#[cfg(feature = "print_attributes")]
use proc_macro::*;
#[cfg(feature = "print_attributes")]
use quote::quote;
#[cfg(feature = "print_attributes")]
use std::collections::{HashMap, HashSet};
#[cfg(feature = "print_attributes")]
use std::fs::OpenOptions;
#[cfg(feature = "print_attributes")]
use syn::{parse_macro_input, spanned::Spanned, ItemFn};
#[cfg(feature = "print_attributes")]
const ITEM_LIST_LOCATION: &str = "./allowed_item_list.json";

macro_rules! declare_attribute {
    ($id:ident, $key: expr, $msg: expr, $doc:tt, $allowed_item: expr) => {
        #[cfg(feature="print_attributes")]
        #[doc=$doc]
        #[proc_macro_attribute]
        pub fn $id(attr: TokenStream, item: TokenStream) -> TokenStream {
            let item_copy = proc_macro2::TokenStream::from(item.clone());
            let func = parse_macro_input!(item as ItemFn);
            let mut attr_args_iter = attr.into_iter();
            let crate_name = match attr_args_iter
                .next()
                .expect("Expecting an argument to the attribute")
            {
                TokenTree::Ident(ident) => ident,
                _ => panic!(),
            };
            let _impl_type_name: Option<String> = attr_args_iter.next().map(|_| {
                let arg = attr_args_iter.next().expect("Error 6");
                format!("{}", arg)
            });
            let _is_generic: bool = attr_args_iter.next().map_or(false, |_| {
                let _ = attr_args_iter.next().expect("Error 7");
                true
            });
            if cfg!(feature = "print_attributes") {
                if $allowed_item {
                    let file = OpenOptions::new()
                        .read(true)
                        .open(ITEM_LIST_LOCATION)
                        .expect("Error 1");
                    let key_s = String::from($key);
                    let crate_s = String::from(format!("{}", crate_name));
                    let mut item_list : HashMap<String, HashMap<String, HashSet<Signature>>> = serde_json::from_reader(&file).unwrap();
                    let item_list_type = match item_list.get_mut(&key_s) {
                        None => {
                          item_list.insert(key_s.clone(), HashMap::new());
                          item_list.get_mut(&key_s).expect("Error 2")
                        }
                        Some(items) => items
                    };
                    let item_list_type_crate = match item_list_type.get_mut(&crate_s) {
                        None => {
                          item_list_type.insert(crate_s.clone(), HashSet::new());
                          item_list_type.get_mut(&crate_s).expect("Error 3")
                        }
                        Some(items) => items
                    };
                    item_list_type_crate.insert(syn_sig_to_reduced(&func.sig));
                }
                Diagnostic::new(
                    Level::Note,
                    format!(
                        "{} ({}): {} {}",
                        $msg,
                        crate_name,
                        Green.paint(format!("{}", func.sig.ident)),
                        {
                            let file = func.sig.span().unwrap().source_file().path();
                            let start = func.sig.span().start();
                            format!(
                                "in file {}, line {}",
                                Yellow.paint(file.to_str().expect("Error 9")),
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
    "**Primitive function**, part of the formalization of the language.",
    true
);
declare_attribute!(
    to_remove,
    "to_remove",
    Red.paint("Function to be removed"),
    "Function that should be **removed** from the library.",
    false
);
declare_attribute!(
    external,
    "external",
    Yellow.paint("External function"),
    "Function that is not part of the language but is offered as a **helper** for tests, etc.",
    false
);
declare_attribute!(
    library,
    "library",
    Blue.paint("Library function"),
    "**Library** function that is part of the language but implemented only \
with primitives and other library functions. As such, it does not need to be \
formalized as a primitive.",
    true
);
declare_attribute!(
    internal,
    "internal",
    Cyan.paint("Internal function"),
    "**Internal** function used in primitive implementations but that is not part of the language.",
    false
);
