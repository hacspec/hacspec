#![cfg_attr(
    any(feature = "print_attributes", feature = "hacspec_unsafe"),
    feature(proc_macro_diagnostic)
)]
#![cfg_attr(
    any(feature = "print_attributes", feature = "hacspec_unsafe"),
    feature(proc_macro_span)
)]

extern crate ansi_term;
extern crate hacspec_util;
extern crate quote;
extern crate serde;
extern crate serde_json;
extern crate syn;

#[cfg(feature = "print_attributes")]
use ansi_term::Colour::{Blue, Green, Purple, Yellow};
#[cfg(feature = "print_attributes")]
use hacspec_util::{syn_sig_to_reduced, Signature};
#[cfg(feature = "hacspec_unsafe")]
use proc_macro::TokenTree::Ident;
#[cfg(any(feature = "print_attributes", feature = "hacspec_unsafe"))]
use proc_macro::*;
#[cfg(feature = "print_attributes")]
use quote::quote;
#[cfg(feature = "print_attributes")]
use std::collections::{HashMap, HashSet};
#[cfg(feature = "print_attributes")]
use std::fs::OpenOptions;
#[cfg(any(feature = "print_attributes", feature = "hacspec_unsafe"))]
use syn::{parse_macro_input, spanned::Spanned, ItemFn};
#[cfg(feature = "print_attributes")]
const ITEM_LIST_LOCATION: &str = "./allowed_item_list.json";

macro_rules! declare_attribute {
    ($id:ident, $key: expr, $msg: expr, $doc:tt, $allowed_item: expr) => {
        #[cfg(feature = "print_attributes")]
        #[doc=$doc]
        #[proc_macro_attribute]
        pub fn $id(attr: TokenStream, item: TokenStream) -> TokenStream {
            let item_copy = proc_macro2::TokenStream::from(item.clone());
            let func = parse_macro_input!(item as ItemFn);
            let mut attr_args_iter = attr.into_iter();
            let _impl_type_name: Option<String> =
                attr_args_iter.next().map(|arg| format!("{}", arg));
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
                    let mut item_list: HashMap<String, HashSet<Signature>> =
                        serde_json::from_reader(&file).unwrap();
                    let item_list_type = match item_list.get_mut(&key_s) {
                        None => {
                            item_list.insert(key_s.clone(), HashSet::new());
                            item_list.get_mut(&key_s).expect("Error 2")
                        }
                        Some(items) => items,
                    };
                    item_list_type.insert(syn_sig_to_reduced(&func.sig));
                }
                Diagnostic::new(
                    Level::Note,
                    format!(
                        "{}: {} {}",
                        $msg,
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
    in_hacspec,
    "in_hacspec",
    Blue.paint("Function in hacspec"),
    "This function is within the hacspec subset of Rust: its signature and body use only hacspec constructs and 
    call functions whose signatures are in hacspec.",
    true
);
declare_attribute!(
    unsafe_hacspec,
    "unsafe_hacspec",
    Purple.paint("Unsafe hacspec function"),
    "This function can be called from hacspec programs but its body features Rust constructs that are not part of hacspec",
    true
);
declare_attribute!(
    not_hacspec,
    "not_hacspec",
    Yellow.paint("Function not in hacspec"),
    "Function that is not part of the language but is offered as a helper for tests, etc.",
    false
);

#[cfg(feature = "hacspec_unsafe")]
#[proc_macro_attribute]
pub fn hacspec_unsafe(attr: TokenStream, item: TokenStream) -> TokenStream {
    let item_copy = item.clone();
    let func = parse_macro_input!(item_copy as ItemFn);
    let outside = match attr.into_iter().next() {
        Some(Ident(arg)) => {
            if arg.to_string() == "outside" {
                true
            } else {
                false
            }
        }
        Some(_) | None => false,
    };
    let msg = if outside {
        format!("function outside of hacspec")
    } else {
        format!("unsafe hacspec function")
    };
    Diagnostic::new(
        Level::Note,
        format!("{}: {} {}", msg, format!("{}", func.sig.ident), {
            let file = func.sig.span().unwrap().source_file().path();
            let start = func.sig.span().start();
            format!(
                "in {}:{}",
                file.to_str().unwrap(),
                format!("{}", start.line)
            )
        }),
    )
    .emit();
    item
}
