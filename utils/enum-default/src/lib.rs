//! # Default for hacspec enums
//!
//! Sequences in hacspec require an implementation of [`Default`].
//! To use `enums` in sequences it is thus necessary to implement a [`Default`].
//! Since hacspec does not allow implementing traits right now this proc macro
//! can be used to use the first enum value as [`Default`].

extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;

/// Implement [`Default`] for an enum by using the first value.
#[proc_macro_derive(HacspecDefault, attributes(default))]
pub fn enum_default_derive(input: TokenStream) -> TokenStream {
    let ast: syn::DeriveInput = syn::parse(input).unwrap();

    match ast.data {
        syn::Data::Enum(data) => {
            if data.variants.is_empty() {
                return TokenStream::new();
            }

            let variant = data.variants.first().unwrap();
            let first = &variant.ident;
            let ident = &ast.ident;

            let token_stream = match &variant.fields {
                syn::Fields::Named(_) => unimplemented!("named fields aren't implemented yet"),
                syn::Fields::Unnamed(u) => {
                    let first_field = u.unnamed.first().unwrap();
                    let ty = &first_field.ty;
                    quote! {
                        impl Default for #ident {
                            fn default() -> Self {
                                Self::#first(#ty::default())
                            }
                        }
                    }
                }
                syn::Fields::Unit => {
                    quote! {
                        impl Default for #ident {
                            fn default() -> Self {
                                Self::#first
                            }
                        }
                    }
                }
            };
            token_stream.into()
        }
        _ => {
            unimplemented!("HacspecDefault only supports enums for now.");
        }
    }
}
