extern crate hacspec;
extern crate proc_macro;
extern crate proc_macro2;
extern crate quote;
extern crate syn;

use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn::spanned::Spanned;
use syn::{parse_macro_input, Data, DeriveInput, Fields, Ident, Index};

fn make_binop(name: &Ident, data: &Data, op: TokenStream) -> TokenStream {
    match *data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => {
                let recurse = fields.named.iter().map(|f| {
                    let name = &f.ident;
                    quote_spanned! {f.span() =>
                        #name: self.#name #op rhs.#name
                    }
                });
                let expanded = quote! {
                    #name { #(#recurse),* }
                };
                expanded
            }
            Fields::Unnamed(ref fields) => {
                let recurse = fields.unnamed.iter().enumerate().map(|(i, f)| {
                    let index = Index::from(i);
                    quote_spanned! {f.span() =>
                       self.#index #op rhs.#index
                    }
                });
                quote! {
                    #name ( #(#recurse),* )
                }
            }
            Fields::Unit => quote! { #name {} },
        },
        | Data::Enum(_)
        | Data::Union(_) => panic!("Deriving the Numeric trait is impossible for enums or unions"),
    }
}

#[proc_macro_derive(Numeric)]
pub fn derive_numeric_impl(input_struct: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input_ast = parse_macro_input!(input_struct as DeriveInput);

    // Used in the quasi-quotation below as `#name`.
    let name = input_ast.ident;
    let generics = input_ast.generics;
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let sum = make_binop(&name, &input_ast.data, quote! { + });
    let difference = make_binop(&name, &input_ast.data, quote! { - });
    let mul = make_binop(&name, &input_ast.data, quote! { * });
    let xor = make_binop(&name, &input_ast.data, quote! { ^ });
    let or = make_binop(&name, &input_ast.data, quote! { | });
    let and = make_binop(&name, &input_ast.data, quote! { & });

    let expanded = quote! {
        impl #impl_generics Add for #name #ty_generics #where_clause {
            type Output = Self;

            fn add(self, rhs: Self) -> Self {
                #sum
            }
        }

        impl #impl_generics Sub for #name #ty_generics #where_clause {
            type Output = Self;

            fn sub(self, rhs: Self) -> Self {
                #difference
            }
        }

        impl #impl_generics Mul for #name #ty_generics #where_clause {
            type Output = Self;

            fn mul(self, rhs: Self) -> Self {
                #mul
            }
        }

        impl #impl_generics BitXor for #name #ty_generics #where_clause {
            type Output = Self;

            fn bitxor(self, rhs: Self) -> Self {
                #xor
            }
        }

        impl #impl_generics BitOr for #name #ty_generics #where_clause {
            type Output = Self;

            fn bitor(self, rhs: Self) -> Self {
                #or
            }
        }

        impl #impl_generics BitAnd for #name #ty_generics #where_clause {
            type Output = Self;

            fn bitand(self, rhs: Self) -> Self {
                #and
            }
        }

        impl #impl_generics Shl<usize> for #name #ty_generics #where_clause {
            type Output = Self;

            fn shl(self, v: usize) -> Self {
                todo!();
            }
        }

        impl #impl_generics Shr<usize> for #name #ty_generics #where_clause {
            type Output = Self;

            fn shr(self, v: usize) -> Self {
                todo!();
            }
        }

        impl #impl_generics Not for #name #ty_generics #where_clause {
            type Output = Self;

            fn not(self) -> Self {
                todo!();
            }
        }

        impl #impl_generics ModNumeric for #name #ty_generics #where_clause  {
            /// (self - rhs) % n.
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                todo!();
            }
            /// `(self + rhs) % n`
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                todo!();
            }
            /// `(self * rhs) % n`
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                todo!();
            }
            /// `(self ^ exp) % n`
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                todo!();
            }
            /// `self % n`
            fn modulo(self, n: Self) -> Self {
                todo!();
            }
            /// `self % n` that always returns a positive integer
            fn signed_modulo(self, n: Self) -> Self {
                todo!();
            }
            /// `|self|`
            fn absolute(self) -> Self {
                todo!();
            }
        }

        impl #impl_generics Numeric for #name #ty_generics #where_clause {
            /// Return largest value that can be represented.
            fn max_val() -> Self  {
                todo!();
            }

            fn wrap_add(self, rhs: Self) -> Self  {
                todo!();
            }
            fn wrap_sub(self, rhs: Self) -> Self  {
                todo!();
            }
            fn wrap_mul(self, rhs: Self) -> Self  {
                todo!();
            }
            fn wrap_div(self, rhs: Self) -> Self  {
                todo!();
            }

            /// `self ^ exp` where `exp` is a `u32`.
            fn exp(self, exp: u32) -> Self  {
                todo!();
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, exp: Self) -> Self  {
                todo!();
            }
            /// Division.
            fn divide(self, rhs: Self) -> Self  {
                todo!();
            }
            /// Invert self modulo n.
            fn inv(self, n: Self) -> Self  {
                todo!();
            }

            // Comparison functions returning bool.
            fn equal(self, other: Self) -> bool  {
                todo!();
            }
            fn greater_than(self, other: Self) -> bool  {
                todo!();
            }
            fn greater_than_or_qual(self, other: Self) -> bool  {
                todo!();
            }
            fn less_than(self, other: Self) -> bool  {
                todo!();
            }
            fn less_than_or_equal(self, other: Self) -> bool  {
                todo!();
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            fn not_equal_bm(self, other: Self) -> Self  {
                todo!();
            }
            fn equal_bm(self, other: Self) -> Self  {
                todo!();
            }
            fn greater_than_bm(self, other: Self) -> Self  {
                todo!();
            }
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                todo!();
            }
            fn less_than_bm(self, other: Self) -> Self  {
                todo!();
            }
            fn less_than_or_equal_bm(self, other: Self) -> Self  {
                todo!();
            }
        };
    };

    proc_macro::TokenStream::from(expanded)
}
