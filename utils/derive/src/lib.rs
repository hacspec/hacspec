extern crate hacspec_lib;
extern crate proc_macro;
extern crate proc_macro2;
extern crate quote;
extern crate syn;

use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn::spanned::Spanned;
use syn::{parse_macro_input, Data, DeriveInput, Fields, Ident, Index};

enum Expression {
    Binop(TokenStream, TokenStream, TokenStream),
    Shift(TokenStream, TokenStream, TokenStream),
    Unop(TokenStream, TokenStream),
    TwoArgsMethod(TokenStream, TokenStream, TokenStream),
    OneArgsMethod(TokenStream, TokenStream),
    OneArgsMethodWithBaseTypeArg(TokenStream, TokenStream),
    ZeroArgsMethod(TokenStream),
}

fn make_impl_body(name: &Ident, data: &Data, inner_expression: Expression) -> TokenStream {
    match *data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => {
                let recurse = fields.named.iter().map(|f| {
                    let name = &f.ident;
                    match &inner_expression {
                        Expression::Binop(e1, op, e2) => quote_spanned! {f.span() =>
                            #name: #e1.#name #op #e2.#name
                        },
                        Expression::Shift(e1, op, e2) => quote_spanned! {f.span() =>
                            #name: #e1.#name #op #e2
                        },
                        Expression::Unop(op, e) => quote_spanned! {f.span() =>
                            #name: #op #e.#name
                        },
                        Expression::TwoArgsMethod(func, e1, e2) => quote_spanned! {f.span() =>
                            #name: self.#name.#func(#e1.#name, #e2.#name)
                        },
                        Expression::OneArgsMethod(func, e1) => quote_spanned! {f.span() =>
                            #name: self.#name.#func(#e1.#name)
                        },
                        Expression::OneArgsMethodWithBaseTypeArg(func, e1) => {
                            quote_spanned! {f.span() =>
                                #name: self.#name.#func(#e1)
                            }
                        }
                        Expression::ZeroArgsMethod(func) => quote_spanned! {f.span() =>
                            #name: self.#name.#func()
                        },
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
                    match &inner_expression {
                        Expression::Binop(e1, op, e2) => quote_spanned! {f.span() =>
                            #e1.#index #op #e2.#index
                        },
                        Expression::Shift(e1, op, e2) => quote_spanned! {f.span() =>
                            #e1.#index #op #e2
                        },
                        Expression::Unop(op, e) => quote_spanned! {f.span() =>
                            #op #e.#index
                        },
                        Expression::TwoArgsMethod(func, e1, e2) => quote_spanned! {f.span() =>
                            self.#index.#func(#e1.#index, #e2.#index)
                        },
                        Expression::OneArgsMethod(func, e1) => quote_spanned! {f.span() =>
                            self.#index.#func(#e1.#index)
                        },
                        Expression::OneArgsMethodWithBaseTypeArg(func, e1) => {
                            quote_spanned! {f.span() =>
                                self.#index.#func(#e1)
                            }
                        }
                        Expression::ZeroArgsMethod(func) => quote_spanned! {f.span() =>
                            self.#index.#func()
                        },
                    }
                });
                quote! {
                    #name ( #(#recurse),* )
                }
            }
            Fields::Unit => quote! { #name {} },
        },
        Data::Enum(_) | Data::Union(_) => {
            panic!("Deriving the Numeric trait is impossible for enums or unions")
        }
    }
}

#[proc_macro_derive(Numeric)]
pub fn derive_numeric_impl(input_struct: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input_ast = parse_macro_input!(input_struct as DeriveInput);

    // Used in the quasi-quotation below as `#name`.
    let name = input_ast.ident;
    let generics = input_ast.generics;
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let sum = make_impl_body(
        &name,
        &input_ast.data,
        Expression::Binop(quote! { self }, quote! { + }, quote! { rhs }),
    );
    let difference = make_impl_body(
        &name,
        &input_ast.data,
        Expression::Binop(quote! { self }, quote! { - }, quote! { rhs }),
    );
    let mul = make_impl_body(
        &name,
        &input_ast.data,
        Expression::Binop(quote! { self }, quote! { * }, quote! { rhs }),
    );
    let xor = make_impl_body(
        &name,
        &input_ast.data,
        Expression::Binop(quote! { self }, quote! { ^ }, quote! { rhs }),
    );
    let or = make_impl_body(
        &name,
        &input_ast.data,
        Expression::Binop(quote! { self }, quote! { | }, quote! { rhs }),
    );
    let and = make_impl_body(
        &name,
        &input_ast.data,
        Expression::Binop(quote! { self }, quote! { & }, quote! { rhs }),
    );
    let shl = make_impl_body(
        &name,
        &input_ast.data,
        Expression::Shift(quote! { self }, quote! { << }, quote! { v }),
    );
    let shr = make_impl_body(
        &name,
        &input_ast.data,
        Expression::Shift(quote! { self }, quote! { >> }, quote! { v }),
    );
    let not = make_impl_body(
        &name,
        &input_ast.data,
        Expression::Unop(quote! { ! }, quote! { self}),
    );
    let sub_mod = make_impl_body(
        &name,
        &input_ast.data,
        Expression::TwoArgsMethod(quote! { sub_mod }, quote! { rhs }, quote! { n }),
    );
    let add_mod = make_impl_body(
        &name,
        &input_ast.data,
        Expression::TwoArgsMethod(quote! { add_mod }, quote! { rhs }, quote! { n }),
    );
    let mul_mod = make_impl_body(
        &name,
        &input_ast.data,
        Expression::TwoArgsMethod(quote! { mul_mod }, quote! { rhs }, quote! { n }),
    );
    let pow_mod = make_impl_body(
        &name,
        &input_ast.data,
        Expression::TwoArgsMethod(quote! { pow_mod }, quote! { exp }, quote! { n }),
    );
    let modulo = make_impl_body(
        &name,
        &input_ast.data,
        Expression::OneArgsMethod(quote! { modulo }, quote! { n }),
    );
    let signed_modulo = make_impl_body(
        &name,
        &input_ast.data,
        Expression::OneArgsMethod(quote! { signed_modulo }, quote! { n }),
    );
    let wrap_add = make_impl_body(
        &name,
        &input_ast.data,
        Expression::OneArgsMethod(quote! { wrap_add }, quote! { rhs }),
    );
    let wrap_sub = make_impl_body(
        &name,
        &input_ast.data,
        Expression::OneArgsMethod(quote! { wrap_sub }, quote! { rhs }),
    );
    let wrap_mul = make_impl_body(
        &name,
        &input_ast.data,
        Expression::OneArgsMethod(quote! { wrap_mul }, quote! { rhs }),
    );
    let wrap_div = make_impl_body(
        &name,
        &input_ast.data,
        Expression::OneArgsMethod(quote! { wrap_div }, quote! { rhs }),
    );
    let pow_self = make_impl_body(
        &name,
        &input_ast.data,
        Expression::OneArgsMethod(quote! { pow_self }, quote! { exp }),
    );
    let divide = make_impl_body(
        &name,
        &input_ast.data,
        Expression::OneArgsMethod(quote! { divide }, quote! { rhs }),
    );
    let inv = make_impl_body(
        &name,
        &input_ast.data,
        Expression::OneArgsMethod(quote! { inv }, quote! { n }),
    );
    let absolute = make_impl_body(
        &name,
        &input_ast.data,
        Expression::ZeroArgsMethod(quote! { absolute }),
    );
    let exp = make_impl_body(
        &name,
        &input_ast.data,
        Expression::OneArgsMethodWithBaseTypeArg(quote! { exp }, quote! { exp }),
    );

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
                #shl
            }
        }

        impl #impl_generics Shr<usize> for #name #ty_generics #where_clause {
            type Output = Self;

            fn shr(self, v: usize) -> Self {
                #shr
            }
        }

        impl #impl_generics Not for #name #ty_generics #where_clause {
            type Output = Self;

            fn not(self) -> Self {
                #not
            }
        }

        impl #impl_generics ModNumeric for #name #ty_generics #where_clause  {
            /// (self - rhs) % n.
            fn sub_mod(self, rhs: Self, n: Self) -> Self {
                #sub_mod
            }
            /// `(self + rhs) % n`
            fn add_mod(self, rhs: Self, n: Self) -> Self {
                #add_mod
            }
            /// `(self * rhs) % n`
            fn mul_mod(self, rhs: Self, n: Self) -> Self {
                #mul_mod
            }
            /// `(self ^ exp) % n`
            fn pow_mod(self, exp: Self, n: Self) -> Self {
                #pow_mod
            }
            /// `self % n`
            fn modulo(self, n: Self) -> Self {
                #modulo
            }
            /// `self % n` that always returns a positive integer
            fn signed_modulo(self, n: Self) -> Self {
                #signed_modulo
            }
            /// `|self|`
            fn absolute(self) -> Self {
                #absolute
            }
        }

        impl #impl_generics Numeric for #name #ty_generics #where_clause {
            /// Return largest value that can be represented.
            fn max_val() -> Self  {
                panic!("Function not implemented by auto-deriving...")
            }

            fn wrap_add(self, rhs: Self) -> Self  {
                #wrap_add
            }
            fn wrap_sub(self, rhs: Self) -> Self  {
                #wrap_sub
            }
            fn wrap_mul(self, rhs: Self) -> Self  {
                #wrap_mul
            }
            fn wrap_div(self, rhs: Self) -> Self  {
                #wrap_div
            }

            /// `self ^ exp` where `exp` is a `u32`.
            fn exp(self, exp: u32) -> Self  {
                #exp
            }
            /// `self ^ exp` where `exp` is a `Self`.
            fn pow_self(self, exp: Self) -> Self  {
                #pow_self
            }
            /// Division.
            fn divide(self, rhs: Self) -> Self  {
                #divide
            }
            /// Invert self modulo n.
            fn inv(self, n: Self) -> Self  {
                #inv
            }

            // Comparison functions returning bool.
            fn equal(self, other: Self) -> bool  {
                panic!("Function not implemented by auto-deriving...")
            }
            fn greater_than(self, other: Self) -> bool  {
                panic!("Function not implemented by auto-deriving...")
            }
            fn greater_than_or_qual(self, other: Self) -> bool  {
                panic!("Function not implemented by auto-deriving...")
            }
            fn less_than(self, other: Self) -> bool  {
                panic!("Function not implemented by auto-deriving...")
            }
            fn less_than_or_equal(self, other: Self) -> bool  {
                panic!("Function not implemented by auto-deriving...")
            }

            // Comparison functions returning a bit mask (0x0..0 or 0xF..F).
            fn not_equal_bm(self, other: Self) -> Self  {
                panic!("Function not implemented by auto-deriving...")
            }
            fn equal_bm(self, other: Self) -> Self  {
                panic!("Function not implemented by auto-deriving...")
            }
            fn greater_than_bm(self, other: Self) -> Self  {
                panic!("Function not implemented by auto-deriving...")
            }
            fn greater_than_or_equal_bm(self, other: Self) -> Self {
                panic!("Function not implemented by auto-deriving...")
            }
            fn less_than_bm(self, other: Self) -> Self  {
                panic!("Function not implemented by auto-deriving...")
            }
            fn less_than_or_equal_bm(self, other: Self) -> Self  {
                panic!("Function not implemented by auto-deriving...")
            }
        };
    };

    proc_macro::TokenStream::from(expanded)
}
