extern crate proc_macro;
use proc_macro::TokenStream as TokenStream;
use quote::{format_ident, quote, ToTokens};
use syn::{parse_macro_input, DeriveInput, FieldsNamed, Type};

#[proc_macro_derive(Codec)]
pub fn derive_codec_impl(input: TokenStream) -> TokenStream {
    let mut input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;

    let impl_block = quote! {
        impl Codec for #name {
            fn encode(self) -> Bytes {
                Seq::new(32)
            }
            fn decode(b:Bytes) -> Option<#name> {
                None
            }
        }
    };

    proc_macro::TokenStream::from(impl_block)
}

/*
// I would like to derive the following from a macro without writing it out
impl Codec for ProtocolMessage {
    fn encode(self) -> Bytes {
        match self {
            ProtocolMessage::Msg1 {n_a,a} => n_a.concat(&a).push(&U8(0)),
            ProtocolMessage::Msg2 {n_a,n_b,b} => n_a.concat(&n_b).concat(&b).push(&U8(1)),
            ProtocolMessage::Msg3 {n_b,a} => n_b.concat(&a).push(&U8(2)),
        }     
    }
    fn decode(b:Bytes) -> Option<ProtocolMessage> {
        if b.len() < 1 {None}
        else
         {if b[b.len()-1].declassify() == 0 && b.len() == 65 {
            Some(ProtocolMessage::Msg1{n_a:Nonce::from_slice(&b,0,32),a:Principal::from_slice(&b,32,32)})}
          else {if b[b.len()-1].declassify() == 1 && b.len() == 97 {
                    Some(ProtocolMessage::Msg2{n_a:Nonce::from_slice(&b,0,32),n_b:Nonce::from_slice(&b,32,32),b:Principal::from_slice(&b,64,32)})}
                else {if b[b.len()-1].declassify() == 2 && b.len() == 65 {
                            Some(ProtocolMessage::Msg3{n_b:Nonce::from_slice(&b,0,32),a:Principal::from_slice(&b,32,32)})}
                      else {None}}}}
    }
} */