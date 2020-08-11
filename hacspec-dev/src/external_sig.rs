use serde::{Serialize, Deserialize};
use syn;

#[derive(Serialize, Deserialize, Debug, Hash, PartialEq, Eq)]
pub struct Signature {
    pub name: String,
    pub method: Option<String>,
}

pub fn syn_sig_to_reduced(sig: &syn::Signature, method_name: Option<String>) -> Signature {
    Signature {
        name: format!("{}", sig.ident),
        method: method_name
    }
}
