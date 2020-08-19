use serde::{Deserialize, Serialize};
use syn;

#[derive(Serialize, Deserialize, Debug, Hash, PartialEq, Eq)]
pub struct Signature {
    pub name: String,
}

pub fn syn_sig_to_reduced(sig: &syn::Signature) -> Signature {
    Signature {
        name: format!("{}", sig.ident),
    }
}
