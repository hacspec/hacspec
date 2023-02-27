use creusot_contracts::trusted;
use serde::{Deserialize, Serialize};
use syn;

// #[derive(Serialize, Deserialize, Debug, Hash, PartialEq, Eq)]
pub struct Signature {
    pub name: String,
}

#[trusted]
pub fn syn_sig_to_reduced(sig: &syn::Signature) -> Signature {
    Signature {
        name: sig.ident.to_string() // format!("{}", sig.ident)
            ,
    }
}
