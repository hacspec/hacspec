use rustc_ast::ast::{AttrKind, AttrStyle};
use rustc_hir::{self, Crate, ItemKind};
use rustc_middle::middle::exported_symbols::ExportedSymbol;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use rustc_span::{Span, Symbol};

use crate::rustspec::*;

pub fn retrieve_external_functions(sess: &Session, tcx: &TyCtxt) -> Vec<ExternFunc> {
    let krates = tcx.crates();
    let mut extern_funcs = Vec::new();
    for krate_num in krates {
        let exported_symbols = tcx.exported_symbols(*krate_num);
        let original_crate_name = tcx.original_crate_name(*krate_num);
        if original_crate_name != Symbol::intern("hacspec") {
            continue;
        }
        println!("Processing new crate! {}", original_crate_name);
        for (exported_symbol, _) in exported_symbols {
            match exported_symbol {
                // TODO: check if it's really not necessary to include ExportedSymbol::Generic
                ExportedSymbol::Generic(id, _) | ExportedSymbol::NonGeneric(id) => {
                    for attribute in tcx.get_attrs(*id) {
                        match (&attribute.style, &attribute.kind) {
                            (_, AttrKind::Normal(attr)) => {
                                ()
                            }
                            _ => (),
                        }
                    }
                }
                _ => (),
            }
        }
    }
    extern_funcs
}
