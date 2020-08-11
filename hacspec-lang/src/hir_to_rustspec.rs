use rustc_middle::middle::exported_symbols::ExportedSymbol;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;

use crate::rustspec::*;

pub fn retrieve_external_functions(_sess: &Session, tcx: &TyCtxt) -> Vec<FuncSig> {
    let krates = tcx.crates();
    let extern_funcs = Vec::new();
    for krate_num in krates {
        let exported_symbols = tcx.exported_symbols(*krate_num);
        let _original_crate_name = tcx.original_crate_name(*krate_num);
        for (exported_symbol, _) in exported_symbols {
            match exported_symbol {
                ExportedSymbol::Generic(_id, _) | ExportedSymbol::NonGeneric(_id) => {
                    ()
                }
                _ => (),
            }
        }
    }
    extern_funcs
}
