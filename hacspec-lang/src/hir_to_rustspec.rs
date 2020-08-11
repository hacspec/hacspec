use im::{HashMap, HashSet};
use rustc_middle::middle::exported_symbols::ExportedSymbol;
use rustc_middle::ty::{PolyFnSig, TyCtxt, TyKind};
use rustc_session::Session;

use crate::rustspec::*;
use crate::typechecker::FnKey;

fn translate_polyfnsig(_sig: &PolyFnSig) -> Result<FuncSig, ()> {
    //TODO: implement
    Err(())
}

pub fn retrieve_external_functions(
    _sess: &Session,
    tcx: &TyCtxt,
    imported_crates: &Vec<Spanned<String>>,
) -> HashMap<FnKey, FuncSig> {
    let krates = tcx.crates();
    let mut def_ids_to_fetch = HashSet::new();
    let extern_funcs = HashMap::new();
    for krate_num in krates {
        let exported_symbols = tcx.exported_symbols(*krate_num);
        let original_crate_name = tcx.original_crate_name(*krate_num);
        if imported_crates
            .iter()
            .filter(|(imported_crate, _)| *imported_crate == original_crate_name.to_ident_string())
            .collect::<Vec<_>>()
            .len()
            > 0
        {
            for (exported_symbol, _) in exported_symbols {
                match exported_symbol {
                    ExportedSymbol::Generic(id, _) | ExportedSymbol::NonGeneric(id) => {
                        match tcx.type_of(*id).kind {
                            TyKind::FnDef(_, _) => {
                                let def_path = tcx.def_path(*id);
                                if def_path.krate == *krate_num {
                                    def_ids_to_fetch.insert(*id);
                                }
                            }
                            _ => (),
                        };
                    }
                    _ => (),
                }
            }
        }
    }
    for id in def_ids_to_fetch {
        let export_sig = tcx.fn_sig(id);
        match translate_polyfnsig(&export_sig) {
            Ok(_sig) => (),
            Err(()) => (),
        }
    }
    extern_funcs
}
