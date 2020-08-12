use im::{HashMap, HashSet};
use rustc_ast::ast::{IntTy, UintTy};
use rustc_hir::definitions::DefPathData;
use rustc_middle::middle::exported_symbols::ExportedSymbol;
use rustc_middle::mir::terminator::Mutability;
use rustc_middle::ty::subst::GenericArgKind;
use rustc_middle::ty::{self, PolyFnSig, TyCtxt, TyKind};
use rustc_session::Session;
use rustc_span::DUMMY_SP;

use crate::rustspec::*;
use crate::typechecker::FnKey;

fn check_vec<T>(v: Vec<Result<T, ()>>) -> Result<Vec<T>, ()> {
    if v.iter().all(|t| t.is_ok()) {
        Ok(v.into_iter().map(|t| t.unwrap()).collect())
    } else {
        Err(())
    }
}

fn translate_base_typ(tcx: &TyCtxt, ty: &ty::Ty) -> Result<BaseTyp, ()> {
    match ty.kind {
        TyKind::Bool => Ok(BaseTyp::Bool),
        TyKind::Int(IntTy::Isize) => Ok(BaseTyp::Isize),
        TyKind::Int(IntTy::I8) => Ok(BaseTyp::Int8),
        TyKind::Int(IntTy::I16) => Ok(BaseTyp::Int16),
        TyKind::Int(IntTy::I32) => Ok(BaseTyp::Int32),
        TyKind::Int(IntTy::I64) => Ok(BaseTyp::Int64),
        TyKind::Int(IntTy::I128) => Ok(BaseTyp::Int128),
        TyKind::Uint(UintTy::Usize) => Ok(BaseTyp::Usize),
        TyKind::Uint(UintTy::U8) => Ok(BaseTyp::UInt8),
        TyKind::Uint(UintTy::U16) => Ok(BaseTyp::UInt16),
        TyKind::Uint(UintTy::U32) => Ok(BaseTyp::UInt32),
        TyKind::Uint(UintTy::U64) => Ok(BaseTyp::UInt64),
        TyKind::Uint(UintTy::U128) => Ok(BaseTyp::UInt128),
        TyKind::Adt(adt, substs) => {
            let adt_id = adt.did;
            let adt_def_path = tcx.def_path(adt_id);
            // We're looking at types from imported crates that can only be imported
            // with * blobs so the types have to be re-exported from inner modules,
            // which is why we only consider the last path segment (there should not
            // be ambiguities)
            match adt_def_path.data.last().unwrap().data {
                DefPathData::TypeNs(name) => match tcx
                    .original_crate_name(adt_def_path.krate)
                    .to_ident_string()
                    .as_str()
                {
                    "hacspec" => match name.to_ident_string().as_str() {
                        "Seq" => {
                            let param_typ = if substs.len() == 1 {
                                match substs.first().unwrap().unpack() {
                                    GenericArgKind::Type(arg_ty) => {
                                        translate_base_typ(tcx, &arg_ty)?
                                    }
                                    _ => return Err(()),
                                }
                            } else {
                                return Err(());
                            };
                            Ok(BaseTyp::Seq(Box::new((param_typ, DUMMY_SP))))
                        }
                        _ => Ok(BaseTyp::Named(Path {
                            location: vec![(Ident::Original(name.to_ident_string()), DUMMY_SP)],
                            arg: None,
                        })),
                    },
                    _ => Ok(BaseTyp::Named(Path {
                        location: vec![(Ident::Original(name.to_ident_string()), DUMMY_SP)],
                        arg: None,
                    })),
                },

                _ => Err(()),
            }
        }
        _ => Err(()),
    }
}

fn translate_ty(tcx: &TyCtxt, ty: &ty::Ty) -> Result<Typ, ()> {
    match ty.kind {
        TyKind::Ref(_, ref_ty, Mutability::Not) => Ok((
            (Borrowing::Borrowed, DUMMY_SP),
            (translate_base_typ(tcx, &ref_ty)?, DUMMY_SP),
        )),
        _ => Ok((
            (Borrowing::Borrowed, DUMMY_SP),
            (translate_base_typ(tcx, ty)?, DUMMY_SP),
        )),
    }
}

fn translate_polyfnsig(tcx: &TyCtxt, sig: &PolyFnSig) -> Result<ExternalFuncSig, ()> {
    Ok(ExternalFuncSig {
        args: check_vec(
            sig.inputs()
                .skip_binder()
                .iter()
                .map(|ty| translate_ty(tcx, ty))
                .collect(),
        )?,
        ret: translate_base_typ(tcx, &sig.output().skip_binder())?,
    })
}

pub fn retrieve_external_functions(
    _sess: &Session,
    tcx: &TyCtxt,
    imported_crates: &Vec<Spanned<String>>,
) -> HashMap<FnKey, ExternalFuncSig> {
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
        match translate_polyfnsig(tcx, &export_sig) {
            Ok(_sig) => (),
            Err(()) => ()
        }
    }
    extern_funcs
}
