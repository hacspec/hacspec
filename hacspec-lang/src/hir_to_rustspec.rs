use im::HashMap;
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
                                        println!("Translating seq arg {:?}!", arg_ty);
                                        match translate_base_typ(tcx, &arg_ty) {
                                            Ok(t) => t,
                                            Err(()) => return Err(()),
                                        }
                                    }
                                    _ => return Err(()),
                                }
                            } else {
                                return Err(());
                            };
                            Ok(BaseTyp::Seq(Box::new((param_typ, DUMMY_SP))))
                        }
                        _ => Ok(BaseTyp::Named(
                            (Ident::Original(name.to_ident_string()), DUMMY_SP),
                            None,
                        )),
                    },
                    _ => Ok(BaseTyp::Named(
                        (Ident::Original(name.to_ident_string()), DUMMY_SP),
                        None,
                    )),
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
) -> HashMap<FnKey, Option<ExternalFuncSig>> {
    let krates = tcx.crates();
    let mut extern_funcs = HashMap::new();
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
                                    let export_sig = tcx.fn_sig(*id);
                                    let sig = match translate_polyfnsig(tcx, &export_sig) {
                                        Ok(sig) => Some(sig),
                                        Err(()) => None,
                                    };
                                    if def_path.data.len() == 1
                                        || (match def_path.data[def_path.data.len() - 2].data {
                                            DefPathData::Impl | DefPathData::ImplTrait => false,
                                            _ => true,
                                        })
                                    {
                                        // Function not within impl block
                                        let name_segment = def_path.data.last().unwrap();
                                        match name_segment.data {
                                            DefPathData::ValueNs(name) => {
                                                let fn_key = FnKey::Independent(Ident::Original(
                                                    name.to_ident_string(),
                                                ));
                                                extern_funcs.insert(fn_key, sig);
                                            }
                                            _ => (),
                                        }
                                    } else {
                                        // Function inside an impl block
                                        let impl_segment = def_path.data[def_path.data.len() - 2];
                                        let name_segment = def_path.data.last().unwrap();
                                        match (impl_segment.data, name_segment.data) {
                                            (DefPathData::Impl, DefPathData::ValueNs(name)) => {
                                                let impl_id = tcx.impl_of_method(*id).unwrap();
                                                println!("Trying!");
                                                let impl_type =
                                                    translate_base_typ(tcx, &tcx.type_of(impl_id));
                                                // TODO: distinguish between methods and static for types
                                                match impl_type {
                                                    Ok(impl_type) => {
                                                        let fn_key = FnKey::Impl(
                                                            impl_type,
                                                            Ident::Original(name.to_ident_string()),
                                                        );
                                                        extern_funcs.insert(fn_key, sig);
                                                    }
                                                    Err(()) => println!("Rejecting {:?}", *id),
                                                }
                                            }
                                            _ => (),
                                        }
                                    };
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
    // for (key, sig) in extern_funcs.iter() {
    //     println!(
    //         "Key in context: {:?} {}",
    //         key,
    //         match sig {
    //             None => "(no sig)",
    //             Some(_) => "",
    //         }
    //     );
    // }
    extern_funcs
}
