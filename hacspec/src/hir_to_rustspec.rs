use im::HashMap;
use rustc_ast::ast::{IntTy, UintTy};
use rustc_hir::definitions::DefPathData;
use rustc_middle::middle::exported_symbols::ExportedSymbol;
use rustc_middle::mir::terminator::Mutability;
use rustc_middle::ty::subst::GenericArgKind;
use rustc_middle::ty::{self, AssocKind, PolyFnSig, TyCtxt, TyKind};
use rustc_session::Session;
use rustc_span::{
    def_id::{CrateNum, DefId},
    DUMMY_SP,
};
use std::sync::atomic::Ordering;

use crate::rustspec::*;
use crate::typechecker::{FnKey, ID_COUNTER};

fn fresh_type_var() -> BaseTyp {
    BaseTyp::Variable(RustspecId(ID_COUNTER.fetch_add(1, Ordering::SeqCst)))
}

type TypVarContext = HashMap<usize, BaseTyp>;

fn translate_base_typ(
    tcx: &TyCtxt,
    ty: &ty::Ty,
    typ_ctx: &TypVarContext,
) -> Result<(BaseTyp, TypVarContext), ()> {
    match ty.kind {
        TyKind::Bool => Ok((BaseTyp::Bool, typ_ctx.clone())),
        TyKind::Int(IntTy::Isize) => Ok((BaseTyp::Isize, typ_ctx.clone())),
        TyKind::Int(IntTy::I8) => Ok((BaseTyp::Int8, typ_ctx.clone())),
        TyKind::Int(IntTy::I16) => Ok((BaseTyp::Int16, typ_ctx.clone())),
        TyKind::Int(IntTy::I32) => Ok((BaseTyp::Int32, typ_ctx.clone())),
        TyKind::Int(IntTy::I64) => Ok((BaseTyp::Int64, typ_ctx.clone())),
        TyKind::Int(IntTy::I128) => Ok((BaseTyp::Int128, typ_ctx.clone())),
        TyKind::Uint(UintTy::Usize) => Ok((BaseTyp::Usize, typ_ctx.clone())),
        TyKind::Uint(UintTy::U8) => Ok((BaseTyp::UInt8, typ_ctx.clone())),
        TyKind::Uint(UintTy::U16) => Ok((BaseTyp::UInt16, typ_ctx.clone())),
        TyKind::Uint(UintTy::U32) => Ok((BaseTyp::UInt32, typ_ctx.clone())),
        TyKind::Uint(UintTy::U64) => Ok((BaseTyp::UInt64, typ_ctx.clone())),
        TyKind::Uint(UintTy::U128) => Ok((BaseTyp::UInt128, typ_ctx.clone())),
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
                    "hacspec_lib" => match name.to_ident_string().as_str() {
                        "Seq" => {
                            let (param_typ, typ_ctx) = if substs.len() == 1 {
                                match substs.first().unwrap().unpack() {
                                    GenericArgKind::Type(arg_ty) => {
                                        match translate_base_typ(tcx, &arg_ty, typ_ctx) {
                                            Ok((t, typ_ctx)) => (t, typ_ctx),
                                            Err(()) => return Err(()),
                                        }
                                    }
                                    _ => return Err(()),
                                }
                            } else {
                                return Err(());
                            };
                            Ok((BaseTyp::Seq(Box::new((param_typ, DUMMY_SP))), typ_ctx))
                        }
                        _ => Ok((
                            BaseTyp::Named(
                                (Ident::Original(name.to_ident_string()), DUMMY_SP),
                                None,
                            ),
                            typ_ctx.clone(),
                        )),
                    },
                    _ => Ok((
                        BaseTyp::Named((Ident::Original(name.to_ident_string()), DUMMY_SP), None),
                        typ_ctx.clone(),
                    )),
                },

                _ => Err(()),
            }
        }
        TyKind::Param(_) => {
            // TODO: sophisticate
            Ok((BaseTyp::Wildcard, typ_ctx.clone()))
        }
        TyKind::Bound(_, _) => {
            // (TODO: sophisticate
            Ok((BaseTyp::Wildcard, typ_ctx.clone()))
        }
        _ => Err(()),
    }
}

fn translate_ty(
    tcx: &TyCtxt,
    ty: &ty::Ty,
    typ_ctx: &TypVarContext,
) -> Result<(Typ, TypVarContext), ()> {
    match ty.kind {
        TyKind::Ref(_, ref_ty, Mutability::Not) => {
            let (ty, typ_ctx) = translate_base_typ(tcx, &ref_ty, typ_ctx)?;
            Ok((((Borrowing::Borrowed, DUMMY_SP), (ty, DUMMY_SP)), typ_ctx))
        }
        _ => {
            let (ty, typ_ctx) = translate_base_typ(tcx, ty, typ_ctx)?;
            Ok((((Borrowing::Consumed, DUMMY_SP), (ty, DUMMY_SP)), typ_ctx))
        }
    }
}

fn translate_polyfnsig(tcx: &TyCtxt, sig: &PolyFnSig) -> Result<ExternalFuncSig, ()> {
    let typ_ctx = HashMap::new();
    let mut new_args = Vec::new();
    let typ_ctx = sig
        .inputs()
        .skip_binder()
        .iter()
        .fold(Ok(typ_ctx), |typ_ctx, ty| {
            let (new_ty, typ_ctx) = translate_ty(tcx, ty, &typ_ctx?)?;
            new_args.push(new_ty);
            Ok(typ_ctx)
        })?;
    let (ret, _) = translate_base_typ(tcx, &sig.output().skip_binder(), &typ_ctx)?;
    Ok(ExternalFuncSig {
        args: new_args,
        ret,
    })
}

fn process_fn_id(
    _sess: &Session,
    tcx: &TyCtxt,
    id: &DefId,
    krate_num: &CrateNum,
    extern_funcs: &mut HashMap<FnKey, Option<ExternalFuncSig>>,
) {
    match tcx.type_of(*id).kind {
        TyKind::FnDef(_, _) => {
            let def_path = tcx.def_path(*id);
            if def_path.krate == *krate_num {
                if def_path.data.len() == 1
                    || (match def_path.data[def_path.data.len() - 2].data {
                        DefPathData::Impl | DefPathData::ImplTrait => false,
                        _ => true,
                    })
                {
                    // Function not within impl block
                    let export_sig = tcx.fn_sig(*id);
                    let sig = match translate_polyfnsig(tcx, &export_sig) {
                        Ok(sig) => Some(sig),
                        Err(()) => None,
                    };
                    let name_segment = def_path.data.last().unwrap();
                    match name_segment.data {
                        DefPathData::ValueNs(name) => {
                            let fn_key =
                                FnKey::Independent(Ident::Original(name.to_ident_string()));
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
                            let impl_type = &tcx.type_of(impl_id);
                            let impl_type = translate_base_typ(tcx, impl_type, &HashMap::new());
                            // TODO: distinguish between methods and static for types
                            match impl_type {
                                Ok((impl_type, _)) => {
                                    let fn_key = FnKey::Impl(
                                        impl_type,
                                        Ident::Original(name.to_ident_string()),
                                    );
                                    let export_sig = tcx.fn_sig(*id);
                                    let sig = match translate_polyfnsig(tcx, &export_sig) {
                                        Ok(sig) => Some(sig),
                                        Err(()) => None,
                                    };
                                    extern_funcs.insert(fn_key, sig);
                                }
                                Err(()) => (),
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

pub fn retrieve_external_functions(
    sess: &Session,
    tcx: &TyCtxt,
    imported_crates: &Vec<Spanned<String>>,
) -> HashMap<FnKey, Option<ExternalFuncSig>> {
    let krates = tcx.crates();
    let mut extern_funcs = HashMap::new();
    for krate_num in krates {
        let exported_symbols = tcx.exported_symbols(*krate_num);
        let trait_impls = tcx.all_trait_implementations(*krate_num);
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
                        process_fn_id(sess, tcx, id, krate_num, &mut extern_funcs)
                    }
                    _ => (),
                }
            }
            for trait_impl_id in trait_impls {
                let assoc_items = tcx.associated_items(*trait_impl_id);
                for item in assoc_items.in_definition_order() {
                    if item.kind == AssocKind::Fn {
                        process_fn_id(sess, tcx, &item.def_id, krate_num, &mut extern_funcs)
                    }
                }
            }
        }
    }
    extern_funcs
}
