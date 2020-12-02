extern crate rustc_ast;
extern crate rustc_hir;
extern crate rustc_metadata;
extern crate rustc_middle;

use im::HashMap;
use rustc_ast::ast::{IntTy, UintTy};
use rustc_hir::{definitions::DefPathData, AssocItemKind, ItemKind};
use rustc_metadata::creader::CStore;
use rustc_middle::middle::cstore::CrateStore;
use rustc_middle::mir::interpret::{ConstValue, Scalar};
use rustc_middle::mir::terminator::Mutability;
use rustc_middle::ty::subst::GenericArgKind;
use rustc_middle::ty::{self, ConstKind, PolyFnSig, RegionKind, TyCtxt, TyKind};
use rustc_session::Session;
use rustc_span::{
    def_id::{CrateNum, DefId, LOCAL_CRATE},
    DUMMY_SP,
};
use std::sync::atomic::Ordering;

use crate::rustspec::*;
use crate::typechecker::{FnKey, ID_COUNTER};

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
enum ParamType {
    ImplParam,
    FnParam,
}

type TypVarContext = HashMap<(ParamType, usize), BaseTyp>;

fn fresh_type_var(
    rust_id: usize,
    p: ParamType,
    typ_ctx: &TypVarContext,
) -> (BaseTyp, TypVarContext) {
    let t = BaseTyp::Variable(HacspecId(ID_COUNTER.fetch_add(1, Ordering::SeqCst)));
    (t.clone(), typ_ctx.update((p, rust_id), t))
}

fn translate_base_typ(
    tcx: &TyCtxt,
    ty: &ty::Ty,
    typ_ctx: &TypVarContext,
) -> Result<(BaseTyp, TypVarContext), ()> {
    match ty.kind() {
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
        TyKind::Ref(region, inner_ty, mutability) => match region {
            RegionKind::ReStatic => match mutability {
                Mutability::Not => match inner_ty.kind() {
                    TyKind::Str => Ok((BaseTyp::Str, typ_ctx.clone())),
                    _ => Err(()),
                },
                _ => Err(()),
            },
            _ => Err(()),
        },
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
                        "Seq" | "PublicSeq" | "SecretSeq" => {
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
                        // We accept all named types from hacspec_lib because of the predefined
                        // array types like U32Word, etc.
                        _ => Ok((
                            BaseTyp::Named(
                                (Ident::Original(name.to_ident_string()), DUMMY_SP),
                                None,
                            ),
                            typ_ctx.clone(),
                        )),
                    },
                    "core" => match name.to_ident_string().as_str() {
                        "Range" => {
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
                            Ok((
                                BaseTyp::Tuple(vec![
                                    (param_typ.clone(), DUMMY_SP),
                                    (param_typ, DUMMY_SP),
                                ]),
                                typ_ctx,
                            ))
                        }
                        _ => Err(()),
                    },
                    _ => Ok((
                        BaseTyp::Named((Ident::Original(name.to_ident_string()), DUMMY_SP), None),
                        typ_ctx.clone(),
                    )),
                },
                _ => Err(()),
            }
        }
        TyKind::Param(p) => match typ_ctx.get(&(ParamType::ImplParam, p.index as usize)) {
            None => {
                let (id_typ, typ_ctx) =
                    fresh_type_var(p.index as usize, ParamType::ImplParam, typ_ctx);
                Ok((id_typ, typ_ctx))
            }
            Some(id_typ) => Ok((id_typ.clone(), typ_ctx.clone())),
        },
        TyKind::Bound(rust_id, _) => match typ_ctx.get(&(ParamType::FnParam, rust_id.index())) {
            None => {
                let (id_typ, typ_ctx) =
                    fresh_type_var(rust_id.index(), ParamType::FnParam, typ_ctx);
                Ok((id_typ, typ_ctx))
            }
            Some(id_typ) => Ok((id_typ.clone(), typ_ctx.clone())),
        },
        TyKind::Tuple(args) => {
            let mut new_args = Vec::new();
            let typ_ctx = args.types().fold(Ok(typ_ctx.clone()), |typ_ctx, ty| {
                let (new_ty, typ_ctx) = translate_base_typ(tcx, &ty, &typ_ctx?)?;
                new_args.push((new_ty, DUMMY_SP));
                Ok(typ_ctx)
            })?;
            Ok((BaseTyp::Tuple(new_args), typ_ctx))
        }
        _ => Err(()),
    }
}

fn translate_ty(
    tcx: &TyCtxt,
    ty: &ty::Ty,
    typ_ctx: &TypVarContext,
) -> Result<(Typ, TypVarContext), ()> {
    match ty.kind() {
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

fn translate_polyfnsig(
    tcx: &TyCtxt,
    sig: &PolyFnSig,
    typ_ctx: &TypVarContext,
) -> Result<ExternalFuncSig, ()> {
    // The type context maps De Bruijn indexed types in the signature
    // to Hacspec type variables
    let mut new_args = Vec::new();
    let typ_ctx = sig
        .inputs()
        .skip_binder()
        .iter()
        .fold(Ok(typ_ctx.clone()), |typ_ctx, ty| {
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

fn insert_extern_func(
    extern_funcs: &mut HashMap<FnKey, Result<ExternalFuncSig, String>>,
    fn_key: FnKey,
    sig: Result<ExternalFuncSig, String>,
) {
    // Here we can deal with function name clashes
    // When two functions have the same name, we can only keep one of them
    // If one of the two is not in hacspec then we keep the other
    // If the two are in hacspec then we decide in an ad hoc way
    match extern_funcs.get(&fn_key) {
        None => {
            extern_funcs.insert(fn_key, sig);
        }
        Some(old_sig) => match (old_sig, &sig) {
            (Ok(_), Err(_)) => (),
            _ => {
                extern_funcs.insert(fn_key, sig);
            }
        },
    }
}

fn process_fn_id(
    _sess: &Session,
    tcx: &TyCtxt,
    id: &DefId,
    krate_num: &CrateNum,
    extern_funcs: &mut HashMap<FnKey, Result<ExternalFuncSig, String>>,
) {
    match tcx.type_of(*id).kind() {
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
                    let sig = match translate_polyfnsig(tcx, &export_sig, &HashMap::new()) {
                        Ok(sig) => Ok(sig),
                        Err(()) => Err(format!("{}", export_sig)),
                    };
                    let name_segment = def_path.data.last().unwrap();
                    match name_segment.data {
                        DefPathData::ValueNs(name) => {
                            let fn_key =
                                FnKey::Independent(Ident::Original(name.to_ident_string()));
                            insert_extern_func(extern_funcs, fn_key, sig);
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
                                Ok((impl_type, typ_ctx)) => {
                                    let fn_key = FnKey::Impl(
                                        impl_type,
                                        Ident::Original(name.to_ident_string()),
                                    );
                                    let export_sig = tcx.fn_sig(*id);
                                    let sig = match translate_polyfnsig(tcx, &export_sig, &typ_ctx)
                                    {
                                        Ok(sig) => Ok(sig),
                                        Err(()) => Err(format!("{}", export_sig)),
                                    };
                                    insert_extern_func(extern_funcs, fn_key, sig);
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

fn add_array_type_from_ctor_sig(
    tcx: &TyCtxt,
    sig: &PolyFnSig,
    external_arrays: &mut HashMap<String, BaseTyp>,
) {
    let ret = sig.output().skip_binder();
    match ret.kind() {
        TyKind::Adt(adt, substs) => {
            if substs.len() > 0 {
                return ();
            }
            if adt.variants.len() != 1 {
                return ();
            }
            for variant in adt.variants.iter() {
                if variant.fields.len() != 1 {
                    return ();
                }
                for field in variant.fields.iter() {
                    match tcx.type_of(field.did).kind() {
                        TyKind::Array(cell_t, size) => {
                            let (new_cell_t, _) =
                                match translate_base_typ(tcx, cell_t, &HashMap::new()) {
                                    Ok(x) => x,
                                    Err(()) => return (),
                                };
                            let new_size = match &size.val {
                                ConstKind::Value(value) => match value {
                                    ConstValue::Scalar(scalar) => match scalar {
                                        Scalar::Int(s) => s.to_bits(s.size()).unwrap() as usize,
                                        _ => return (),
                                    },
                                    _ => return (),
                                },
                                _ => return (),
                            };
                            let array_typ = BaseTyp::Array(
                                (ArraySize::Integer(new_size), DUMMY_SP),
                                Box::new((new_cell_t, DUMMY_SP)),
                            );
                            let array_name =
                                tcx.def_path(adt.did).data.last().unwrap().data.to_string();
                            external_arrays.insert(array_name, array_typ);
                        }
                        _ => return (),
                    }
                }
            }
            ()
        }
        _ => (),
    }
}

pub fn retrieve_external_functions(
    sess: &Session,
    tcx: &TyCtxt,
    imported_crates: &Vec<Spanned<String>>,
) -> (
    HashMap<FnKey, Result<ExternalFuncSig, String>>,
    HashMap<String, BaseTyp>,
) {
    let mut krates: Vec<_> = tcx.crates().iter().collect();
    krates.push(&LOCAL_CRATE);
    let mut extern_funcs = HashMap::new();
    let mut extern_arrays = HashMap::new();
    let crate_store = tcx.cstore_as_any().downcast_ref::<CStore>().unwrap();
    let mut imported_crates = imported_crates.clone();
    // You normally only import hacspec_lib which then reexports the definitions
    // from abstract_integers and secret_integers. But we do have to fetch those
    // reexported definitions here and thus need to examine the original crates
    // containing them
    imported_crates.push(("core".to_string(), DUMMY_SP));
    imported_crates.push(("abstract_integers".to_string(), DUMMY_SP));
    imported_crates.push(("secret_integers".to_string(), DUMMY_SP));
    for krate_num in krates {
        let original_crate_name = tcx.original_crate_name(*krate_num);
        if imported_crates
            .iter()
            .filter(|(imported_crate, _)| {
                *imported_crate == original_crate_name.to_ident_string()
                    || original_crate_name.to_ident_string()
                        == tcx.crate_name(LOCAL_CRATE).to_ident_string()
            })
            .collect::<Vec<_>>()
            .len()
            > 0
        {
            if *krate_num != LOCAL_CRATE {
                let def_ids = <CStore as CrateStore>::all_def_path_hashes_and_def_ids(
                    crate_store,
                    *krate_num,
                );
                for (_, def_id) in def_ids {
                    let def_path = tcx.def_path(def_id);
                    match &def_path.data.last() {
                        Some(x) => {
                            // We only import things really defined in the crate
                            if tcx.original_crate_name(def_path.krate).to_ident_string()
                                == original_crate_name.to_ident_string()
                            {
                                match x.data {
                                    DefPathData::ValueNs(_) => process_fn_id(
                                        sess,
                                        tcx,
                                        &def_id,
                                        krate_num,
                                        &mut extern_funcs,
                                    ),
                                    DefPathData::Ctor => {
                                        // Some weird constructor inside std crashes so we disable them for std
                                        if &original_crate_name.to_ident_string() != "core" {
                                            let export_sig = tcx.fn_sig(def_id);
                                            let sig = match translate_polyfnsig(
                                                tcx,
                                                &export_sig,
                                                &HashMap::new(),
                                            ) {
                                                Ok(sig) => Ok(sig),
                                                Err(()) => Err(format!("{}", export_sig)),
                                            };
                                            add_array_type_from_ctor_sig(
                                                tcx,
                                                &export_sig,
                                                &mut extern_arrays,
                                            );
                                            let name_segment =
                                                def_path.data[def_path.data.len() - 2];
                                            match name_segment.data {
                                                DefPathData::TypeNs(name) => {
                                                    let fn_key = FnKey::Independent(
                                                        Ident::Original(name.to_ident_string()),
                                                    );
                                                    extern_funcs.insert(fn_key, sig);
                                                }
                                                _ => (),
                                            }
                                        }
                                    }
                                    _ => (),
                                }
                            }
                        }
                        _ => (),
                    }
                }
            }
        }
    }
    let items = &tcx.hir_crate(LOCAL_CRATE).items;
    for (item_id, item) in items {
        let item_id = tcx.hir().local_def_id(*item_id).to_def_id();
        match item.kind {
            ItemKind::Fn(_, _, _) => {
                process_fn_id(sess, tcx, &item_id, &LOCAL_CRATE, &mut extern_funcs)
            }
            ItemKind::Impl { items, .. } => {
                for item in items {
                    let item_id = tcx.hir().local_def_id(item.id.hir_id).to_def_id();
                    if let AssocItemKind::Fn { .. } = item.kind {
                        process_fn_id(sess, tcx, &item_id, &LOCAL_CRATE, &mut extern_funcs)
                    }
                }
            }
            _ => (),
        }
    }
    (extern_funcs, extern_arrays)
}
