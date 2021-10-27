use hacspec_lib::*;

array!(ArrTyp, 32, u8);

#[derive(Clone, PartialEq)]
pub enum EnumTyp {
    Empty,
    OneArg(ArrTyp),
    TwoArg(ArrTyp, u8),
    ZeroArg(()),
}

#[derive(Clone, PartialEq)]
pub struct Map(pub PublicByteSeq, pub PublicByteSeq); // address = 32 x u8, value = 8 x u8

#[derive(Clone, PartialEq)]
pub struct TupleStructTyp(pub u64, pub EnumTyp, pub Map);

pub fn instance() -> TupleStructTyp {
    TupleStructTyp(
        0_u64,
        EnumTyp::ZeroArg(()),
        Map(PublicByteSeq::new(0_usize), PublicByteSeq::new(0_usize)),
    )
}

#[derive(Clone, PartialEq)]
pub enum MapEntry {
    Entry(u64, Map),
}

fn map_get_entry(m: Map, entry: ArrTyp) -> MapEntry {
    let Map(m0, m1) = m;

    let mut res = MapEntry::Entry(
        0_u64,
        Map(
            m0.clone().concat(&entry),
            m1.clone().concat(&u64_to_be_bytes(0_u64)),
        ),
    );

    for x in 0..m0.clone().len() / 32 {
        if ArrTyp::from_seq(&m0.clone().slice(x * 32, 32)) == entry {
            res = MapEntry::Entry(
                u64_from_be_bytes(u64Word::from_seq(&m1.slice(x * 8, 8))),
                Map(m0.clone(), m1.clone()),
            );
        }
    }

    res
}

pub enum MapUpdate {
    Update(u64, Map),
}

fn map_update_entry(m: Map, entry: ArrTyp, amount: u64) -> MapUpdate {
    let Map(m0, m1) = m;

    let mut res = MapUpdate::Update(
        amount,
        Map(m0.concat(&entry), m1.concat(&u64_to_be_bytes(amount))),
    );

    for x in 0..m0.clone().len() / 32 {
        if ArrTyp::from_seq(&m0.clone().slice(x * 32, 32)) == entry {
            res = MapUpdate::Update(
                amount,
                Map(
                    m0.clone().update(x * 32, &entry),
                    m1.clone().update(x * 8, &u64_to_be_bytes(amount)),
                ),
            );
        }
    }

    res
}

pub fn check_if_max(instance: TupleStructTyp, increase: u64, entry: ArrTyp) -> TupleStructTyp {
    let TupleStructTyp(max, enum_typ, map) = instance;

    let (curr_val, map) = match map_get_entry(map, entry) {
        MapEntry::Entry(curr_val, map) => (curr_val, map),
    };

    let (res_val, map) = match map_update_entry(map, entry, increase + curr_val) {
        MapUpdate::Update(res_val, map) => (res_val, map),
    };

    let enum_typ = match enum_typ.clone() {
        EnumTyp::Empty => EnumTyp::ZeroArg(()),
        EnumTyp::ZeroArg(()) => EnumTyp::OneArg(entry),
        EnumTyp::OneArg(add) => EnumTyp::TwoArg(add, 0_u8),
        EnumTyp::TwoArg(add, i) => EnumTyp::TwoArg(add, i + 1_u8),
    };

    if enum_typ.clone() == EnumTyp::TwoArg(entry, 100_u8) {
        
    };
    
    if TupleStructTyp(increase + res_val, enum_typ.clone(), map.clone()) ==
        TupleStructTyp(max, enum_typ.clone(), map.clone()){
            
    };
    
    if max < increase + res_val {
        TupleStructTyp(increase + res_val, enum_typ, map)
    } else {
        TupleStructTyp(max, enum_typ, map)
    }
}

// TODO: should check for name clash
