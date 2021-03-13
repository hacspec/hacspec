// A module that for the formatting code needed by TLS 1.3
use crate::tls13crypto::*;

// Import hacspec and all needed definitions.
use hacspec_lib::*;

bytes!(Bytes1, 1);
bytes!(Bytes2, 2);
bytes!(Bytes3, 3);
bytes!(Bytes4, 4);
bytes!(Bytes5, 5);
bytes!(Bytes6, 6);
bytes!(Bytes7, 7);
bytes!(Bytes8, 8);
bytes!(Bytes9, 9);
bytes!(Bytes10, 10);
bytes!(Bytes11, 11);
bytes!(Bytes12, 12);

pub fn bytes1(x:u8) -> Bytes {bytes(&Bytes1([U8(x)]))}
pub fn bytes2(x:u8,y:u8) -> Bytes {bytes(&Bytes2([U8(x),U8(y)]))}

pub const label_iv: Bytes2 = Bytes2(secret_bytes!([105, 118]));
pub const label_key: Bytes3 = Bytes3(secret_bytes!([107, 101, 121]));
pub const label_tls13: Bytes6 = Bytes6(secret_bytes!([116, 108, 115, 049, 051, 032]));
pub const label_derived: Bytes7 = Bytes7(secret_bytes!([100, 101, 114, 105, 118, 101, 100]));
pub const label_finished: Bytes8 = Bytes8(secret_bytes!([102, 105, 110, 105, 115, 104, 101, 100]));
pub const label_res_binder: Bytes10 = Bytes10(secret_bytes!([
    114, 101, 115, 032, 098, 105, 110, 100, 101, 114
]));
pub const label_ext_binder: Bytes10 = Bytes10(secret_bytes!([
    101, 120, 116, 032, 098, 105, 110, 100, 101, 114
]));
pub const label_exp_master: Bytes10 = Bytes10(secret_bytes!([
    101, 120, 112, 032, 109, 097, 115, 116, 101, 114
]));
pub const label_res_master: Bytes10 = Bytes10(secret_bytes!([
    114, 101, 115, 032, 109, 097, 115, 116, 101, 114
]));
pub const label_c_e_traffic: Bytes11 = Bytes11(secret_bytes!([
    099, 032, 101, 032, 116, 114, 097, 102, 102, 105, 099
]));
pub const label_e_exp_master: Bytes12 = Bytes12(secret_bytes!([
    101, 032, 101, 120, 112, 032, 109, 097, 115, 116, 101, 114
]));
pub const label_c_hs_traffic: Bytes12 = Bytes12(secret_bytes!([
    099, 032, 104, 115, 032, 116, 114, 097, 102, 102, 105, 099
]));
pub const label_s_hs_traffic: Bytes12 = Bytes12(secret_bytes!([
    115, 032, 104, 115, 032, 116, 114, 097, 102, 102, 105, 099
]));
pub const label_c_ap_traffic: Bytes12 = Bytes12(secret_bytes!([
    099, 032, 097, 112, 032, 116, 114, 097, 102, 102, 105, 099
]));
pub const label_s_ap_traffic: Bytes12 = Bytes12(secret_bytes!([
    115, 032, 097, 112, 032, 116, 114, 097, 102, 102, 105, 099
]));

pub const incorrect_state: usize = 0;
pub const mac_failed: usize = 1;
pub const verify_failed: usize = 2;
pub const zero_rtt_disabled: usize = 3;
pub const not_zero_rtt_sender: usize = 4;
pub const payload_too_long: usize = 5;
pub const psk_mode_mismatch: usize = 6;
pub const negotiation_mismatch: usize = 7;
pub const unsupported_algorithm: usize = 8;
pub const parse_failed: usize = 9;

pub fn lbytes1(b: &Bytes) -> Res<Bytes> {
    let len = b.len();
    if len >= 256 {
        return Err(payload_too_long);
    } else {
        let mut lenb = Seq::new(1);
        lenb[0] = U8(len as u8);
        return Ok(lenb.concat(b));
    }
}

pub fn lbytes2(b: &Bytes) -> Res<Bytes> {
    let len = b.len();
    if len >= 65536 {
        return Err(payload_too_long);
    } else {
        let len : u16 = len as u16;
        let lenb = Seq::from_seq(&U16_to_be_bytes(U16(len)));
        return Ok(lenb.concat(b));
    }
}

pub fn lbytes3(b: &Bytes) -> Res<Bytes> {
    let len = b.len();
    if len >= 16777216 {
        Err(payload_too_long)
    } else {
        let lenb = U32_to_be_bytes(U32(len as u32));
        Ok(lenb.slice_range(1..4).concat(b))
    }
}


#[derive(Clone, Copy, PartialEq)]
pub struct ALGS(
    pub HashAlgorithm,
    pub AEADAlgorithm,
    pub SignatureScheme,
    pub NamedGroup,
    pub bool,
    pub bool,
);

pub fn ciphersuite(algs:ALGS) -> Res<Bytes> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    match (ha,ae) {
        (HashAlgorithm::SHA256,AEADAlgorithm::AES_128_GCM) => Ok(bytes2(0x13,0x01)),
        (HashAlgorithm::SHA256,AEADAlgorithm::CHACHA20_POLY1305) => Ok(bytes2(0x13,0x03)),
        _ => Err(unsupported_algorithm)
    }
}

pub fn supported_group(algs:ALGS) -> Res<Bytes> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    match gn {
        NamedGroup::X25519 => Ok(bytes2(0x00,0x1D)),
        NamedGroup::SECP256r1 => Ok(bytes2(0x00,0x17)),
      //  _ => Err(unsupported_algorithm)
    }
}

pub fn signature_algorithm(algs:ALGS) -> Res<Bytes> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    match sa {
        SignatureScheme::RSA_PSS_RSAE_SHA256 => Ok(bytes2(0x08,0x04)),
        SignatureScheme::ECDSA_SECP256r1_SHA256 => Ok(bytes2(0x04,0x03)),
        _ => Err(unsupported_algorithm)
    }
}


pub fn server_name(sn:&Bytes) -> Res<Bytes> {
    Ok(bytes2(0,0).concat(&lbytes2(&lbytes2(&bytes1(0).concat(&lbytes2(sn)?))?)?))
}

pub fn supported_versions(algs:ALGS) -> Res<Bytes> {
    Ok(bytes2(0,0x2b).concat(&lbytes2(&lbytes1(&bytes2(3,4))?)?))
}

pub fn server_supported_version(algs:ALGS) -> Res<Bytes> {
    Ok(bytes2(0,0x2b).concat(&lbytes2(&bytes2(3,4))?))
}

pub fn supported_groups(algs:ALGS) -> Res<Bytes> {
    Ok(bytes2(0,0x0a).concat(&lbytes2(&lbytes2(&supported_group(algs)?)?)?))
}

pub fn signature_algorithms(algs:ALGS) -> Res<Bytes> {
    Ok(bytes2(0,0x0d).concat(&lbytes2(&lbytes2(&signature_algorithm(algs)?)?)?))
}

pub fn psk_key_exchange_modes(algs:ALGS) -> Res<Bytes> {
    Ok(bytes2(0,0x2d).concat(&lbytes2(&lbytes1(&bytes1(1))?)?))
}

pub fn key_shares(algs:ALGS,gx:DHPK) -> Res<Bytes> {
    let ks = supported_group(algs)?.concat(&lbytes2(&bytes(&gx))?);
    Ok(bytes2(0,0x33).concat(&lbytes2(&lbytes2(&ks)?)?))
}

pub fn pre_shared_key(algs:ALGS,tkt:&Bytes) -> Res<Bytes> {
    let identities = lbytes2(&lbytes2(tkt)?.concat(&U32_to_be_bytes(U32(0xffffffff))))?;
    let binders = lbytes2(&lbytes1(&bytes(&HMAC::new()))?)?;
    Ok(bytes2(0,41).concat(&lbytes2(&identities.concat(&binders))?))
}

pub fn server_pre_shared_key(algs:ALGS) -> Res<Bytes> {
    Ok(bytes2(0,41).concat(&lbytes2(&bytes2(0,0))?))
}

pub fn client_hello(algs:ALGS,cr:Random,gx:DHPK,sn:&Bytes,tkt:Option<&Bytes>) -> Res<Bytes> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let ty = bytes1(1);
    let ver = bytes2(3,3);
    let sid = lbytes1(&Bytes::new(32))?;
    let cip = lbytes2(&ciphersuite(algs)?)?;
    let comp = bytes2(1,0);
    let sn = server_name(sn)?;
    let sv = supported_versions(algs)?;
    let sg = supported_groups(algs)?;
    let sa = signature_algorithms(algs)?;
    let ks = key_shares(algs,gx)?;
    let mut exts = sn.concat(&sv.concat(&sg.concat(&sa.concat(&ks))));
    if psk_mode {
        if let Some(tkt) = tkt {
            let pskm = psk_key_exchange_modes(algs)?;
            let psk = pre_shared_key(algs,tkt)?;
            exts = exts.concat(&pskm.concat(&psk))}
        else {return Err(psk_mode_mismatch)}}
    let ch = ty.concat(&lbytes3(&ver.concat(&cr.concat(&sid.concat(&cip.concat(&comp.concat(&lbytes2(&exts)?))))))?);
    Ok(ch)
}

pub fn server_hello(algs:ALGS,sr:Random,sid:&Bytes,gy:DHPK) -> Res<Bytes> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let ty = bytes1(1);
    let ver = bytes2(3,3);
    let sid = lbytes1(sid)?;
    let cip = ciphersuite(algs)?;
    let comp = bytes1(0);
    let ks = key_shares(algs,gy)?;
    let sv = server_supported_version(algs)?;
    let mut exts = ks.concat(&sv);
    if psk_mode {
        exts = exts.concat(&server_pre_shared_key(algs)?);
    }
    let sh = ty.concat(&lbytes3(&ver.concat(&sr.concat(&sid.concat(&cip.concat(&comp.concat(&lbytes2(&exts)?))))))?);
    Ok(sh)
}

pub fn check_eq(b1:&Bytes,b2:&Bytes) -> Res<()> {
    if b1.len() != b2.len() {Err(parse_failed)}
    else {
        let mut ok = true;
        for i in 0..b1.len(){
            if b1[i].declassify() != b2[i].declassify() {ok = false;}
        }
        if ok {Ok(())} else {Err(parse_failed)}
    }
}

pub fn check_lbytes1(b:&Bytes) -> Res<usize> {
    if b.len() < 1 {Err(parse_failed)}
    else  {
        let l = (b[0] as U8).declassify() as usize;
        if b.len() - 1 < l {Err(parse_failed)}
        else {Ok(b.len() - 1 - l)}
    }
}

pub fn check_lbytes2(b:&Bytes) -> Res<usize> {
    if b.len() < 2 {Err(parse_failed)}
    else  {
        let l0 = (b[0] as U8).declassify() as usize;
        let l1 = (b[1] as U8).declassify() as usize;
        let l = l0 * 256 + l1;
        if b.len() - 2 < l as usize {Err(parse_failed)}
        else {Ok(l)}}
}

pub fn check_lbytes3(b:&Bytes) -> Res<usize> {
    if b.len() < 3 {Err(parse_failed)}
    else  {
        let l0 = (b[0] as U8).declassify() as usize;
        let l1 = (b[1] as U8).declassify() as usize;
        let l2 = (b[2] as U8).declassify() as usize;
        let l = l0 * 65536 + l1 * 256 + l2;
        if b.len() - 3 < l {Err(parse_failed)}
        else {Ok(l)}}
}

pub fn check_lbytes1_full(b:&Bytes) -> Res<()> {
    if check_lbytes1(b)? + 1 != b.len() {Err(parse_failed)}
    else {Ok(())}
}

pub fn check_lbytes2_full(b:&Bytes) -> Res<()> {
    if check_lbytes2(b)? + 2 != b.len() {Err(parse_failed)}
    else {Ok(())}
}

pub fn check_lbytes3_full(b:&Bytes) -> Res<()> {
    if check_lbytes3(b)? + 3 != b.len() {Err(parse_failed)}
    else {Ok(())}
}


pub fn check_ciphersuite(algs:ALGS,ch:&Bytes) -> Res<()> {
    check_eq(&ciphersuite(algs)?,&ch.slice_range(0..2))
}

pub fn check_supported_version(algs:ALGS,ch:&Bytes) -> Res<()> {
    check_lbytes1_full(ch)?;
    check_eq(&bytes2(3,4),&ch.slice_range(1..3))
}

pub fn check_supported_group(algs:ALGS,ch:&Bytes) -> Res<()> {
    check_lbytes2_full(ch)?;
    check_eq(&supported_group(algs)?,&ch.slice_range(2..4))
}

pub fn check_signature_algorithm(algs:ALGS,ch:&Bytes) -> Res<()> {
    check_lbytes2_full(ch)?;
    check_eq(&signature_algorithm(algs)?,&ch.slice_range(2..4))
}

pub fn check_key_share(algs:ALGS,ch:&Bytes) -> Res<()> {
    check_lbytes2_full(ch)?;
    check_eq(&supported_group(algs)?,&ch.slice_range(2..4))?;
    check_lbytes2_full(&ch.slice_range(4..ch.len()))
}

pub fn check_psk_shared_key(algs:ALGS,ch:&Bytes) -> Res<()> {
    let len_id = check_lbytes2(ch)?;
    let len_tkt = check_lbytes2(&ch.slice_range(2..2+len_id))?;
    if len_id == len_tkt + 6 {
        check_lbytes2_full(&ch.slice_range(2+len_id..ch.len()))?;
        check_lbytes1_full(&ch.slice_range(4+len_id..ch.len()))?;
        if ch.len() - 6 - len_id != 32 {Err(parse_failed)}
        else {Ok(())}
    } else {Err(parse_failed)}
}

pub struct Params(Option<usize>,Option<(usize,usize)>,Option<usize>);

pub fn check_extension(algs:ALGS,sn:&Bytes,b:&Bytes,p:Params) -> Res<(usize,Params)> {
    let Params(ks,tkt,binder) = p;
    let l0 = (b[0] as U8).declassify() as usize;
    let l1 = (b[1] as U8).declassify() as usize;
    let len = check_lbytes2(&b.slice_range(2..b.len()))?;
    let mut out = p;
    match (l0,l1) {
        (0,0) => check_eq(&server_name(sn)?,&b.slice_range(0..4+len))?,
        (0,0x2d) => check_eq(&psk_key_exchange_modes(algs)?,&b.slice_range(0..4+len))?,
        (0,0x2b) => check_supported_version(algs,&b.slice_range(4..4+len))?,
        (0,0x0a) => check_supported_group(algs,&b.slice_range(4..4+len))?,
        (0,0x0d) => check_signature_algorithm(algs,&b.slice_range(4..4+len))?,
        (0,0x33) => {
            if let Some(k) = ks {return Err(parse_failed);}
            else {check_key_share(algs,&b.slice_range(4..4+len))?;
                  out = Params(Some(6),tkt,binder);}},
        (0,41) => check_psk_shared_key(algs,&b.slice_range(4..4+len))?,
        _ => ()
    }
    return Ok((4+len,out));
}

pub fn parse_client_hello(algs:ALGS, ch:&Bytes) -> Res<(usize,usize)> {
    let ty = bytes1(1);
    let ver = bytes2(3,3);
    let rand = Bytes::new(32);
    let sid = lbytes1(&Bytes::new(32))?;
    let cip = lbytes2(&ciphersuite(algs)?)?;
    let comp = bytes2(1,0);
    check_eq(&ty,&ch.slice_range(0..1))?;
    check_lbytes3_full(&ch.slice_range(1..ch.len()))?;
    check_eq(&ver,&ch.slice_range(4..6))?;
    let cslen = check_lbytes1(&ch.slice_range(38..ch.len()))?;
    check_ciphersuite(algs,&ch.slice_range(39..39+cslen))?;
    check_eq(&comp,&ch.slice_range(39+cslen..41+cslen))?;
    check_lbytes2_full(&ch.slice_range(41+cslen..ch.len()))?;
    return Ok((6,0))
}