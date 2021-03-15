#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(unused_imports)]
#![allow(unused_parens)]

// A module that for the formatting code needed by TLS 1.3
use crate::cryptolib::*;

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
bytes!(Bytes32, 32);

pub fn bytes1(x: u8) -> Bytes {
    bytes(&Bytes1([U8(x)]))
}
pub fn bytes2(x: u8, y: u8) -> Bytes {
    bytes(&Bytes2([U8(x), U8(y)]))
}
pub fn bytes3(x: u8, y: u8, z: u8) -> Bytes {
    bytes(&Bytes3([U8(x), U8(y), U8(z)]))
}
pub fn bytes5(x0: u8, x1: u8, x2:u8, x3:u8, x4:u8) -> Bytes {
    bytes(&Bytes5([U8(x0), U8(x1), U8(x2), U8(x3), U8(x4)]))
}

const sha256_empty : Bytes32 = Bytes32(secret_bytes!([
    0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
    0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55
]));

pub fn hash_empty(ha:&HashAlgorithm) -> Res<HASH> {
   hash(ha, &empty())
   //Ok(HASH::from_seq(&sha256_empty))
}
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
pub const insufficient_entropy: usize = 10;
pub const insufficient_data: usize = 11;

pub fn check_eq(b1: &Bytes, b2: &Bytes) -> Res<()> {
    if b1.len() != b2.len() {
        Err(parse_failed)
    } else {
        let mut ok = true;
        for i in 0..b1.len() {
            if b1[i].declassify() != b2[i].declassify() {
                ok = false;
            }
        }
        if ok {
            Ok(())
        } else {
            Err(parse_failed)
        }
    }
}

pub fn check_mem(b1: &Bytes, b2: &Bytes) -> Res<()> {
    if b2.len() % b1.len() != 0 {
        Err(parse_failed)
    } else {
        for i in 0..(b2.len() / b1.len()) {
            let snip = b2.slice_range(i * b1.len()..(i + 1) * b1.len());
            match check_eq(b1, &snip) {
                Ok(()) => {return(Ok(()));},
                Err(x) => {}
            }
        }
        Ok(())
    }
}

pub fn lbytes1(b: &Bytes) -> Res<Bytes> {
    let len = b.len();
    if len >= 256 {
        Err(payload_too_long)
    } else {
        let mut lenb = Seq::new(1);
        lenb[0] = U8(len as u8);
        Ok(lenb.concat(b))
    }
}

pub fn lbytes2(b: &Bytes) -> Res<Bytes> {
    let len = b.len();
    if len >= 65536 {
        Err(payload_too_long)
    } else {
        let len: u16 = len as u16;
        let lenb = Seq::from_seq(&U16_to_be_bytes(U16(len)));
        Ok(lenb.concat(b))
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

pub fn check_lbytes1(b: &Bytes) -> Res<usize> {
    if b.len() < 1 {
        Err(parse_failed)
    } else {
        let l = (b[0] as U8).declassify() as usize;
        if b.len() - 1 < l {
            Err(parse_failed)
        } else {
            Ok(l)
        }
    }
}

pub fn check_lbytes2(b: &Bytes) -> Res<usize> {
    if b.len() < 2 {
        Err(parse_failed)
    } else {
        let l0 = (b[0] as U8).declassify() as usize;
        let l1 = (b[1] as U8).declassify() as usize;
        let l = l0 * 256 + l1;
        if b.len() - 2 < l as usize {
            Err(parse_failed)
        } else {
            Ok(l)
        }
    }
}

pub fn check_lbytes3(b: &Bytes) -> Res<usize> {
    if b.len() < 3 {
        Err(parse_failed)
    } else {
        let l0 = (b[0] as U8).declassify() as usize;
        let l1 = (b[1] as U8).declassify() as usize;
        let l2 = (b[2] as U8).declassify() as usize;
        let l = l0 * 65536 + l1 * 256 + l2;
        if b.len() - 3 < l {
            Err(parse_failed)
        } else {
            Ok(l)
        }
    }
}

pub fn check_lbytes1_full(b: &Bytes) -> Res<()> {
    if check_lbytes1(b)? + 1 != b.len() {
        Err(parse_failed)
    } else {
        Ok(())
    }
}

pub fn check_lbytes2_full(b: &Bytes) -> Res<()> {
    if check_lbytes2(b)? + 2 != b.len() {
        Err(parse_failed)
    } else {
        Ok(())
    }
}

pub fn check_lbytes3_full(b: &Bytes) -> Res<()> {
    if check_lbytes3(b)? + 3 != b.len() {
        Err(parse_failed)
    } else {
        Ok(())
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


pub fn ciphersuite(algs:&ALGS) -> Res<Bytes> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    match (ha, ae) {
        (HashAlgorithm::SHA256, AEADAlgorithm::AES_128_GCM) => Ok(bytes2(0x13, 0x01)),
        (HashAlgorithm::SHA256, AEADAlgorithm::CHACHA20_POLY1305) => Ok(bytes2(0x13, 0x03)),
        _ => Err(unsupported_algorithm),
    }
}

pub fn supported_group(algs: &ALGS) -> Res<Bytes> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    match gn {
        NamedGroup::X25519 => Ok(bytes2(0x00, 0x1D)),
        NamedGroup::SECP256r1 => Ok(bytes2(0x00, 0x17)),
        //  _ => Err(unsupported_algorithm)
    }
}

pub fn signature_algorithm(algs: &ALGS) -> Res<Bytes> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    match sa {
        SignatureScheme::RSA_PSS_RSAE_SHA256 => Ok(bytes2(0x08, 0x04)),
        SignatureScheme::ECDSA_SECP256r1_SHA256 => Ok(bytes2(0x04, 0x03)),
        _ => Err(unsupported_algorithm),
    }
}

pub fn check_ciphersuites(algs: &ALGS, b: &Bytes) -> Res<usize> {
    let len = check_lbytes2(b)?;
    let cs = ciphersuite(algs)?;
    let csl = b.slice_range(2..2 + len);
    check_mem(&cs, &csl)?;
    Ok(len + 2)
}

pub fn server_name(sn: &Bytes) -> Res<Bytes> {
    Ok(bytes2(0, 0).concat(&lbytes2(&lbytes2(&bytes1(0).concat(&lbytes2(sn)?))?)?))
}

pub fn check_server_name(ext: &Bytes) -> Res<Bytes> {
    check_lbytes2_full(ext)?;
    check_eq(&bytes1(0), &ext.slice_range(2..3))?;
    check_lbytes2_full(&ext.slice_range(3..ext.len()))?;
    Ok(ext.slice_range(5..ext.len()))
}

pub fn supported_versions(algs: &ALGS) -> Res<Bytes> {
    Ok(bytes2(0, 0x2b).concat(&lbytes2(&lbytes1(&bytes2(3, 4))?)?))
}

pub fn check_supported_versions(algs: &ALGS, ch: &Bytes) -> Res<()> {
    check_lbytes1_full(ch)?;
    check_mem(&bytes2(3, 4), &ch.slice_range(1..ch.len()))
}

pub fn server_supported_version(algs: &ALGS) -> Res<Bytes> {
    Ok(bytes2(0, 0x2b).concat(&lbytes2(&bytes2(3, 4))?))
}

pub fn check_server_supported_version(algs: &ALGS, b: &Bytes) -> Res<()> {
    check_eq(&bytes2(3, 4), b)
}

pub fn supported_groups(algs: &ALGS) -> Res<Bytes> {
    Ok(bytes2(0, 0x0a).concat(&lbytes2(&lbytes2(&supported_group(algs)?)?)?))
}

pub fn check_supported_groups(algs: &ALGS, ch: &Bytes) -> Res<()> {
    check_lbytes2_full(ch)?;
    check_mem(&supported_group(algs)?, &ch.slice_range(2..ch.len()))
}

pub fn signature_algorithms(algs: &ALGS) -> Res<Bytes> {
    Ok(bytes2(0, 0x0d).concat(&lbytes2(&lbytes2(&signature_algorithm(algs)?)?)?))
}

pub fn check_signature_algorithms(algs: &ALGS, ch: &Bytes) -> Res<()> {
    check_lbytes2_full(ch)?;
    check_mem(&signature_algorithm(algs)?, &ch.slice_range(2..ch.len()))
}

pub fn psk_key_exchange_modes(algs: &ALGS) -> Res<Bytes> {
    Ok(bytes2(0, 0x2d).concat(&lbytes2(&lbytes1(&bytes1(1))?)?))
}

pub fn check_psk_key_exchange_modes(algs: &ALGS, ch: &Bytes) -> Res<()> {
    check_lbytes1_full(ch)?;
    check_eq(&bytes1(1), &ch.slice_range(1..2))
}

pub fn key_shares(algs: &ALGS, gx: &DHPK) -> Res<Bytes> {
    let ks = supported_group(algs)?.concat(&lbytes2(&bytes(gx))?);
    Ok(bytes2(0, 0x33).concat(&lbytes2(&lbytes2(&ks)?)?))
}

pub fn check_key_share(algs: &ALGS, ch: &Bytes) -> Res<Bytes> {
    check_lbytes2_full(ch)?;
    check_eq(&supported_group(algs)?, &ch.slice_range(2..4))?;
    check_lbytes2_full(&ch.slice_range(4..ch.len()))?;
    Ok(ch.slice_range(6..ch.len()))
}

pub fn server_key_shares(algs: &ALGS, gx: &DHPK) -> Res<Bytes> {
    let ks = supported_group(algs)?.concat(&lbytes2(&bytes(gx))?);
    Ok(bytes2(0, 0x33).concat(&lbytes2(&ks)?))
}

pub fn check_server_key_share(algs: &ALGS, b: &Bytes) -> Res<Bytes> {
    check_eq(&supported_group(algs)?, &b.slice_range(0..2))?;
    check_lbytes2_full(&b.slice_range(2..b.len()))?;
    Ok(b.slice_range(4..b.len()))
}

pub fn pre_shared_key(algs: &ALGS, tkt: &Bytes) -> Res<(Bytes,usize)> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let identities = lbytes2(&lbytes2(tkt)?.concat(&U32_to_be_bytes(U32(0xffffffff))))?;
    let binders = lbytes2(&lbytes1(&zero_key(ha))?)?;
    let ext = bytes2(0, 41).concat(&lbytes2(&identities.concat(&binders))?);
    Ok((ext,binders.len()))
}

pub fn check_psk_shared_key(algs: &ALGS, ch: &Bytes) -> Res<()> {
    let len_id = check_lbytes2(ch)?;
    let len_tkt = check_lbytes2(&ch.slice_range(2..2 + len_id))?;
    if len_id == len_tkt + 6 {
        check_lbytes2_full(&ch.slice_range(2 + len_id..ch.len()))?;
        check_lbytes1_full(&ch.slice_range(4 + len_id..ch.len()))?;
        if ch.len() - 6 - len_id != 32 {
            Err(parse_failed)
        } else {
            Ok(())
        }
    } else {
        Err(parse_failed)
    }
}

pub fn server_pre_shared_key(algs: &ALGS) -> Res<Bytes> {
    Ok(bytes2(0, 41).concat(&lbytes2(&bytes2(0, 0))?))
}

pub fn check_server_psk_shared_key(algs: &ALGS, b: &Bytes) -> Res<()> {
    check_eq(&bytes2(0, 0), &b)
}

pub struct EXTS(pub Option<Bytes>, pub Option<Bytes>, pub Option<Bytes>, pub Option<Bytes>);

pub fn merge_opts<T>(o1: Option<T>, o2: Option<T>) -> Res<Option<T>> {
    match (o1, o2) {
        (None, Some(o)) => Ok(Some(o)),
        (Some(o), None) => Ok(Some(o)),
        (None,None) => Ok(None),
        _ => Err(parse_failed),
    }
}
pub fn merge_exts(e1: EXTS, e2: EXTS) -> Res<EXTS> {
    let EXTS(sn1, ks1, tkt1, bd1) = e1;
    let EXTS(sn2, ks2, tkt2, bd2) = e2;
    Ok(EXTS(
        merge_opts(sn1, sn2)?,
        merge_opts(ks1, ks2)?,
        merge_opts(tkt1, tkt2)?,
        merge_opts(bd1, bd2)?,
    ))
}

pub fn check_extension(algs: &ALGS, b: &Bytes) -> Res<(usize, EXTS)> {
    let l0 = (b[0] as U8).declassify() as usize;
    let l1 = (b[1] as U8).declassify() as usize;
    let len = check_lbytes2(&b.slice_range(2..b.len()))?;
    let mut out = EXTS(None, None, None, None);
    match (l0, l1) {
        (0, 0) => {
            let sn = check_server_name(&b.slice_range(4..4 + len))?;
            out = EXTS(Some(sn), None, None, None)
        }
        (0, 0x2d) => check_psk_key_exchange_modes(algs, &b.slice_range(4..4 + len))?,
        (0, 0x2b) => check_supported_versions(algs, &b.slice_range(4..4 + len))?,
        (0, 0x0a) => check_supported_groups(algs, &b.slice_range(4..4 + len))?,
        (0, 0x0d) => check_signature_algorithms(algs, &b.slice_range(4..4 + len))?,
        (0, 0x33) => {
            let gx = check_key_share(algs, &b.slice_range(4..4 + len))?;
            out = EXTS(None, Some(gx), None, None)
        }
        (0, 41) => check_psk_shared_key(algs, &b.slice_range(4..4 + len))?,
        _ => (),
    }
    Ok((4 + len, out))
}

pub fn check_server_extension(algs: &ALGS, b: &Bytes) -> Res<(usize, Option<Bytes>)> {
    let l0 = (b[0] as U8).declassify() as usize;
    let l1 = (b[1] as U8).declassify() as usize;
    let len = check_lbytes2(&b.slice_range(2..b.len()))?;
    let mut out = None;
    match (l0, l1) {
        (0, 0x2b) => check_server_supported_version(algs, &b.slice_range(4..4 + len))?,
        (0, 0x33) => {
            let gx = check_server_key_share(algs, &b.slice_range(4..4 + len))?;
            out = Some(gx)
        }
        (0, 41) => check_server_psk_shared_key(algs, &b.slice_range(4..4 + len))?,
        _ => (),
    }
    Ok((4 + len, out))
}

pub fn check_extensions(algs: &ALGS, b: &Bytes) -> Res<EXTS> {
    let (len, out) = check_extension(algs, b)?;
    if len == b.len() {
        Ok(out)
    } else {
        let out_rest = check_extensions(algs, &b.slice_range(len..b.len()))?;
        merge_exts(out, out_rest)
    }
}

pub fn check_server_extensions(algs: &ALGS, b: &Bytes) -> Res<Option<Bytes>> {
    let (len, out) = check_server_extension(algs, b)?;
    if len == b.len() {
        Ok(out)
    } else {
        let out_rest = check_server_extensions(algs, &b.slice_range(len..b.len()))?;
        merge_opts(out, out_rest)
    }
}

pub fn client_hello(
    algs: &ALGS,
    cr: &Random,
    gx: &DHPK,
    sn: &Bytes,
    tkt:&Option<Bytes>,
) -> Res<(Bytes,usize)> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let ty = bytes1(1);
    let ver = bytes2(3, 3);
    let sid = lbytes1(&Bytes::new(32))?;
    let cip = lbytes2(&ciphersuite(algs)?)?;
    let comp = bytes2(1, 0);
    let sn = server_name(sn)?;
    let sv = supported_versions(algs)?;
    let sg = supported_groups(algs)?;
    let sa = signature_algorithms(algs)?;
    let ks = key_shares(algs, gx)?;
    let mut exts = sn.concat(&sv).concat(&sg).concat(&sa).concat(&ks);
    let mut trunc_len = 0;
    match (psk_mode,tkt) {
        (true, Some(tkt)) => {
            let pskm = psk_key_exchange_modes(algs)?;
            let (psk,len) = pre_shared_key(algs, tkt)?;
            exts = exts.concat(&pskm).concat(&psk);
            trunc_len = len;
            },
        (false,None) => {},
        _ => {return Err(psk_mode_mismatch)
        }
    }
    
    let ch = ty.concat(&lbytes3(
        &ver.concat(cr)
            .concat(&sid)
            .concat(&cip)
            .concat(&comp)
            .concat(&lbytes2(&exts)?),
    )?);
    Ok((ch,trunc_len))
}

pub fn set_client_hello_binder(algs: &ALGS, binder:&Option<HMAC>, ch:Bytes) -> Res<Bytes> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let chlen = &ch.len();
    match binder {
        Some(m) => Ok(ch.update_slice(chlen-hash_len(ha),m,0,hash_len(ha))),
        None => Ok(ch),
    }
} 

pub fn parse_client_hello(algs: &ALGS, ch: &Bytes) -> Res<(Random, Bytes, Bytes, Bytes, Option<Bytes>, Option<Bytes> ,usize)> {
    let ty = bytes1(1);
    let ver = bytes2(3, 3);
    let comp = bytes2(1, 0);
    let mut next = 0;
    check_eq(&ty, &ch.slice_range(next..next + 1))?;
    next = 1;
    check_lbytes3_full(&ch.slice_range(next..ch.len()))?;
    next = next + 3;
    check_eq(&ver, &ch.slice_range(next..next + 2))?;
    next = next + 2;
    let crand = ch.slice_range(next..next + 32);
    next = next + 32;
    let sidlen = check_lbytes1(&ch.slice_range(next..ch.len()))?;
    let sid = ch.slice_range(next+1..next+1+sidlen);
    next = next + 1 + sidlen;
    let cslen = check_ciphersuites(algs, &ch.slice_range(next..ch.len()))?;
    next = next + cslen;
    check_eq(&comp, &ch.slice_range(next..next + 2))?;
    next = next + 2;
    check_lbytes2_full(&ch.slice_range(next..ch.len()))?;
    next = next + 2;
    let exts = check_extensions(algs, &ch.slice_range(next..ch.len()))?;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let trunc_len = ch.len() - hash_len(ha) - 3;
    match (psk_mode,exts) {
        (true,EXTS(Some(sn),Some(gx),Some(tkt),Some(binder))) =>
            Ok((Random::from_seq(&crand),sid,sn,gx,Some(tkt),Some(binder),trunc_len)),
        (false,EXTS(Some(sn),Some(gx),None,None)) =>
            Ok((Random::from_seq(&crand),sid,sn,gx,None,None,0)),
        _ => Err(parse_failed)
    }

}

pub fn server_hello(algs: &ALGS, sr: &Random, sid: &Bytes, gy: &DHPK) -> Res<Bytes> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let ty = bytes1(2);
    let ver = bytes2(3, 3);
    let sid = lbytes1(sid)?;
    let cip = ciphersuite(algs)?;
    let comp = bytes1(0);
    let ks = server_key_shares(algs, gy)?;
    let sv = server_supported_version(algs)?;
    let mut exts = ks.concat(&sv);
    match psk_mode {
        true => exts = exts.concat(&server_pre_shared_key(algs)?),
        false => {}
    }
    let sh = ty.concat(&lbytes3(
        &ver.concat(sr)
            .concat(&sid)
            .concat(&cip)
            .concat(&comp)
            .concat(&lbytes2(&exts)?),
    )?);
    Ok(sh)
}

pub fn parse_server_hello(algs: &ALGS, sh: &Bytes) -> Res<(Random, DHPK)> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let ty = bytes1(2);
    let ver = bytes2(3, 3);
    let cip = ciphersuite(algs)?;
    let comp = bytes1(0);
    let mut next = 0;
    check_eq(&ty, &sh.slice_range(next..next + 1))?;
    next = 1;
    check_lbytes3_full(&sh.slice_range(next..sh.len()))?;
    next = next + 3;
    check_eq(&ver, &sh.slice_range(next..next + 2))?;
    next = next + 2;
    let srand = sh.slice_range(next..next + 32);
    next = next + 32;
    let sidlen = check_lbytes1(&sh.slice_range(next..sh.len()))?;
    next = next + 1 + sidlen;
    check_eq(&cip, &sh.slice_range(next..next + 2))?;
    next = next + 2;
    check_eq(&comp, &sh.slice_range(next..next + 1))?;
    next = next + 1;
    check_lbytes2_full(&sh.slice_range(next..sh.len()))?;
    next = next + 2;
    let gy = check_server_extensions(algs, &sh.slice_range(next..sh.len()))?;
    if let Some(gy) = gy {Ok((Random::from_seq(&srand), gy))}
    else {Err(unsupported_algorithm)}
}

pub fn encrypted_extensions(algs: &ALGS) -> Res<Bytes> {
    let ty = bytes1(8);
    Ok(ty.concat(&lbytes3(&empty())?))
}

pub fn parse_encrypted_extensions(algs: &ALGS, ee: &Bytes) -> Res<()> {
    let ty = bytes1(8);
    check_eq(&ty, &ee.slice_range(0..1))?;
    check_lbytes3_full(&ee.slice_range(1..ee.len()))
}

pub fn server_certificate(algs: &ALGS, cert: &Bytes) -> Res<Bytes> {
    let ty = bytes1(0x0b);
    let creq = lbytes1(&empty())?;
    let crt = lbytes3(cert)?;
    let ext = lbytes2(&empty())?;
    let crts = lbytes3(&crt.concat(&ext))?;
    Ok(ty.concat(&creq).concat(&crts))
}

pub fn parse_server_certificate(algs: &ALGS, sc: &Bytes) -> Res<Bytes> {
    let ty = bytes1(0x0b);
    check_eq(&ty, &sc.slice_range(0..1))?;
    let mut next = 1;
    check_lbytes3_full(&sc.slice_range(next..sc.len()))?;
    next = 4;
    let creqlen = check_lbytes1(&sc.slice_range(4..sc.len()))?;
    next = next + 1 + creqlen;
    check_lbytes3_full(&sc.slice_range(next..sc.len()))?;
    next = next + 3;
    let crtlen = check_lbytes3(&sc.slice_range(next..sc.len()))?;
    next = next + 3;
    let crt = sc.slice_range(next..next + crtlen);
    next = next + crtlen;
    let extlen = check_lbytes2(&sc.slice_range(next..sc.len()))?;
    Ok(crt)
}

pub fn certificate_verify(algs: &ALGS, cv: &Bytes) -> Res<Bytes> {
    let ty = bytes1(0x0f);
    let sig = signature_algorithm(algs)?.concat(&lbytes2(cv)?);
    Ok(ty.concat(&lbytes3(&sig)?))
}

pub fn parse_certificate_verify(algs: &ALGS, cv: &Bytes) -> Res<Bytes> {
    let ty = bytes1(0x0f);
    check_eq(&ty, &cv.slice_range(0..1))?;
    check_lbytes3_full(&cv.slice_range(1..cv.len()))?;
    check_eq(&signature_algorithm(algs)?, &cv.slice_range(4..6))?;
    check_lbytes2_full(&cv.slice_range(6..cv.len()))?;
    Ok(cv.slice_range(8..cv.len()))
}

pub fn finished(algs: &ALGS, vd: &Bytes) -> Res<Bytes> {
    let ty = bytes1(0x14);
    Ok(ty.concat(&lbytes3(vd)?))
}

pub fn parse_finished(algs: &ALGS, fin: &Bytes) -> Res<Bytes> {
    let ty = bytes1(0x14);
    check_eq(&ty, &fin.slice_range(0..1))?;
    check_lbytes3_full(&fin.slice_range(1..fin.len()))?;
    Ok(fin.slice_range(4..fin.len()))
}

pub fn session_ticket(algs: &ALGS, tkt: &Bytes) -> Res<Bytes> {
    let ty = bytes1(0x04);
    let lifetime = U32_to_be_bytes(U32(172800));
    let age = U32_to_be_bytes(U32(9999));
    let nonce = lbytes1(&bytes1(1))?;
    let stkt = lbytes2(&tkt)?;
    let grease_ext = bytes2(0x5a, 0x5a).concat(&lbytes2(&empty())?);
    let ext = lbytes2(&grease_ext)?;
    Ok(ty.concat(&lbytes3(
        &lifetime
            .concat(&age)
            .concat(&nonce)
            .concat(&stkt)
            .concat(&grease_ext),
    )?))
}

pub fn parse_session_ticket(algs: &ALGS, tkt: &Bytes) -> Res<(U32, Bytes)> {
    let ty = bytes1(0x0f);
    check_eq(&ty, &tkt.slice_range(0..1))?;
    check_lbytes3_full(&tkt.slice_range(1..tkt.len()))?;
    let lifetime = U32_from_be_bytes(U32Word::from_seq(&tkt.slice_range(4..8)));
    let age = U32_from_be_bytes(U32Word::from_seq(&tkt.slice_range(8..12)));
    let nonce_len = check_lbytes1(&tkt.slice_range(12..tkt.len()))?;
    let stkt_len = check_lbytes2(&tkt.slice_range(13 + nonce_len..tkt.len()))?;
    let stkt = tkt.slice_range(15 + nonce_len..15 + nonce_len + stkt_len);
    check_lbytes2_full(&tkt.slice_range(15 + nonce_len + stkt_len..tkt.len()))?;
    Ok((lifetime + age, stkt))
}
