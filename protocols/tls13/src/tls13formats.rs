// A module that for the formatting code needed by TLS 1.3

// Import hacspec and all needed definitions.
use hacspec_lib::*;

pub type Res<T> = Result<T, usize>;
pub type Bytes = Seq<U8>;

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

pub fn empty() -> Bytes {
    return Seq::new(0);
}

pub fn bytes<T: SeqTrait<U8>>(x: &T) -> Bytes {
    return Seq::from_seq(x);
}