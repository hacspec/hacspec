use hacspec_lib::*;
use hacspec_aes::*;

pub type AesCcmResult = Result<ByteSeq, u8>;
pub const INVALID: u8 = 0u8;

fn format_func(a: &ByteSeq, n: &ByteSeq, p: &ByteSeq, t: usize, alen: usize, nlen: usize, plen: usize) -> ByteSeq {
    let mut r = 0;
    let mut a_octets = 0;
    let mut flags: u8 = 0u8;

    if alen > 0 {
        flags = 0x40u8;

        if alen < 0x800000 {
            a_octets = 2;
        } else {
            if alen < 0x100000000 {
                a_octets = 6;
            } else {
                a_octets = 10;
            }
        }
    }

    r = r + ((a_octets+alen+15)/16)+((plen+15)/16); // ceiling operation used
    let mut b = ByteSeq::new(16 * (r + 1));

    // creation of b(0)
    let qlen: u8 = 15u8 - (nlen as u8);

    flags = flags | ((t as u8-2u8)/2u8) << 3;
    flags = flags | (qlen-1u8);
    b[0] = U8(flags);

    for i in 0..nlen {
        b[i+1] = n[i];
    }

    let mut plen_copy = plen;

    for i in 1..(qlen as usize)+1 {
        let curr = (plen_copy & 0xFF) as u8;
        b[16-i] = U8(curr);
        plen_copy = plen_copy >> 8;
    }

    // creation of b(1) to b(u)
    let mut k: usize = 16; // byte number to set next

    if a_octets > 0 {
        let x = 0xffu8;
        let y = 0xfeu8;
        let mut alen_copy = alen;

        if alen >= 0x800000 {
            b[16] = U8(x);
            k = k + 2;

            if alen < 0x100000000 {
                b[17] = U8(y);
            } else {
                b[17] = U8(x);
            }
        }

        for i in 1..a_octets+1 {
            let curr = (alen_copy & 0xFF) as u8;
            b[k + a_octets - i] = U8(curr);
            alen_copy = alen_copy >> 8;
        }

        k = k + a_octets;

        for i in 0..alen {
            b[i+k]= a[i];
        }

        k = k + alen;

        for _t in 0..16 {
            if k % 16 != 0 {
                // add zero padding for Associated Data
                b[k] = U8(0u8);
                k = k + 1;
            }
        }
    }

    // creation of b(u+1) to b(r)
    for i in 0..plen {
        b[i+k] = p[i];
    }

    k = k + plen;

    for _t in 0..16 {
        if k % 16 != 0 {
            // add zero padding for Payload
            b[k] = U8(0u8);
            k = k + 1;
        }
    }

    b
}

fn get_t(b: &ByteSeq, key: Key128, num: usize) -> ByteSeq {
    let b0 = b.get_exact_chunk(16, 0);
    let bloc = Block::from_seq(&b0);
    let mut y_curr = aes128_encrypt_block(key, bloc);

    for i in 1..b.len()/16 {
        let mut b_curr = Block::from_seq(&b.get_exact_chunk(16, i));
        b_curr = y_curr ^ b_curr;
        y_curr = aes128_encrypt_block(key, b_curr);
    }

    ByteSeq::from_seq(&(y_curr.slice(0, num)))
}

fn counter_func(n: &ByteSeq, nlen: usize, m: usize) -> ByteSeq {
    let mut ctr = ByteSeq::new(16 * (m + 1));
    let qlen: u8 = 15u8 - (nlen as u8);
    let flag = qlen - 1u8;

    for i in 0..m+1 {
        let mut icopy = i as u64;

        let k = 16 * i;
        ctr[k] = U8(flag);

        for j in 0..nlen {
            ctr[k+j+1] = n[j];
        }

        for x in 1..15-nlen {
            let curr = icopy & 0xFFu64;
            ctr[k+16-x] = U8(curr as u8);
            icopy = icopy >> 8;
        }
    }

    ctr
}

fn ctr_cipher(ctr: &ByteSeq, key: Key128, m: usize) -> (ByteSeq, ByteSeq) {
    let ctr_zero = Block::from_seq(&ctr.get_exact_chunk(16, 0));
    let key_copy = key.clone();
    let s0 = ByteSeq::from_seq(&aes128_encrypt_block(key, ctr_zero));
    let mut s = ByteSeq::new(16 * m);

    for i in 1..m+1 {
        let new_copy = key_copy.clone();
        let ctr_block = Block::from_seq(&ctr.get_exact_chunk(16, i));
        let s_curr = aes128_encrypt_block(new_copy, ctr_block);
        let seq_s = ByteSeq::from_seq(&s_curr);
        s = s.set_exact_chunk(16, i-1, &seq_s);
    }

    (s0, s)
}

pub fn encrypt_ccm(a: ByteSeq, n: ByteSeq, pay: ByteSeq, key: Key128, tlen: usize) -> ByteSeq {
    let key_copy = key.clone();
    let plen = pay.len();
    let alen = a.len();
    let nlen = n.len();

    let b = format_func(&a, &n, &pay, tlen, alen, nlen, plen); // step 1
    let t = get_t(&b, key, tlen); // steps 2 to 4

    let m = (plen + 15) / 16; // round up
    let counter = counter_func(&n, nlen, m);
    let (s0, s) = ctr_cipher(&counter, key_copy, m);

    let cipherlen = tlen + plen;
    let mut ciphertext = ByteSeq::new(cipherlen);

    let pay_xor = pay ^ s.get_exact_chunk(plen, 0);
    ciphertext = ciphertext.set_exact_chunk(plen, 0, &pay_xor);
    let t_xor = t ^ s0.get_exact_chunk(tlen, 0);

    for i in plen..cipherlen {
        ciphertext[i] = t_xor[i-plen];
    }

    ciphertext
}

pub fn decrypt_ccm(adata: ByteSeq, nonce: ByteSeq, key: Key128, ciph: ByteSeq, clen: usize, tlen: usize) -> AesCcmResult {
    if clen > tlen {
        let m = (clen - tlen + 15) / 16;
        let counter = counter_func(&nonce, nonce.len(), m);
        let (s0, s) = ctr_cipher(&counter, key, m);

        let p = ciph.get_exact_chunk(clen - tlen, 0) ^ s.get_exact_chunk(clen - tlen, 0);

        let t = ciph.slice_range(clen-tlen..clen) ^ s0.get_exact_chunk(tlen, 0);
        let b = format_func(&adata, &nonce, &p, tlen, adata.len(), nonce.len(), p.len());

        if get_t(&b, key, tlen) == t {
            AesCcmResult::Ok(p)
        } else {
            AesCcmResult::Err(INVALID)
        }
    } else {
        AesCcmResult::Err(INVALID)
    }
}
