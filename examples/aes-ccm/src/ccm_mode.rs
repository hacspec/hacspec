use hacspec_lib::*;
use hacspec_aes::*;

fn format_func(a: &ByteSeq, n: &ByteSeq, p: &ByteSeq, t: u8, alen: u64, nlen: u8, plen: u64) -> ByteSeq {
    let mut r = 0;
    let mut tmp = 10;

    if alen < 0x800000 {
        tmp = 2;
    } else if alen < 0x100000000 {
        tmp = 6;
    }

    r = r + ((tmp+alen+15)/16)+((plen+15)/16); // ceiling operation used
    let mut b = ByteSeq::new((16*(r+1)) as usize);

    // creation of b(0)
    let qlen: u8 = 15 - nlen;
    let mut flags: u8 = 0;

    if alen > 0 {
        flags = 0x40;
    }

    flags = flags | (((t-2)/2) << 3);
    flags = flags | (qlen-1);
    b[0] = U8(flags);

    for i in 0..nlen {
        let tmp2 = n.get_exact_chunk(1, i.into());
        b = b.set_exact_chunk(1, (i+1).into(), &tmp2);
    }

    let andy: u64 = 255; // 0xFF
    let mut copy: u64 = plen;

    for i in (16-qlen..16).rev() {
        let smth = ByteSeq::from_public_slice(&[(copy & andy) as u8]);
        b = b.set_exact_chunk(1, i.into(), &smth);
        copy = copy >> 8;
    }

    // creation of b(1) to b(u)
    let x: u8 = 0xff;
    let y: u8 = 0xfe;

    let mut k = 16; // byte number to set next
    let mut copy2 = alen;

    if alen >= 0x800000 {
        b[16] = U8(x);
        k = k + 2;

        if alen < 0x100000000 {
            b[17] = U8(y);
        } else {
            b[17] = U8(x);
        }
    }

    for i in (k..k+tmp).rev() {
        let smth2 = ByteSeq::from_public_slice(&[(copy2 & andy) as u8]);
        b = b.set_exact_chunk(1, i as usize, &smth2);
        copy2 = copy2 >> 8;
    }

    k = k + tmp;

    for i in 0..alen {
        let tmp2 = a.get_exact_chunk(1, i as usize);
        b = b.set_exact_chunk(1, (i+k) as usize, &tmp2);
    }

    k = k + alen;

    for _t in 0..16 {
        if k % 16 != 0 {
            // add zero padding for Associated Data
            b[k as usize] = U8(0x0);
            k = k + 1;
        }
    }

    // creation of b(u+1) to b(r)
    for i in 0..plen {
        let tmp2 = p.get_exact_chunk(1, i as usize);
        b = b.set_exact_chunk(1, (i+k) as usize, &tmp2);
    }

    k = k + plen;

    for _t in 0..16 {
        if k % 16 != 0 {
            // add zero padding for Payload
            b[k as usize] = U8(0x0);
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

fn counter_func(n: &ByteSeq, nlen: u8, m: u64) -> ByteSeq {
    let qlen: u8 = 15 - nlen;
    let flag = qlen - 1;
    let mut ctr = ByteSeq::new((16 * (m+1)) as usize);
    let high: u64 = 255; // 0xFF

    for i in 0..m+1 {
        let k = 16 * i;
        ctr[k as usize] = U8(flag);

        for j in 0..nlen.into() {
            let tmp2 = n.get_exact_chunk(1, j as usize);
            ctr = ctr.set_exact_chunk(1, (k+j+1) as usize, &tmp2);
        }

        let mut icopy = i;
        let ncopy: u64 = nlen.into();

        for x in (k+ncopy+1..k+16).rev() {
            let curr = ByteSeq::from_public_slice(&[(icopy & high) as u8]);
            ctr = ctr.set_exact_chunk(1, x as usize, &curr);
            icopy = icopy >> 8;
        }
    }

    ctr
}

fn ctr_cipher(ctr: &ByteSeq, key: Key128, m: u64) -> (ByteSeq, ByteSeq) {
    let ctr_zero = Block::from_seq(&ctr.get_exact_chunk(16, 0));
    let s0 = ByteSeq::from_seq(&aes128_encrypt_block(key, ctr_zero));
    let mut s = ByteSeq::new((16*m) as usize);

    for i in 1..m+1 {
        let ctr_block = Block::from_seq(&ctr.get_exact_chunk(16, i as usize));
        let s_curr = aes128_encrypt_block(key, ctr_block);
        let seq_s = ByteSeq::from_seq(&s_curr);
        s = s.set_exact_chunk(16, (i-1) as usize, &seq_s);
    }

    (s0, s)
}

pub fn encrypt_ccm(a: ByteSeq, n: ByteSeq, pay: ByteSeq, key: Key128, tlen: u8, alen: u64, nlen: u8, plen: u64) -> ByteSeq {
    let b = format_func(&a, &n, &pay, tlen, alen, nlen, plen); // step 1
    let t = get_t(&b, key, tlen.into()); // steps 2 to 4

    let m = (plen+15)/16; // round up
    let counter = counter_func(&n, nlen, m.into());
    let (s0, s) = ctr_cipher(&counter, key, m.into());

    let cipherlen = t.len()+pay.len(); let pl = pay.len();
    let mut ciphertext = ByteSeq::new(cipherlen);

    let pay_xor = pay ^ s.get_exact_chunk(plen as usize, 0);
    ciphertext = ciphertext.set_exact_chunk(plen as usize, 0, &pay_xor);

    let t_xor = t ^ s0.get_exact_chunk(tlen.into(), 0);

    for i in pl..cipherlen {
        let curr_chunk = t_xor.get_exact_chunk(1, i-pl);
        ciphertext = ciphertext.set_exact_chunk(1, i, &curr_chunk);
    }

    ciphertext
}

pub fn decrypt_ccm(adata: ByteSeq, nonce: ByteSeq, ciph: ByteSeq, clen: u8, key: Key128, tlen: u8, nlen: u8) -> ByteSeq {
    if clen > tlen {
        let m = (clen-tlen+15) / 16;
        let counter = counter_func(&nonce, nlen.into(), m.into());
        let (s0, s) = ctr_cipher(&counter, key, m.into());

        let x = clen - tlen;
        let p = ciph.get_exact_chunk(x.into(), 0) ^ s.get_exact_chunk(x.into(), 0);
        p
    } else {
        ByteSeq::new(0) // TODO: Return "Invalid" instead
    }
}
