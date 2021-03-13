use crate::tls13crypto::*;
use crate::tls13formats::*;

// Import hacspec and all needed definitions.
use hacspec_lib::*;

/* TLS 1.3 Key Schedule: See RFC 8446 Section 7 */

pub fn hkdf_expand_label(
    ha: HashAlgorithm,
    k: KEY,
    label: Bytes,
    context: &Bytes,
    len: u16,
) -> Res<KEY> {
    let lenb = bytes(&U16_to_be_bytes(U16(len)));
    let tls13_label = label_tls13.concat(&label);
    let info = lenb.concat(&lbytes1(&tls13_label)?).concat(&lbytes1(context)?);
    return hkdf_expand(ha, k, info, len as usize);
}

pub fn derive_secret(ha: HashAlgorithm, k: KEY, label: Bytes, tx: &HASH) -> Res<KEY> {
    return hkdf_expand_label(ha, k, label, &bytes(tx), 32);
}

fn derive_binder_key(ha: HashAlgorithm, k: KEY) -> Res<MACK> {
    let early_secret = hkdf_extract(ha, k, zeros)?;
    let mk = derive_secret(ha, early_secret, bytes(&label_res_binder), &hash_empty(ha))?;
    return Ok(MACK::from_seq(&mk));
}

fn derive_aead_key_iv(ha: HashAlgorithm, k: KEY) -> Res<AEKIV> {
    let sender_write_key = hkdf_expand_label(ha, k, bytes(&label_key), &empty(), 32)?;
    let sender_write_iv = hkdf_expand_label(ha, k, bytes(&label_iv), &empty(), 12)?;
    return Ok((
        AEK::from_seq(&sender_write_key),
        AEIV::from_seq(&sender_write_iv),
    ));
}

fn derive_0rtt_keys(ha: HashAlgorithm, ae: AEADAlgorithm, k: KEY, tx: &HASH) -> Res<(AEKIV, KEY)> {
    let early_secret = hkdf_extract(ha, k, zeros)?;
    let client_early_traffic_secret =
        derive_secret(ha, early_secret, bytes(&label_c_e_traffic), tx)?;
    let early_exporter_master_secret =
        derive_secret(ha, early_secret, bytes(&label_c_e_traffic), tx)?;
    let sender_write_key_iv = derive_aead_key_iv(ha, client_early_traffic_secret)?;
    return Ok((sender_write_key_iv, early_exporter_master_secret));
}

fn derive_finished_key(ha:HashAlgorithm,k:KEY) -> Res<MACK> {
    Ok(MACK::from_seq(&hkdf_expand_label(
        ha,
        k,
        bytes(&label_finished),
        &empty(),
        32,
    )?))
}

fn derive_hk_ms(
    ha: HashAlgorithm,
    ae: AEADAlgorithm,
    gxy: KEY,
    psk: KEY,
    tx: &HASH,
) -> Res<(AEKIV, AEKIV, MACK, MACK, KEY)> {
    let early_secret = hkdf_extract(ha, psk, zeros)?;
    let handshake_secret = hkdf_extract(ha, gxy, early_secret)?;
    let client_handshake_traffic_secret =
        derive_secret(ha, handshake_secret, bytes(&label_c_hs_traffic), tx)?;
    let server_handshake_traffic_secret =
        derive_secret(ha, handshake_secret, bytes(&label_s_hs_traffic), tx)?;
    let client_finished_key = derive_finished_key(ha,client_handshake_traffic_secret)?;
    let server_finished_key = derive_finished_key(ha,server_handshake_traffic_secret)?;
    let client_write_key_iv = derive_aead_key_iv(ha, client_handshake_traffic_secret)?;
    let server_write_key_iv = derive_aead_key_iv(ha, server_handshake_traffic_secret)?;
    let master_secret_ =
        derive_secret(ha, handshake_secret, bytes(&label_derived), &hash_empty(ha))?;
    let master_secret = hkdf_extract(ha, zeros, master_secret_)?;
    return Ok((
        client_write_key_iv,
        server_write_key_iv,
        client_finished_key,
        server_finished_key,
        master_secret,
    ));
}

fn derive_app_keys(
    ha: HashAlgorithm,
    ae: AEADAlgorithm,
    master_secret: KEY,
    tx: &HASH,
) -> Res<(AEKIV, AEKIV, KEY)> {
    let client_application_traffic_secret_0 =
        derive_secret(ha, master_secret, bytes(&label_c_ap_traffic), tx)?;
    let server_application_traffic_secret_0 =
        derive_secret(ha, master_secret, bytes(&label_s_ap_traffic), tx)?;
    let client_write_key_iv = derive_aead_key_iv(ha, client_application_traffic_secret_0)?;
    let server_write_key_iv = derive_aead_key_iv(ha, server_application_traffic_secret_0)?;
    let exporter_master_secret = derive_secret(ha, master_secret, bytes(&label_exp_master), tx)?;
    return Ok((
        client_write_key_iv,
        server_write_key_iv,
        exporter_master_secret,
    ));
}

fn derive_rms(ha: HashAlgorithm, master_secret: KEY, tx: &HASH) -> Res<KEY> {
    let resumption_master_secret = derive_secret(ha, master_secret, bytes(&label_res_master), tx)?;
    return Ok(resumption_master_secret);
}

/* TLS 1.3 Record Layer Encryption: See RFC 8446 Section 5 */

// Using newtype pattern below, but the same thing works with tuples too
struct CipherState(AEADAlgorithm, AEKIV);

fn derive_iv_ctr(iv:AEIV, n:u64) -> AEIV {
    let counter = bytes(&U64_to_be_bytes(U64(n)));
    let mut iv_ctr = iv;
    for i in 0..8 {
        iv_ctr[i + 4] = iv[i + 4] ^ counter[i];
    }
    return iv_ctr;
}
fn encrypt(payload: Bytes, n: u64, st: CipherState) -> Res<Bytes> {
    let CipherState(ae, (k, iv)) = st;
    let iv_ctr = derive_iv_ctr(iv,n);
    let clen = payload.len() + 16;
    if clen <= 65536 {
        let clenb = u16_to_be_bytes(clen as u16);
        let ad = bytes(&Bytes5(secret_bytes!([23, 3, 3, clenb[0], clenb[1]])));
        return aead_encrypt(ae, k, iv_ctr, payload, ad);
    } else {
        return Err(payload_too_long);
    }
}

fn decrypt(ciphertext: Bytes, n: u64, st: CipherState) -> Res<Bytes> {
    let CipherState(ae, (k, iv)) = st;
    let iv_ctr = derive_iv_ctr(iv,n);
    if ciphertext.len() <= 65536 {
        let clenb = u16_to_be_bytes(ciphertext.len() as u16);
        let ad = bytes(&Bytes5(secret_bytes!([23, 3, 3, clenb[0], clenb[1]])));
        return aead_encrypt(ae, k, iv_ctr, ciphertext, ad);
    } else {
        return Err(payload_too_long);
    }
}

/* Handshake State Machine */
/* We implement a simple linear state machine:
PostClientHello -> PostServerHello -> PostCertificateVerify -> PostServerFinished -> PostClientFinished -> PostServerTicket
There are no optional steps, all states must be traversed, even if the traversals are NOOPS */

#[derive(Clone, Copy, PartialEq)]
pub struct ALGS(
    HashAlgorithm,
    AEADAlgorithm,
    SignatureScheme,
    NamedGroup,
    bool,
    bool,
);

struct ClientPostClientHello(Random, ALGS, DHSK, KEY);
struct ClientPostServerHello(Random, Random, ALGS, KEY, MACK, MACK);
struct ClientPostCertificateVerify(Random, Random, ALGS, KEY, MACK, MACK);
struct ClientPostServerFinished(Random, Random, ALGS, KEY, MACK);
struct ClientPostClientFinished(Random, Random, ALGS, KEY);
struct ClientPostServerTicket(Random, Random, ALGS, KEY);

struct ServerPostClientHello(Random, Random, ALGS, KEY, PSK);
struct ServerPostServerHello(Random, Random, ALGS, KEY, MACK, MACK);
struct ServerPostCertificateVerify(Random, Random, ALGS, KEY, MACK, MACK);
struct ServerPostServerFinished(Random, Random, ALGS, KEY, MACK);
struct ServerPostClientFinished(Random, Random, ALGS, KEY);

struct TranscriptTruncatedClientHello(HASH);
struct TranscriptClientHello(HASH);
struct TranscriptServerHello(HASH);
struct TranscriptServerCertificate(HASH);
struct TranscriptServerCertificateVerify(HASH);
struct TranscriptServerFinished(HASH);
struct TranscriptClientFinished(HASH);
/* Handshake Core Functions: See RFC 8446 Section 4 */
/* We delegate all details of message formatting and transcript hashes to the caller */

/* TLS 1.3 Client Side Handshake Functions */

fn get_client_hello(
    algs0: ALGS,
    psk: Option<KEY>,
    ent: Entropy,
) -> Res<(Random, DHPK, ClientPostClientHello)> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs0;
    let cr = Random::from_seq(&ent.slice_range(0..32));
    let x = DHSK::from_seq(&ent.slice_range(32..64));
    let gx = secret_to_public(gn, x)?;
    match psk {
        Some(k) if psk_mode => Ok((cr, gx, ClientPostClientHello(cr, algs0, x, k))),
        None if !psk_mode => Ok((cr, gx, ClientPostClientHello(cr, algs0, x, zeros))),
        _ => Err(psk_mode_mismatch),
    }
}

fn get_client_hello_binder(
    tx: &TranscriptTruncatedClientHello,
    st: ClientPostClientHello,
) -> Res<HMAC> {
    let ClientPostClientHello(cr, algs0, x, psk) = st;
    let TranscriptTruncatedClientHello(tx_hash) = tx;
    if let ALGS(ha, ae, sa, gn, true, zero_rtt) = algs0 {
        let mk = derive_binder_key(ha, psk)?;
        let mac = hmac(ha, mk, &bytes(tx_hash))?;
        Ok(mac)
    } else {
        Err(psk_mode_mismatch)
    }
}

fn client_get_0rtt_keys(
    tx: &TranscriptClientHello,
    st: ClientPostClientHello,
) -> Res<(CipherState, KEY)> {
    let ClientPostClientHello(cr, algs0, x, psk) = st;
    let TranscriptClientHello(tx_hash) = tx;
    if let ALGS(ha, ae, sa, gn, true, true) = algs0 {
        let (aek, key) = derive_0rtt_keys(ha, ae, psk, tx_hash)?;
        Ok((CipherState(ae, aek), key))
    } else {
        Err(zero_rtt_disabled)
    }
}

fn put_server_hello(
    sr: Random,
    gy: DHPK,
    algs: ALGS,
    tx: &TranscriptServerHello,
    st: ClientPostClientHello,
) -> Res<(CipherState, CipherState, ClientPostServerHello)> {
    let ClientPostClientHello(cr, algs0, x, psk) = st;
    let TranscriptServerHello(tx_hash) = tx;
    if algs == algs0 {
        let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
        let gxy = ecdh(gn, x, gy)?;
        let (chk, shk, cfk, sfk, ms) = derive_hk_ms(ha, ae, gxy, psk, tx_hash)?;
        Ok((
            CipherState(ae, chk),
            CipherState(ae, shk),
            ClientPostServerHello(cr, sr, algs, ms, cfk, sfk),
        ))
    } else {
        Err(negotiation_mismatch)
    }
}

fn put_server_signature(
    pk: VERK,
    sig: Bytes,
    tx: &TranscriptServerCertificate,
    st: ClientPostServerHello,
) -> Res<ClientPostCertificateVerify> {
    let ClientPostServerHello(cr, sr, algs, ms, cfk, sfk) = st;
    let TranscriptServerCertificate(tx_hash) = tx;
    if let ALGS(ha, ae, sa, gn, false, zero_rtt) = algs {
        verify(sa, pk, &bytes(tx_hash), sig)?;
        Ok(ClientPostCertificateVerify(cr, sr, algs, ms, cfk, sfk))
    } else {
        Err(psk_mode_mismatch)
    }
}

fn put_skip_server_signature(st: ClientPostServerHello) -> Res<ClientPostCertificateVerify> {
    let ClientPostServerHello(cr, sr, algs, ms, cfk, sfk) = st;
    if let ALGS(ha, ae, sa, gn, true, zero_rtt) = algs {
        Ok(ClientPostCertificateVerify(cr, sr, algs, ms, cfk, sfk))
    } else {
        Err(psk_mode_mismatch)
    }
}

fn put_server_finished(
    vd: HMAC,
    tx: &TranscriptServerCertificateVerify,
    st: ClientPostCertificateVerify,
) -> Res<ClientPostServerFinished> {
    let ClientPostCertificateVerify(cr, sr, algs, ms, cfk, sfk) = st;
    let TranscriptServerCertificateVerify(tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    hmac_verify(ha, sfk, &bytes(tx_hash), vd)?;
    return Ok(ClientPostServerFinished(cr, sr, algs, ms, cfk));
}
fn client_get_1rtt_keys(
    tx: &TranscriptServerFinished,
    st: ClientPostServerFinished,
) -> Res<(CipherState, CipherState, KEY)> {
    let ClientPostServerFinished(_, _, algs, ms, cfk) = st;
    let TranscriptServerFinished(tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let (cak, sak, exp) = derive_app_keys(ha, ae, ms, tx_hash)?;
    return Ok((CipherState(ae, cak), CipherState(ae, sak), exp));
}

fn get_client_finished(
    tx: &TranscriptServerFinished,
    st: ClientPostServerFinished,
) -> Res<(HMAC, ClientPostClientFinished)> {
    let ClientPostServerFinished(cr, sr, algs, ms, cfk) = st;
    let TranscriptServerFinished(tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let m = hmac(ha, cfk, &bytes(tx_hash))?;
    return Ok((m, ClientPostClientFinished(cr, sr, algs, ms)));
}

fn put_server_ticket(
    tx: &TranscriptClientFinished,
    st: ClientPostClientFinished,
) -> Res<ClientPostServerTicket> {
    let ClientPostClientFinished(cr, sr, algs, ms) = st;
    let TranscriptClientFinished(tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let rms = derive_rms(ha, ms, tx_hash)?;
    return Ok(ClientPostServerTicket(cr, sr, algs, rms));
}

/* TLS 1.3 Server Side Handshake Functions */

fn put_client_hello(
    cr: Random,
    algs: ALGS,
    gx: DHPK,
    psk: Option<(PSK, &TranscriptTruncatedClientHello, HMAC)>,
    ent: Entropy,
) -> Res<(Random, DHPK, ServerPostClientHello)> {
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let sr = Random::from_seq(&ent.slice_range(0..32));
    let y = DHSK::from_seq(&ent.slice_range(32..64));
    let gy = secret_to_public(gn, y)?;
    let gxy = ecdh(gn, y, gx)?;
    match psk {
        Some((k, tx, binder)) if psk_mode => {
            let mk = derive_binder_key(ha, k)?;
            let TranscriptTruncatedClientHello(tx_hash) = tx;
            hmac_verify(ha, mk, &bytes(tx_hash), binder)?;
            Ok((sr, gy, ServerPostClientHello(cr, sr, algs, gxy, k)))
        }
        None if !psk_mode => Ok((cr, gx, ServerPostClientHello(cr, sr, algs, gxy, zeros))),
        _ => Err(psk_mode_mismatch),
    }
}

fn server_get_0rtt_keys(
    tx: &TranscriptClientHello,
    st: ServerPostClientHello,
) -> Res<(CipherState, KEY)> {
    let ServerPostClientHello(cr, sr, algs, gxy, psk) = st;
    let TranscriptClientHello(tx_hash) = tx;
    if let ALGS(ha, ae, sa, gn, true, true) = algs {
        let (aek, key) = derive_0rtt_keys(ha, ae, psk, tx_hash)?;
        Ok((CipherState(ae, aek), key))
    } else {
        Err(zero_rtt_disabled)
    }
}

fn get_server_hello(
    tx: &TranscriptClientHello,
    st: ServerPostClientHello,
) -> Res<(CipherState, CipherState, ServerPostServerHello)> {
    let ServerPostClientHello(cr, sr, algs, gxy, psk) = st;
    let TranscriptClientHello(tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let (chk, shk, cfk, sfk, ms) = derive_hk_ms(ha, ae, gxy, psk, tx_hash)?;
    Ok((
        CipherState(ae, shk),
        CipherState(ae, chk),
        ServerPostServerHello(cr, sr, algs, ms, cfk, sfk),
    ))
}

fn get_server_signature(
    sk: SIGK,
    tx: &TranscriptServerCertificate,
    st: ServerPostServerHello,
) -> Res<(SIG, ServerPostCertificateVerify)> {
    let ServerPostServerHello(cr, sr, algs, ms, cfk, sfk) = st;
    let TranscriptServerCertificate(tx_hash) = tx;
    if let ALGS(ha, ae, sa, gn, false, zero_rtt) = algs {
        let sig = sign(sa, sk, &bytes(tx_hash))?;
        Ok((sig, ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk)))
    } else {
        Err(psk_mode_mismatch)
    }
}

fn get_skip_server_signature(st: ServerPostServerHello) -> Res<ServerPostCertificateVerify> {
    let ServerPostServerHello(cr, sr, algs, ms, cfk, sfk) = st;
    if let ALGS(ha, ae, sa, gn, true, zero_rtt) = algs {
        Ok(ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk))
    } else {
        Err(psk_mode_mismatch)
    }
}

fn get_server_finished(
    sk: SIGK,
    tx: &TranscriptServerCertificateVerify,
    st: ServerPostCertificateVerify,
) -> Res<(HMAC, ServerPostServerFinished)> {
    let ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk) = st;
    let TranscriptServerCertificateVerify(tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let m = hmac(ha, sfk, &bytes(tx_hash))?;
    Ok((m, ServerPostServerFinished(cr, sr, algs, ms, cfk)))
}

fn server_get_1rtt_keys(
    tx: &TranscriptServerFinished,
    st: ServerPostServerFinished,
) -> Res<(CipherState, CipherState, KEY)> {
    let ServerPostServerFinished(_, _, algs, ms, cfk) = st;
    let TranscriptServerFinished(tx_hash) = tx;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    let (cak, sak, exp) = derive_app_keys(ha, ae, ms, tx_hash)?;
    return Ok((CipherState(ae, sak), CipherState(ae, cak), exp));
}

fn put_client_finished(
    tx1: &TranscriptServerFinished,
    mac: HMAC,
    tx2: &TranscriptClientFinished,
    st: ServerPostServerFinished,
) -> Res<ServerPostClientFinished> {
    let ServerPostServerFinished(cr, sr, algs, ms, cfk) = st;
    let TranscriptServerFinished(tx_hash1) = tx1;
    let TranscriptClientFinished(tx_hash2) = tx2;
    let ALGS(ha, ae, sa, gn, psk_mode, zero_rtt) = algs;
    hmac_verify(ha, cfk, &bytes(tx_hash1), mac)?;
    let rms = derive_rms(ha, ms, tx_hash2)?;
    return Ok(ServerPostClientFinished(cr, sr, algs, rms));
}
