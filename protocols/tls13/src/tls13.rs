mod tls13formats;
use tls13formats::*;
mod tls13crypto;
use tls13crypto::*;

// Import hacspec and all needed definitions.
use hacspec_lib::*;

/* TLS 1.3 - specific crypto code for key schedule */

pub fn hkdf_expand_label(
    ha: HashAlgorithm,
    k: KEY,
    label: Bytes,
    context: &Bytes,
    len: u16,
) -> Res<KEY> {
    let lenb = Seq::from_seq(&U16_to_be_bytes(U16(len)));
    let labelb = label_tls13.concat(&label);
    let info = lenb.concat(&vlbytes1(&labelb)?).concat(&vlbytes1(context)?);
    return hkdf_expand(ha, k, info, len as usize);
}

pub fn derive_secret(ha: HashAlgorithm, k: KEY, label: Bytes, context: &Bytes) -> Res<KEY> {
    return hkdf_expand_label(ha, k, label, context, 32);
}

fn derive_binder_key(ha: HashAlgorithm, k: KEY) -> Res<MACK> {
    let zeros = KEY::new();
    let early_secret = hkdf_extract(ha, k, zeros)?;
    let mk = derive_secret(
        ha,
        early_secret,
        Seq::from_seq(&label_res_binder),
        &Seq::new(0),
    )?;
    return Ok(MACK::from_seq(&mk));
}

fn derive_aead_keyiv(ha: HashAlgorithm, k: KEY) -> Res<AEKIV> {
    let empty = Bytes::new(0);
    let sender_write_key = hkdf_expand_label(ha, k, Seq::from_seq(&label_key), &empty, 32)?;
    let sender_write_iv = hkdf_expand_label(ha, k, Seq::from_seq(&label_iv), &empty, 12)?;
    return Ok((
        AEK::from_seq(&sender_write_key),
        AEIV::from_seq(&sender_write_iv),
    ));
}

fn derive_0rtt_keys(
    ha: HashAlgorithm,
    ae: AEADAlgorithm,
    k: KEY,
    ch_log: &Bytes,
) -> Res<(AEKIV, KEY)> {
    let zeros = KEY::new();
    let early_secret = hkdf_extract(ha, k, zeros)?;
    let client_early_traffic_secret =
        derive_secret(ha, early_secret, Seq::from_seq(&label_c_e_traffic), ch_log)?;
    let early_exporter_master_secret =
        derive_secret(ha, early_secret, Seq::from_seq(&label_c_e_traffic), ch_log)?;
    let sender_write_key_iv = derive_aead_keyiv(ha, client_early_traffic_secret)?;
    return Ok((sender_write_key_iv, early_exporter_master_secret));
}

fn derive_hk_ms(
    ha: HashAlgorithm,
    ae: AEADAlgorithm,
    gxy: KEY,
    psk: KEY,
    log: &Bytes,
) -> Res<(AEKIV, AEKIV, MACK, MACK, KEY)> {
    let zeros = KEY::new();
    let empty = Bytes::new(0);
    let early_secret = hkdf_extract(ha, psk, zeros)?;
    let handshake_secret = hkdf_extract(ha, gxy, early_secret)?;
    let client_handshake_traffic_secret = derive_secret(
        ha,
        handshake_secret,
        Seq::from_seq(&label_c_hs_traffic),
        log,
    )?;
    let server_handshake_traffic_secret = derive_secret(
        ha,
        handshake_secret,
        Seq::from_seq(&label_s_hs_traffic),
        log,
    )?;
    let client_finished_key = MACK::from_seq(&hkdf_expand_label(
        ha,
        client_handshake_traffic_secret,
        Seq::from_seq(&label_finished),
        &empty,
        32,
    )?);
    let server_finished_key = MACK::from_seq(&hkdf_expand_label(
        ha,
        server_handshake_traffic_secret,
        Seq::from_seq(&label_finished),
        &empty,
        32,
    )?);
    let client_write_key_iv = derive_aead_keyiv(ha, client_handshake_traffic_secret)?;
    let server_write_key_iv = derive_aead_keyiv(ha, server_handshake_traffic_secret)?;
    let master_secret_ =
        derive_secret(ha, handshake_secret, Seq::from_seq(&label_derived), &empty)?;
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
    log: &Bytes,
) -> Res<(AEKIV, AEKIV, KEY)> {
    let client_application_traffic_secret_0 =
        derive_secret(ha, master_secret, Seq::from_seq(&label_c_ap_traffic), log)?;
    let server_application_traffic_secret_0 =
        derive_secret(ha, master_secret, Seq::from_seq(&label_s_ap_traffic), log)?;
    let client_write_key_iv = derive_aead_keyiv(ha, client_application_traffic_secret_0)?;
    let server_write_key_iv = derive_aead_keyiv(ha, server_application_traffic_secret_0)?;
    let exporter_master_secret =
        derive_secret(ha, master_secret, Seq::from_seq(&label_exp_master), log)?;
    return Ok((
        client_write_key_iv,
        server_write_key_iv,
        exporter_master_secret,
    ));
}

fn derive_rms(ha: HashAlgorithm, master_secret: KEY, log: &Bytes) -> Res<KEY> {
    let resumption_master_secret =
        derive_secret(ha, master_secret, Seq::from_seq(&label_res_master), log)?;
    return Ok(resumption_master_secret);
}

/* Record Layer Encryption */

// Using newtype pattern below, but the same thing works with tuples too
struct CipherState(AEADAlgorithm, AEKIV);

fn encrypt(msg: Bytes, ad: Bytes, n: u64, st: CipherState) -> Res<Bytes> {
    return Ok(msg);
}

fn decrypt(msg: Bytes, ad: Bytes, n: u64, st: CipherState) -> Res<Bytes> {
    return Ok(msg);
}

/* Handshake State and Core Functions */

struct ClientPostClientHello(Random, DH_KEYPAIR, PSK, Option<AEADAlgorithm>);
struct ClientPostClientHelloBinder(Random, DH_KEYPAIR, PSK, Option<AEADAlgorithm>);
struct ClientPostServerHello(Random, Random, ALGS, KEY, MACK, MACK);
struct ClientPostCertificateVerify(Random, Random, ALGS, KEY, MACK, MACK);
struct ClientPostServerFinished(Random, Random, ALGS, KEY, MACK);
struct ClientPostClientFinished(Random, Random, ALGS, KEY);
struct ClientPostServerTicket(Random, Random, ALGS, KEY);

struct ServerPostClientHello(Random, Random, KEY, PSK, Option<AEADAlgorithm>);
struct ServerPostServerHello(Random, Random, ALGS, KEY, MACK, MACK);
struct ServerPostCertificateVerify(Random, Random, ALGS, KEY, MACK, MACK);
struct ServerPostServerFinished(Random, Random, ALGS, KEY, MACK);
struct ServerPostClientFinished(Random, Random, ALGS, KEY);

fn get_client_hello(
    gn: NamedGroup,
    psk: PSK,
    zerortt: Option<AEADAlgorithm>,
    ent: Entropy,
) -> Res<(Random, DHPK, ClientPostClientHello)> {
    let cr = Random::from_seq(&ent.slice_range(0..32));
    let x = DHSK::from_seq(&ent.slice_range(32..64));
    let gx = secret_to_public(gn, x)?;
    return Ok((cr, gx, ClientPostClientHello(cr, (gn, x, gx), psk, zerortt)));
}

fn get_client_hello_binder(truncated_ch: &Bytes, st: ClientPostClientHello) -> Res<HMAC> {
    let ClientPostClientHello(cr, _, (ha, psk), _) = st;
    let mk = derive_binder_key(ha, psk)?;
    let mac = hmac(ha, mk, truncated_ch)?;
    Ok(mac)
}

fn client_get_0rtt_keys(ch_log: &Bytes, st: ClientPostClientHello) -> Res<(CipherState, KEY)> {
    if let ClientPostClientHello(cr, _, (ha, psk), Some(ae_alg)) = st {
        let (aek, key) = derive_0rtt_keys(ha, ae_alg, psk, ch_log)?;
        return Ok((CipherState(ae_alg, aek), key));
    } else {
        return Err(zero_rtt_disabled);
    }
}

fn put_server_hello(
    sr: Random,
    gy: DHPK,
    algs: ALGS,
    log: &Bytes,
    st: ClientPostClientHello,
) -> Res<(CipherState, CipherState, ClientPostServerHello)> {
    let ClientPostClientHello(cr, (gn, x, gx), (_, psk), _) = st;
    let (ha, ae, sa) = algs;
    let gxy = ecdh(gn, x, gy)?;
    let (chk, shk, cfk, sfk, ms) = derive_hk_ms(ha, ae, gxy, psk, log)?;
    let (ha, ae, sa) = algs;
    Ok((
        CipherState(ae, chk),
        CipherState(ae, shk),
        ClientPostServerHello(cr, sr, algs, ms, cfk, sfk),
    ))
}

fn put_server_signature(
    pk: VERK,
    log: &Bytes,
    sig: Bytes,
    st: ClientPostServerHello,
) -> Res<ClientPostCertificateVerify> {
    let ClientPostServerHello(cr, sr, algs, ms, cfk, sfk) = st;
    let (ha, ae, sa) = algs;
    verify(sa, pk, log, sig)?;
    return Ok(ClientPostCertificateVerify(cr, sr, algs, ms, cfk, sfk));
}

fn put_server_finished(
    log: &Bytes,
    vd: HMAC,
    st: ClientPostCertificateVerify,
) -> Res<ClientPostServerFinished> {
    let ClientPostCertificateVerify(cr, sr, algs, ms, cfk, sfk) = st;
    let (ha, ae, sa) = algs;
    hmac_verify(ha, sfk, log, vd)?;
    return Ok(ClientPostServerFinished(cr, sr, algs, ms, cfk));
}
fn client_get_1rtt_keys(
    log: &Bytes,
    st: ClientPostServerFinished,
) -> Res<(CipherState, CipherState, KEY)> {
    let ClientPostServerFinished(_, _, algs, ms, cfk) = st;
    let (ha, ae, sa) = algs;
    let (cak, sak, exp) = derive_app_keys(ha, ae, ms, log)?;
    return Ok((CipherState(ae, cak), CipherState(ae, sak), exp));
}

fn get_client_finished(
    log: &Bytes,
    st: ClientPostServerFinished,
) -> Res<(HMAC, ClientPostClientFinished)> {
    let ClientPostServerFinished(cr, sr, algs, ms, cfk) = st;
    let (ha, ae, sig) = algs;
    let m = hmac(ha, cfk, log)?;
    return Ok((m, ClientPostClientFinished(cr, sr, algs, ms)));
}

fn put_server_ticket(log: &Bytes, st: ClientPostClientFinished) -> Res<ClientPostServerTicket> {
    let ClientPostClientFinished(cr, sr, algs, ms) = st;
    let (ha, ae, sa) = algs;
    let rms = derive_rms(ha, ms, log)?;
    return Ok(ClientPostServerTicket(cr, sr, algs, rms));
}

fn put_client_hello(
    cr: Random,
    gn: NamedGroup,
    gx: DHPK,
    psk: PSK,
    truncated_ch: &Bytes,
    binder: HMAC,
    zerortt: Option<AEADAlgorithm>,
    ent: Entropy,
) -> Res<(Random, DHPK, ServerPostClientHello)> {
    let sr = Random::from_seq(&ent.slice_range(0..32));
    let y = DHSK::from_seq(&ent.slice_range(32..64));
    let gy = secret_to_public(gn, y)?;
    let gxy = ecdh(gn, y, gx)?;
    let (ha, psk) = psk;
    let mk = derive_binder_key(ha, psk)?;
    hmac_verify(ha, mk, truncated_ch, binder)?;
    return Ok((
        sr,
        gy,
        ServerPostClientHello(cr, sr, gxy, (ha, psk), zerortt),
    ));
}

fn server_get_0rtt_keys(ch_log: &Bytes, st: ServerPostClientHello) -> Res<(CipherState, KEY)> {
    if let ServerPostClientHello(_, _, _, (ha, psk), Some(ae_alg)) = st {
        let (aek, key) = derive_0rtt_keys(ha, ae_alg, psk, ch_log)?;
        return Ok((CipherState(ae_alg, aek), key));
    } else {
        return Err(zero_rtt_disabled);
    }
}

fn get_server_hello(
    algs: ALGS,
    log: &Bytes,
    st: ServerPostClientHello,
) -> Res<(CipherState, CipherState, ServerPostServerHello)> {
    let ServerPostClientHello(cr, sr, gxy, (ha, psk), zerortt) = st;
    let (ha, ae, sa) = algs;
    let (chk, shk, cfk, sfk, ms) = derive_hk_ms(ha, ae, gxy, psk, log)?;
    Ok((
        CipherState(ae, shk),
        CipherState(ae, chk),
        ServerPostServerHello(cr, sr, algs, ms, cfk, sfk),
    ))
}

fn get_server_signature(
    sk: SIGK,
    log: &Bytes,
    st: ServerPostServerHello,
) -> Res<(SIG, ServerPostCertificateVerify)> {
    let ServerPostServerHello(cr, sr, algs, ms, cfk, sfk) = st;
    let (ha, ae, sa) = algs;
    let sig = sign(sa, sk, log)?;
    Ok((sig, ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk)))
}

fn get_server_finished(
    sk: SIGK,
    log: &Bytes,
    st: ServerPostCertificateVerify,
) -> Res<(HMAC, ServerPostServerFinished)> {
    let ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk) = st;
    let (ha, ae, sa) = algs;
    let m = hmac(ha, sfk, log)?;
    Ok((m, ServerPostServerFinished(cr, sr, algs, ms, cfk)))
}

fn server_get_1rtt_keys(
    log: &Bytes,
    st: ServerPostServerFinished,
) -> Res<(CipherState, CipherState, KEY)> {
    let ServerPostServerFinished(_, _, algs, ms, cfk) = st;
    let (ha, ae, sa) = algs;
    let (cak, sak, exp) = derive_app_keys(ha, ae, ms, log)?;
    return Ok((CipherState(ae, sak), CipherState(ae, cak), exp));
}

fn put_client_finished(
    log1: &Bytes,
    mac: HMAC,
    log2: &Bytes,
    st: ServerPostServerFinished,
) -> Res<ServerPostClientFinished> {
    let ServerPostServerFinished(cr, sr, algs, ms, cfk) = st;
    let (ha, ae, sa) = algs;
    hmac_verify(ha, cfk, log1, mac)?;
    let rms = derive_rms(ha, ms, log2)?;
    return Ok(ServerPostClientFinished(cr, sr, algs, rms));
}
