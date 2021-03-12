mod tls13crypto;
use tls13crypto::*;

// Import hacspec and all needed definitions.
use hacspec_lib::*;

pub fn hkdf_expand_label(
    ha: HashAlgorithm,
    k: KEY,
    label: String,
    context: Bytes,
    len: usize,
) -> Res<KEY> {
    return Ok(k);
}

pub fn derive_secret(ha: HashAlgorithm, k: KEY, label: String, context: Bytes) -> Res<KEY> {
    return Ok(k);
}
fn derive_binder_key(psk: PSK) -> MACK {
    return MACK::new();
}

fn derive_0rtt_keys(psk: PSK, ch: Bytes, ae_alg: AEADAlgorithm) -> (AEK, KEY) {
    return (AEK::new(), KEY::new());
}

fn derive_app_keys(
    hash_alg: HashAlgorithm,
    ae_alg: AEADAlgorithm,
    ms: KEY,
    log: Bytes,
) -> (AEK, AEK, KEY) {
    return (AEK::new(), AEK::new(), KEY::new());
}

fn derive_rms(ha: HashAlgorithm, ms: KEY, log: Bytes) -> KEY {
    return KEY::new();
}

fn derive_hk_ms(
    x: DH_KEYPAIR,
    psk: PSK,
    gy: DHPK,
    algs: ALGS,
    log: Bytes,
) -> (AEK, AEK, MACK, MACK, KEY) {
    return (AEK::new(), AEK::new(), MACK::new(), MACK::new(), KEY::new());
}


// Using newtype pattern below, but the same thing works with tuples too
struct CipherState(AEADAlgorithm,AEK);

fn encrypt(msg: Bytes, ad: Bytes, n: u64, st: CipherState) -> Res<Bytes> {
    return Ok(msg);
}

fn decrypt(msg: Bytes, ad: Bytes, n: u64, st: CipherState) -> Res<Bytes> {
    return Ok(msg);
}

struct ClientPostClientHello(Random, DH_KEYPAIR, PSK, Option<AEADAlgorithm>);
struct ClientPostClientHelloBinder(Random, DH_KEYPAIR, PSK, Option<AEADAlgorithm>);
struct ClientPostServerHello(Random, Random, ALGS, KEY, MACK, MACK);
struct ClientPostCertificateVerify(Random, Random, ALGS, KEY, MACK, MACK);
struct ClientPostServerFinished(Random, Random, ALGS, KEY, MACK);
struct ClientPostClientFinished(Random, Random, ALGS, KEY);
struct ClientPostServerTicket(Random, Random, ALGS, KEY);

struct ServerPostClientHello(Random, Random, DH_KEYPAIR, DHPK, PSK, Option<AEADAlgorithm>);
struct ServerPostServerHello(Random, Random, ALGS, KEY, MACK, MACK);
struct ServerPostCertificateVerify(Random, Random, ALGS, KEY, MACK, MACK);
struct ServerPostServerFinished(Random, Random, ALGS, KEY, MACK);
struct ServerPostClientFinished(Random, Random, ALGS, KEY);

static incorrect_state: usize = 0;
static mac_failed: usize = 1;
static verify_failed: usize = 2;
static zero_rtt_disabled: usize = 3;
static not_zero_rtt_sender: usize = 4;

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

fn get_client_hello_binder(truncated_ch: Bytes, st: ClientPostClientHello) -> Res<HMAC> {
    let ClientPostClientHello(cr, _, (ha, psk), _) = st;
    let mk = derive_binder_key((ha, psk));
    let mac = hmac(ha, mk, truncated_ch)?;
    Ok(mac)
}

fn client_get_0rtt_keys(ch: Bytes, st: ClientPostClientHello) -> Res<(CipherState,KEY)> {
    match st {
        ClientPostClientHello(cr, _, psk, Some(ae_alg)) => {
            let (aek, key) = derive_0rtt_keys(psk, ch, ae_alg);
            return Ok((CipherState(ae_alg, aek), key));
        }
        _ => return Err(zero_rtt_disabled),
    }
}

fn put_server_hello(
    sr: Random,
    gy: DHPK,
    algs: ALGS,
    log: Bytes,
    st: ClientPostClientHello,
) -> Res<(CipherState, CipherState, ClientPostServerHello)> {
    let ClientPostClientHello(cr, kp, psk, _) = st;
    let (chk, shk, cfk, sfk, ms) = derive_hk_ms(kp, psk, gy, algs, log);
    let (ha, ae, sa) = algs;
    Ok((
        CipherState(ae, chk),
        CipherState(ae, shk),
        ClientPostServerHello(cr, sr, algs, ms, cfk, sfk),
    ))
}

fn put_server_signature(
    pk: VERK,
    log: Bytes,
    sig: Bytes,
    st: ClientPostServerHello,
) -> Res<ClientPostCertificateVerify> {
    let ClientPostServerHello(cr, sr, algs, ms, cfk, sfk) = st;
    let (ha, ae, sa) = algs;
    verify(sa, pk, log, sig)?;
    return Ok(ClientPostCertificateVerify(cr, sr, algs, ms, cfk, sfk));
}

fn put_server_finished(
    log: Bytes,
    vd: HMAC,
    st: ClientPostCertificateVerify,
) -> Res<ClientPostServerFinished> {
    let ClientPostCertificateVerify(cr, sr, algs, ms, cfk, sfk) = st;
    let (ha, ae, sa) = algs;
    hmac_verify(ha, sfk, log, vd)?;
    return Ok(ClientPostServerFinished(cr, sr, algs, ms, cfk));
}
fn client_get_1rtt_keys(log: Bytes, st: ClientPostServerFinished) -> Res<(CipherState,CipherState,KEY)> {
    let ClientPostServerFinished(_, _, algs, ms, cfk) = st;
    let (ha, ae, sa) = algs;
    let (cak, sak, exp) = derive_app_keys(ha, ae, ms, log);
    return Ok((CipherState(ae, cak), CipherState(ae,sak), exp));
}

fn get_client_finished(
    log: Bytes,
    st: ClientPostServerFinished,
) -> Res<(HMAC, ClientPostClientFinished)> {
    let ClientPostServerFinished(cr, sr, algs, ms, cfk) = st;
    let (ha, ae, sig) = algs;
    let m = hmac(ha, cfk, log)?;
    return Ok((m, ClientPostClientFinished(cr, sr, algs, ms)));
}

fn put_server_ticket(log: Bytes, st: ClientPostClientFinished) -> Res<ClientPostServerTicket> {
    let ClientPostClientFinished(cr, sr, algs, ms) = st;
    let (ha, ae, sa) = algs;
    let rms = derive_rms(ha, ms, log);
    return Ok(ClientPostServerTicket(cr, sr, algs, rms));
}

fn put_client_hello(
    cr: Random,
    gn: NamedGroup,
    gx: DHPK,
    psk: PSK,
    truncated_ch: Bytes,
    binder: HMAC,
    zerortt: Option<AEADAlgorithm>,
    ent: Entropy,
) -> Res<(Random, DHPK, ServerPostClientHello)> {
    let sr = Random::from_seq(&ent.slice_range(0..32));
    let y = DHSK::from_seq(&ent.slice_range(32..64));
    let gy = secret_to_public(gn, y)?;
    let (ha, psk) = psk;
    let mk = derive_binder_key((ha, psk));
    hmac_verify(ha, mk, truncated_ch, binder)?;
    return Ok((
        sr,
        gy,
        ServerPostClientHello(cr, sr, (gn, y, gy), gx, (ha, psk), zerortt),
    ));
}

fn server_get_0rtt_keys(ch: Bytes, st: ServerPostClientHello) -> Res<(CipherState,KEY)> {
    if let ServerPostClientHello(_, _, _, _, psk, Some(ae_alg)) = st {
        let (aek, key) = derive_0rtt_keys(psk, ch, ae_alg);
        return Ok((CipherState(ae_alg, aek), key));
    } else {
        return Err(zero_rtt_disabled);
    }
}

fn get_server_hello(
    algs: ALGS,
    log: Bytes,
    st: ServerPostClientHello,
) -> Res<(CipherState, CipherState, ServerPostServerHello)> {
    let ServerPostClientHello(cr, sr, kp, gx, psk, zerortt) = st;
    let (chk, shk, cfk, sfk, ms) = derive_hk_ms(kp, psk, gx, algs, log);
    let (ha, ae, sa) = algs;
    Ok((
        CipherState(ae, shk), CipherState(ae, chk),
        ServerPostServerHello(cr, sr, algs, ms, cfk, sfk),
    ))
}

fn get_server_signature(
    sk: SIGK,
    log: Bytes,
    st: ServerPostServerHello,
) -> Res<(SIG, ServerPostCertificateVerify)> {
    let ServerPostServerHello(cr, sr, algs, ms, cfk, sfk) = st;
    let (ha, ae, sa) = algs;
    let sig = sign(sa, sk, log)?;
    Ok((sig, ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk)))
}

fn get_server_finished(
    sk: SIGK,
    log: Bytes,
    st: ServerPostCertificateVerify,
) -> Res<(HMAC, ServerPostServerFinished)> {
    let ServerPostCertificateVerify(cr, sr, algs, ms, cfk, sfk) = st;
    let (ha, ae, sa) = algs;
    let m = hmac(ha, sfk, log)?;
    Ok((m, ServerPostServerFinished(cr, sr, algs, ms, cfk)))
}

fn server_get_1rtt_keys(log: Bytes, st: ServerPostServerFinished) -> Res<(CipherState,CipherState,KEY)> {
    let ServerPostServerFinished(_, _, algs, ms, cfk) = st;
    let (ha, ae, sa) = algs;
    let (cak, sak, exp) = derive_app_keys(ha, ae, ms, log);
    return Ok((CipherState(ae, sak), CipherState(ae,cak), exp));
}

fn put_client_finished(
    log1: Bytes,
    mac: HMAC,
    log2: Bytes,
    st: ServerPostServerFinished,
) -> Res<ServerPostClientFinished> {
    let ServerPostServerFinished(cr, sr, algs, ms, cfk) = st;
    let (ha, ae, sa) = algs;
    hmac_verify(ha, cfk, log1, mac)?;
    let rms = derive_rms(ha, ms, log2);
    return Ok(ServerPostClientFinished(cr, sr, algs, rms));
}
