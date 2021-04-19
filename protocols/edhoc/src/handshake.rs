use crate::cryptolib::*;
use crate::formats::*;

// Import hacspec and all needed definitions.
use hacspec_lib::*;

pub struct Transcript_Msg1(pub HashAlgorithm, pub Bytes);
pub struct Transcript_TH_2(pub HashAlgorithm, pub HASH);
pub struct Transcript_TH_3(pub HashAlgorithm, pub HASH);
pub struct Transcript_TH_4(pub HashAlgorithm, pub HASH);

pub struct InitiatorPostMsg1(pub CONNID, pub ALGS, pub KEMSK, pub KEMPK, Transcript_Msg1); //May need Responder Identifier
pub struct ResponderPostMsg2(pub CONNID, pub CONNID, pub ALGS, pub KEMPK, pub KEMPK, pub KEY, pub Transcript_TH_2, pub Bytes); 
pub struct InitiatorComplete(pub CONNID, pub CONNID, pub ALGS, pub KEMPK, pub KEMPK, pub KEY, pub Transcript_TH_4); 
pub struct ResponderComplete(pub CONNID, pub CONNID, pub ALGS, pub KEMPK, pub KEMPK, pub KEY, pub Transcript_TH_4);

pub fn get_msg1(algs:ALGS, corr:usize, c_i:CONNID, ad_1:&Bytes, entropy:Bytes32) -> Res<(Bytes , InitiatorPostMsg1)> {
    let ALGS(method,ha,aea,ss,ks) = algs;
    let sk = KEMSK::from_seq(&entropy);
    let pk = secret_to_public(&ks,&sk)?;
    let msg1 = make_msg1(algs,corr,&c_i,&pk,ad_1)?;
    let th_1 = Transcript_Msg1(ha,empty().concat(&msg1));
    Ok((msg1,InitiatorPostMsg1(c_i,algs,sk,pk,th_1)))
}

pub fn put_msg1(algs:ALGS, c_r:CONNID, id_cred_r:CREDID, cred_r:CRED, ad_2:&Bytes, skR:SIGK, msg1:&Bytes, entropy:Bytes32) -> Res<(Bytes , ResponderPostMsg2)> {
    let ALGS(method,ha,aea,ss,ks) = algs;
    let (corr,c_i,pk_i) = parse_msg1(algs,&msg1)?;
    let sk_r = KEMSK::from_seq(&entropy);
    let pk_r = secret_to_public(&ks,&sk)?;
    let gxy = ecdh(ks, &sk_r, pk_i)?;
    let prk_2e = hkdf_extract(ha,empty(),gxy)?;
    let data_2 = make_data_2(c_i,pk_r,c_r)?;
    let tx = msg1.concat(&data_2);
    let th_2 = Transcript_TH_2(ha,hash(ha,tx)?);
    let prk_2e3m = prk2e; // ASSUMING SIGNATURE KEY
    let aad = make_aad("Encrypt0",id_cred_r,th_2,cred_r,ad_2)?;
    let k2m = edhoc_kdf(ha,prk3e2m,th_2,"K_2m",aead_key_len(aea))?;
    let iv2m = edhoc_kdf(ha,prk3e2m,th_2,"IV_2m",aead_iv_len(aea))?;
    let mac_2 = aead_encrypt(aea,k2m,iv2m,empty(),aad)?;
    let sv = make_sigval("Signature1",id_cred_r,th_2,cred_r,id_2,mac_2)?;
    let sg = sign(ss,skR,sv)?;
    let plaintext = make_plaintext(id_cred_r,sg, ad_2)?;
    let info = get_info(aea,"",th_2,plaintext.len())?;
    let keystream = hkdf_expand(ha,prk_2e,info,plaintext.len())?;
    let ciphertext = plaintext ^ keystream;
    let msg2 = make_msg2(data_2,&ciphertext);
    Ok((msg2,ResponderPostMsg2(c_i,c_r,algs,pk_i,pk_r,prk2e3m,th_2,ciphertext))
}

pub fn put_msg2(st:InitiatorPostMsg1, skI:SIGK, vkR:VERK, msg2:&Bytes) -> Res<(Bytes , InitiatorComplete)> {

    Err(parse_failed)
}

pub fn put_msg3(st:ResponderPostMsg2, vkI:VERK, msg3:&Bytes) -> Res<ResponderComplete> {

    Err(parse_failed)
}
