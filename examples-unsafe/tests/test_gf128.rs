use hacspec_lib::prelude::*;

use unsafe_hacspec_examples::aes_gcm::gf128::*;

#[test]
fn test_gmac() {
    let msg = ByteSeq::from_hex("feedfacedeadbeeffeedfacedeadbeefabaddad20000000000000000000000005a8def2f0c9e53f1f75d7853659e2a20eeb2b22aafde6419a058ab4f6f746bf40fc0c3b780f244452da3ebf1c5d82cdea2418997200ef82e44ae7e3f");
    let key = Key::from_hex("acbef20579b4b8ebce889bac8732dad7");
    let output = Tag::from_hex("cc9ae9175729a649936e890bd971a8bf");
    let tag = gmac(&msg, key);
    assert!(output.declassify_eq(&tag));
}
