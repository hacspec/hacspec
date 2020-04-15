use hacspec_examples::p256::*;

#[test]
fn test_gmac() {
    let sk = Scalar::from_hex("14");
    let point_expected = (
        FieldElement::from_hex("83A01A9378395BAB9BCD6A0AD03CC56D56E6B19250465A94A234DC4C6B28DA9A"),
        FieldElement::from_hex("76E49B6DE2F73234AE6A5EB9D612B75C9F2202BB6923F54FF8240AAA86F640B8"),
    );

    let point_computed = point_mul(sk);
    assert_eq!(point_computed, point_expected);

    let sk = Scalar::from_hex("018ebbb95eed0e13");
    let point_expected = (
        FieldElement::from_hex("339150844EC15234807FE862A86BE77977DBFB3AE3D96F4C22795513AEAAB82F"),
        FieldElement::from_hex("B1C14DDFDC8EC1B2583F51E85A5EB3A155840F2034730E9B5ADA38B674336A21"),
    );

    let point_computed = point_mul(sk);
    assert_eq!(point_computed, point_expected);

    let sk = Scalar::from_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550");
    let point_expected = (
        FieldElement::from_hex("6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296"),
        FieldElement::from_hex("B01CBD1C01E58065711814B583F061E9D431CCA994CEA1313449BF97C840AE0A"),
    );

    let point_computed = point_mul(sk);
    assert_eq!(point_computed, point_expected);
}
