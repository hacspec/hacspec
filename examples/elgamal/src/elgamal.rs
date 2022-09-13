use hacspec_lib::*;

public_nat_mod!(
    type_name: ElGamalFieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 256,
    modulo_value: "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed"
);
const alpha : ElGamalFieldElement = 
