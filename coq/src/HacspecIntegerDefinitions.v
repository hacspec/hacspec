From Coq Require Import ZArith List.

Inductive ints := U8
             | U16
             | U32
             | U64
             | U128.

Definition wordsize {i} :=
  match i with
  | U8 => 8
  | U16 => 16
  | U32 => 32
  | U64 => 64
  | U128 => 128
  end.
Definition modulus {i : ints} : Z := two_power_nat (@wordsize i).
Definition max_unsigned {i : ints} : Z := @modulus i - 1.

Class WS (T : Type) : Type := {
    translate : ints -> T ;
    ws_wordsize : T -> nat ;
    wordsize_eq : forall (i : ints), ws_wordsize (translate i) = @wordsize i ;

    ws_modulus : T -> Z ;
    modulus_eq : forall (i : ints), ws_modulus (translate i) = @modulus i ;

    ws_max_unsigned : T -> Z ;
    max_unsigned_eq : forall (i : ints), ws_max_unsigned (translate i) = @max_unsigned i ;
  }.

Class Integer (i : ints) {word_type} `{ws : WS word_type} :=
  {
    IntType : word_type -> Type ;
    T : Type := IntType (translate i) ;
    repr : Z -> T ;
    unsigned : T -> Z ;
    signed : T -> Z ;

    rotate_left : forall (s u : T), T ;
    rotate_right : forall (s u : T), T ;

    add_int : forall (s u : T), T ;
    sub_int : forall (s u : T), T ;
    neg_int : forall (s : T), T  ;
    mul_int : forall (s u : T), T  ;
    divs_int : forall (s u : T), T  ;
    mods_int : forall (s u : T), T  ;
    xor_int : forall (s u : T), T ;
    and_int : forall (s u : T), T ;
    or_int : forall (s u : T), T ;

    not : forall (s : T), T  ;
    
    eq_int : forall (s u : T), bool ;
    lt_int : forall (s u : T), bool ;

    shl_int : forall (s u : T), T ;
    shr_int : forall (s u : T), T ;

    zero : T ;
    one : T ;

    unsigned_repr : forall z, (0 <= z <= @max_unsigned i)%Z -> unsigned (repr z) = z ;
    repr_unsigned : forall x, repr (unsigned x) = x ;
    unsigned_range : forall x, (0 <= unsigned x < @modulus i)%Z ;

    add_unsigned : forall x y, add_int x y = repr (unsigned x + unsigned y) ;
    add_commut : forall x y , add_int x y = add_int y x ;
    add_assoc: forall x y z, add_int (add_int x y) z = add_int x (add_int y z) ;

    zero_is_repr_zero : repr (0%Z) = zero ;
    add_zero_l : forall n, add_int zero n = n ;

    unsigned_one : unsigned one = 1%Z ;

    eq_leibniz_int : forall x y, eq_int x y = true <-> x = y ;
  }.
Definition IntegerType `(Integer) : Type := T.

Global Infix "%%" := Z.rem (at level 40, left associativity) : Z_scope.
Global Infix ".+" := add_int (at level 77) : hacspec_scope.
Global Infix ".-" := sub_int (at level 77) : hacspec_scope.
Global Notation "-" := neg_int (at level 77) : hacspec_scope.
Global Infix ".*" := mul_int (at level 77) : hacspec_scope.
Global Infix "./" := divs_int (at level 77) : hacspec_scope.
Global Infix ".%" := mods_int (at level 77) : hacspec_scope.
Global Infix ".^" := xor_int (at level 77) : hacspec_scope.
Global Infix ".&" := and_int (at level 77) : hacspec_scope.
Global Infix ".|" := or_int (at level 77) : hacspec_scope.
Global Infix "==" := eq_int (at level 32) : hacspec_scope.
