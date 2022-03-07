
Class EqDec (A : Type) :=
  { eqb : A -> A -> bool ;
    eqb_leibniz : forall x y, eqb x y = true <-> x = y }.

Infix "=.?" := eqb (at level 40) : hacspec_scope.
Infix "!=.?" := (fun a b => negb (eqb a b)) (at level 40) : hacspec_scope.

Class Comparable (A : Type) := {
  ltb : A -> A -> bool;
  leb : A -> A -> bool;
  gtb : A -> A -> bool;
  geb : A -> A -> bool;
}.
Infix "<.?" := ltb (at level 42) : hacspec_scope.
Infix "<=.?" := leb (at level 42) : hacspec_scope.
Infix ">.?" := gtb (at level 42) : hacspec_scope.
Infix ">=.?" := geb (at level 42) : hacspec_scope.

Instance eq_dec_lt_Comparable {A : Type} `{EqDec A} (ltb : A -> A -> bool) : Comparable A := {
    ltb := ltb;
    leb a b := if eqb a b then true else ltb a b ;
    gtb a b := ltb b a;
    geb a b := if eqb a b then true else ltb b a;
  }.

Theorem eqb_refl : forall {A} {H : EqDec A} (x : A), @eqb A H x x = true.
Proof.
  intros.
  now apply eqb_leibniz.
Qed.
