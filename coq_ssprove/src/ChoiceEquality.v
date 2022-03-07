From Crypt Require Import choice_type Package.
Import PackageNotation.
From Crypt Require Import pkg_interpreter.

Class ChoiceEquality := {
    T :> Type ;
    ct :> choice_type ;
    ChoiceEq : choice.Choice.sort (chElement ct) = T ;
  }.

Global Coercion T : ChoiceEquality >-> Sortclass.
Global Coercion ct : ChoiceEquality >-> choice_type.

Definition ct_T {ce : ChoiceEquality} (x : choice.Choice.sort (@ct ce)) : @T ce :=
  eq_rect (choice.Choice.sort (chElement (@ct ce))) id x (@T ce) ChoiceEq.

Definition T_ct {ce : ChoiceEquality} (x : @T ce) : choice.Choice.sort (@ct ce) :=
  eq_rect_r id x ChoiceEq.

Theorem ct_T_id : forall {ce : ChoiceEquality} t, ct_T (T_ct t) = t.
Proof (fun ce => rew_opp_r id (@ChoiceEq ce)). 

Theorem T_ct_id : forall {ce : ChoiceEquality} t, T_ct (ct_T t) = t.
Proof (fun ce => rew_opp_l id (@ChoiceEq ce)).


Global Coercion ct_T : choice.Choice.sort >-> T.
Global Coercion T_ct : T >-> choice.Choice.sort.

Definition lift_to_code {ce : ChoiceEquality} {L I} (x : @T ce) : code L I (@ct ce) :=
  {code ret (T_ct x)}.

Definition evaluate_code {ce : ChoiceEquality} {L I} (x : code L I (@ct ce)) `{match Run sampler x 0 with Some _ => True | _ => False end} : @T ce.
Proof.
  destruct (Run sampler x 0).
  apply (ct_T s).
  contradiction.
Defined.
