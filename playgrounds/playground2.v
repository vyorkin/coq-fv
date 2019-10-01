From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.

Set Implicit Arguments.

Module Playground2.
  Section Symmetric_Conjunction_Disjunction.
    Lemma andb_sym : forall A B : bool, A && B -> B && A.
    Proof.
      case.
        by case.
      by [].
    Qed.

    Lemma andb_sym' : forall A B : bool, A && B -> B && A.
    Proof.
      by case; case.
      Undo 1.
      (* If there were 10 boolean variables instead of 2,
         one could write do 10! case. *)
      by do 2! case.
    Qed.
  End Symmetric_Conjunction_Disjunction.
End Playground2.
