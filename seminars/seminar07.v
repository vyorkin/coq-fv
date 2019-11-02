From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Projection using phantoms.
    Implement [swap'] definition and [swap] notation
    so that the following works: *)

(** Strictly no pattern-matching! *)

Definition swap'' A B (a : A) (b : B)
           & phantom (A * B) (a, b) :=
  (b, a).

Definition swap'
           (A : Type) (B : Type) (a : A) (b : B)
           (_ : phantom (A * B) (a, b)) : (B * A) :=
  (b, a).

Notation "'swap' p" :=
  (@swap' _ _ _ _ (Phantom _ p)) (at level 60).

(** Usage: *)
Eval hnf in swap (true || false, 41 + 1).
(**
= (41 + 1, true || false)
 *)


(** Design a unification tool so that the following
    typechecks iff X and Y can be unified *)

About Logic.eq.
About Logic.eq_refl.

Definition unify (A : Type) (x _ : A) :=
  @Logic.eq_refl A x : @Logic.eq A x x.

Notation "[unify X 'with' Y ]" := (erefl : X=Y) (at level 60).

(** Usage: *)
Check [unify 1 with 0 + 1].
Check [unify 1 with 1 + 0].
Check (fun n : nat => [unify 0 + n with n]).
Fail Check (fun n : nat => [unify n + 0 with n]).  (** this should fail *)

Section LHS.
(** Design a tool for extracting the left-hand side expression
    from a term proving an equation *)

(* Notation "[LHS 'of' proof_of_equation ]" := *)

Variable prf_eq : true && false = false.
(* Eval cbv zeta in [LHS of prf_eq]. *)
(** The desired result = true && false *)

End LHS.
