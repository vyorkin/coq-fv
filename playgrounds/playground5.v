From mathcomp Require Import ssreflect ssrnat ssrbool prime eqtype.
(* From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq div prime. *)

Structure eqType : Type :=
  Pack {
    sort : Type;
    eq_op : sort -> sort -> bool
  }.

(* Notation "x == y" := (@eq_op _ x y) (default interpretation). *)

(* Inductive eqType  : Type := *)
(*   Pack (sort : Type) of (sort -> sort -> bool). *)
(* Print eqType. *)

Module Explicit.

Inductive eqType : Type :=
  Pack : forall sort : Type, (sort -> sort -> bool) -> eqType.

Definition sort (c : eqType) : Type :=
  match c with
    Pack t _ => t
  end.

Definition eq_op (c : eqType) : sort c -> sort c -> bool :=
  match c with
    Pack _ f => f
  end.
End Explicit.

Definition nat_eqType := Pack nat eqn.

Eval simpl in sort nat_eqType.
Eval simpl in eq_op nat_eqType.
Check (eq_op nat_eqType 3 4).

Definition eqb (a b : bool) := if a then b else ~~ b.
Definition bool_eqType := Pack bool eqb.

(* Error: A left-recursive notation must have an explicit level. *)
Notation "x == y" := (@eq_op _ x y).
(* Notation "x == y" := (@eq_op _ x y) (at level 80, no associativity). *)
