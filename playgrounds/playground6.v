(** Use some very basic facilities of mathcomp library *)
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq div prime ssrfun.

Unset Printing All.
Print rel.
Definition id A (a : A) : A := a.
Check (id nat 3).
Check (id _ 3).

Arguments id {A} a.
Compute @id nat 3.

Check (fun x => @id nat x).

Lemma prime_gt1 p :
  prime p -> 1 < p.
Proof.
Admitted.

(* fun m n : nat => leq_trans (n:=m.+1) (m:=m) (p:=n) (leqnSn m) *)
(*      : forall m n : nat, m < n -> m <= n *)
(* Unset Printing Notations. *)
Lemma example q : prime q -> 0 < q.
Proof.
  move=> pr_q.
  have q_gt1 := @prime_gt1 _ pr_q.
  exact: ltnW q_gt1.
Qed.

(* Для задания неявных аргументов для лемм также используется ключевое слово Arguments. *)
Arguments prime_gt1 {p}.

Lemma example' q : prime q -> 0 < q.
Proof.
  move=> pr_q.
  have q_gt1 := prime_gt1 pr_q.
  exact: ltnW q_gt1.
Qed.

Module induct.
  Inductive eqType : Type :=
    Pack sort of sort -> sort -> bool.

  Definition sort (c : eqType) : Type :=
    let: Pack t _ := c in t.

  Definition eq_op (c : eqType) : sort c -> sort c -> bool :=
    let: Pack _ f := c in f.

  Print eqType.
End induct.


Record eqType : Type := Pack
{
  sort : Type;
  eq_op : sort -> sort -> bool
}.

Check eq_op.
Definition nat_eqType : eqType := Pack nat eqn.
Eval simpl in sort nat_eqType.
Compute sort nat_eqType.
Eval simpl in eq_op nat_eqType.

Check (eq_op nat_eqType 3 4).

Definition eqb (a b : bool) := if a then b else ~~ b.
Definition bool_eqType := Pack bool eqb.

Notation "x == y" := (@eq_op _ x y).
Locate "==".
Check (@eq_op bool_eqType true false).

Definition prod_cmp eqA eqB x y :=
  @eq_op eqA x.1 y.1 && @eq_op eqB x.2 y.2.

(* Check (3 == 4). *)

Canonical nat_eqType.
Canonical bool_eqType.

Check (3 == 4).
Check (true == false).
Compute false == false.
Compute false == true.

(* Check [law of addn]. *)

Print ltnW.
Lemma prime_gt1
