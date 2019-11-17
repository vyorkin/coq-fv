Require Import String.
From mathcomp Require Import all_ssreflect.
(* From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat. *)

Set Implicit Arguments.

Module Playground3.
Lemma or_sym2 : forall A B : bool, A \/ B -> B \/ A.
Proof.
  move=> [] [] AorB.
  (* Is a shortcut for [case; case; move=> AorB.] *)

  (* [apply/orP] rephrases the goal using the
     reflection lemma [orP], which is defined in the file [ssrbool.v]. *)

  apply/orP.

  move/orP : AorB.
  (* Is a shortcut for [move: AorB; move/orP.] *)
  Undo.
  move: AorB. move/orP.

  (* [move/orP] rephrases the top of the proof stack,
     i.e. A \/ B, using the reflection lemma [orP]. *)

  Restart.

  (* A reflection lemma is an equivalence property between the
    [bool] world and the [Prop] world. It is called a view when used in this way. *)

  by move=> [] [] AorB; apply/orP; move/orP : AorB.
Qed.

Lemma foo A (P : A -> Prop) :
  forall x, P x -> exists y, P y.
Proof.
  move=> x px.
  exact: (ex_intro P x px).
  Undo.
  exists x.
  exact: px.
Qed.

Lemma bar (P : Prop) :
  P -> (True -> bool) -> P.
Proof.
  move=> evP.

  (* Для функций  разбор случаев делается для типа результата функции: *)
  case.

  - exact: I.
  - exact: evP.
  exact: evP.
Abort.

Lemma ex1' (m n : nat) : ~ (3 * (m.+1) + 5 * (n.+1) = 12).
Proof.
  case: m.
  case: n=> // n.
  - by rewrite muln1 !mulnS addnA addnA.
  case.
  - rewrite [in 5 * n.+1]mulnS.
    rewrite addnA.
    case: n=> //.
    + by case.
Abort.


Lemma ex1_lia (m n : nat) : ~ (3 * (m.+1) + 5 * (n.+1) = 12).
Proof.
  case: m.
  case: n=> // n.
  lia.
Qed.

Lemma ex1 (m n : nat) : ~ (3 * (m.+1) + 5 * (n.+1) = 12).
Proof.
  case: m.
  case: n=> // n.
  - rewrite muln1.
    rewrite !mulnS addnA addnA.
    done.
  move=> m.
  rewrite !mulnS.
  rewrite !addSn.
  rewrite !add0n.
  rewrite -add2n.
  rewrite -add4n.
  rewrite addnA.
  rewrite addnA.
  rewrite -[in (5 * n).+1.+4]add4n.
  rewrite -[in (5 * n).+1]add1n.
  rewrite addnCA.
  rewrite addnAC.
  rewrite addnA.
  rewrite addnA.
  rewrite addnA.
  rewrite addnA.
  case: n. case: m=> //.
  - rewrite muln0 addn0.
    by case.
  by case.
Qed.

(* Lemma ex2 n m : 2 ^ 1 + 2 ^ 2 + ... + 2 ^ n = 2 ^ (n + 1) - 2. *)

Lemma ex2 n : \sum_(1 <= i < n) 2^i = 2^n - 2.
Proof.
Admitted.

End Playground3.
