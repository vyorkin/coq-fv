From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*** Proofs by induction *)

(** * Generalizing Induction Hypothesis *)

(* Индукция это рекурсия в рамках теории типов *)

(** The standard (non-tail-recursive) factorial function *)
Locate "`!".
Print factorial.
Print fact_rec.

Fixpoint factorial_mul (n : nat) (k : nat) : nat :=
  if n is n'.+1 then
    factorial_mul n' (n * k)
  else
    k.

Definition factorial_iter (n : nat) : nat :=
  factorial_mul n 1.

Lemma factorial_mul_correct n k :
  factorial_mul n k = n`! * k.
Proof.
  (* elim: n k. *)
  (* Undo. *)
  (* move: n k. *)
  (* elim. *)
  (* - move=> k. *)
  (*   rewrite /factorial_mul. *)
  (*   (* Print fact0. *) *)
  (*   rewrite fact0. *)
  (*   rewrite mul1n. *)
  (*   by []. *)
  (* - move=> n IHn. *)
  (*   About factS. *)
  (*   rewrite factS. *)
  (*   rewrite -IHn. *)
  (*   About mulnCA. *)
  (*   Print mulnA. *)

  elim: n k=> [|n IHn] k; first by rewrite fact0 mul1n.
  by rewrite factS /= IHn mulnCA mulnA.
Qed.

Lemma factorial_iter_correct n :
  factorial_iter n = n`!.
Proof.
  (* elim: n =>/=. *)
  (* Undo. *)
  (* elim: n => // n IHn. *)
  (* rewrite /factorial_iter. *)
  (* rewrite /factorial_iter in IHn. *)
  (* В ssreflect не работает [rewrite Smth in *] и
     это не рекомендуемый стиль *)
  (* move=>/=. *)
  (* rewrite factorial_mul_correct. *)
  (* rewrite IHn. *)
  (* rewrite /factorial /=. *)
  (* done. *)

  by rewrite /factorial_iter factorial_mul_correct muln1.
Qed.


(** * Fibonacci numbers and custom induction principles *)

(** Let's define a recursive fibonacci function *)

(** Coq cannot figure out that we are using
    structural recursion here. It needs a hint. *)
Fail Fixpoint fib (n : nat) : nat :=
  if n is n''.+2 then fib n'' + fib n''.+1
  else n.

(** Here is the hint: name a structural subterm explicitly
    using [as]-annotation *)
Fixpoint fib (n : nat) : nat :=
  if n is (n''.+1 as n').+1 then fib n'' + fib n'
  else n.


(** Illustrate how [simpl nomatch] works *)

Section Illustrate_simpl_nomatch.
Variable n : nat.

Lemma default_behavior :
  fib n.+2 = 0.
Proof.
move=> /=.  (* fib n.+1 should not get simplified *)
Abort.

Arguments fib n : simpl nomatch.

Lemma after_simpl_nomatch :
  fib n.+2 = 0.
Proof.
move=> /=.  (* this is what we want *)
Abort.

End Illustrate_simpl_nomatch.


(** The results of the [Arguments] command does not survive
    sections so we have to repeat it here *)
Arguments fib n : simpl nomatch.


(** And here is a more efficient iterative version *)
Fixpoint fib_iter (n : nat) (f0 f1 : nat) : nat :=
  if n is n'.+1 then fib_iter n' f1 (f0 + f1)
  else f0.

Arguments fib_iter : simpl nomatch.

Lemma fib_iterS n f0 f1 :
  fib_iter n.+1 f0 f1 = fib_iter n f1 (f0 + f1).
Proof. by []. Qed.

Lemma fib_iter_sum n f0 f1 :
  fib_iter n.+2 f0 f1 =
  fib_iter n f0 f1 + fib_iter n.+1 f0 f1.
Proof.
elim: n f0 f1 => [//|n IHn] f0 f1.
by rewrite fib_iterS IHn.
Qed.

Lemma dup {A} : A -> A * A. Proof. by []. Qed.

(** This induction principle repeats, in a sense,
    the structure of the (recursive) Fibonacci function *)
Lemma nat_ind2 (P : nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P n.+1 -> P n.+2) ->
  forall n, P n.
Proof.
  move=> p0 p1 step n.
  (* [have: P n /\ P n.+1.], но это другое *)
  (* В ванильном Coq есть аналогичная тактика [enough] *)
  suffices: P n /\ P n.+1.
  by case.
  elim: n=> // n [IHn1 IHn2].
  split=> //.
  apply: step.
  - exact: IHn1.
  - exact: IHn2.

  Undo 10.

  move=> p0 p1 step n; suffices: P n /\ P n.+1 by case.
  (* elim: n=> // n [/step]. *)
  elim: n=> // n. move=>[]. move/step => impl.
  by move=> /dup[/impl].

  Undo 5.

  (* Желательно объединять несколько тактик в одну,
     когда они формируют некоторый шаг в неформальном док-ве *)

  move=> p0 p1 Istep n; suffices: P n /\ P n.+1 by case.
  by elim: n=> // n [/Istep pn12] /dup[/pn12].
Qed.

Lemma fib_iter_correct n :
  fib_iter n 0 1 = fib n.
Proof.
  elim/nat_ind2: n=> // n IHn0 IHn1.
  by rewrite fib_iter_sum /= -IHn0 -IHn1 addnC.
  Undo 2.
  elim/nat_ind2: n=> // n IHn0 IHn1.
  by rewrite fib_iter_sum IHn0 IHn1.
Qed.
(** Note: fib_iter_correct can be proven using
    suffices:
     (fib_iter n 0 1 = fib n /\ fib_iter n.+1 0 1 = fib n.+1).
 *)



(** * Another way is to provide a spec for fib_iter *)

From Coq Require Import Omega.
From Coq Require Import Psatz.

Lemma fib_iter_spec n f0 f1 :
  (* Основная сложность тут это догадаться до
     формулировки леммы, док-во тивиально *)
  fib_iter n.+1 f0 f1 = f0 * fib n + f1 * fib n.+1.
Proof.
  elim: n f0 f1=> [|n IHn] f0 f1; first by rewrite muln0 muln1.
  by rewrite fib_iterS IHn /= mulnDr mulnDl addnCA.

  (* Это можно доказать тактиками:
     lia - линейная челочисленная арифметика
     omega - арифметика Пресбургера (заточена на работу с операторами из ванильного Coq ) *)
Qed.

Lemma fib_iter_correct' n :
  fib_iter n 0 1 = fib n.
Proof.
  by case: n=> // n; rewrite fib_iter_spec mul0n mul1n.
Qed.


(** * Yet another solutiton *)

(* due to D.A. Turner, see his "Total Functional Programming" (2004) *)
Lemma fib_iter_spec' n p :
  fib_iter n (fib p) (fib p.+1) = fib (p + n).
Proof.
  elim: n p=> [|n IHn] p; first by rewrite addn0.
  by rewrite fib_iterS IHn addnS.
Qed.

Lemma fib_iter_correct'' n :
  fib_iter n 0 1 = fib n.
Proof.
  Fail apply: fib_iter_spec'.
  suffices: (fib_iter n (fib 0) (fib 1) = fib n) by [].
  by apply: fib_iter_spec'.
Qed.



(** * Complete induction *)

(** It's also called:
    - strong induction;
    - well-founded induction;
    - course-of-values induction
 *)


Lemma lt_wf_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, (k < m) -> P k) -> P m) ->
  forall n, P n.
Proof.
  (* move=> m n. *)
  (* Search _ (_ < _ ). *)
Admitted.


(** In SSReflect/Mathcomp one does not use
    a custom principle like above
    directly, but rather generates it on the fly
    using [leqnn] lemma.
 *)

Lemma fib_iter_correct''' n :
  fib_iter n 0 1 = fib n.
Proof.
elim: n {-2}n (leqnn n)=> [[]//|n IHn].
case=> //; case=> // n0.
rewrite fib_iter_sum.
move=> /dup[/ltnW/IHn-> ].
by rewrite ltnS=> /IHn->.
Qed.





(*** Lists *)

From mathcomp Require Import ssrnat ssrbool eqtype seq path.
(** Note that we added [seq] and [path] modules to imports *)

(** [seq] is a Mathcomp's notation for [list] data type *)
Print seq.
Print list.

(**
   Inductive list (A : Type) : Type :=
   | nil : seq A
   | cons : A -> seq A -> seq A
*)

(** A simple example *)
Compute [:: 1; 2; 3] ++ [::].

(** List concatenation *)
Locate "++".
Print cat.


(** * Structural Induction for Lists *)

Section StructuralInduction.

Variable T : Type.

Implicit Types xs ys zs : seq T.

Lemma catA xs ys zs :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof.

Check list_ind :
  forall (A : Type) (P : seq A -> Prop),
    P [::] ->
    (forall (a : A) (l : seq A), P l -> P (a :: l)) ->
    forall l : seq A, P l.

by elim: xs=> //= x xs' ->.
Qed.

End StructuralInduction.


(** * Classical example: list reversal function *)

(** The standard implementation is tail recursive *)
Print rev.
Print catrev.

Fixpoint rev_rec {A : Type} (xs : seq A) : seq A :=
  if xs is (x::xs') then
    rev_rec xs' ++ [:: x]
  else xs.

Lemma rev_rec_inv A :
  involutive (@rev A).
Proof.
Admitted.

Lemma rev_correct A (xs : seq A):
  rev xs = rev_rec xs.
Proof.
Admitted.