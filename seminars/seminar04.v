From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From Coq Require Import Omega.

Section InductionExercises.

Fixpoint triple (n : nat) : nat :=
  if n is n'.+1 then (triple n').+3
  else n.

Lemma triple_mul3 n :
  triple n = 3 * n.
Proof.
  elim: n.
  - by [].
  - move=> n IHn //=.
    rewrite IHn.
    About mulnS.
    rewrite mulnS.
    move=>//=.
    Undo.
    done.

  Restart.

  by elim: n => //= n IHn; rewrite IHn mulnS.

  Restart.

  by elim: n=> //= n ->; rewrite mulnS.
Qed.

Lemma double_inj m n :
  m + m = n + n -> m = n.
Proof.
  elim: m n.
  - rewrite addn0.
    case.
    + rewrite add0n. done.
    + move=> n. rewrite addSn addnS. by [].
    move=> n IHn m.
    rewrite addnS addSn.
    case: m.
    + rewrite add0n. by [].
    move=> m.
    rewrite !addnS !addSn.
    case.
    move/IHn.
    Search _ (?n = ?m -> ?n.+1 = ?m.+1).
    About eq_S.
    apply: eq_S.
Qed.

(** Write a tail-recursive variation of the [addn] function
    (let's call it [addn_iter]). *)
Fixpoint add_iter (n m : nat) {struct n}: nat :=
  if n is n'.+1 then S (add_iter n' m)
  else m.

Lemma add_iter_correct m n :
  add_iter m n = m + n.
Proof.
  move: n.
  elim.
  Restart.
  by elim/nat_ind: n.
  Restart.
  by move: n; elim.
Qed.

Fixpoint fib (n : nat) : nat :=
  if n is (n''.+1 as n').+1 then fib n'' + fib n'
  else n.
Arguments fib n : simpl nomatch.

Lemma leq_add1l p m n :
  m <= n -> m <= p + n.
Proof.
  (* Search _ ((is_true (?m <= ?n)) -> (is_true (?n <= ?p)) -> (is_true (?m <= ?p))). *)
  (* Search _ ((?m <= ?n) -> _). *)

  (* leq_trans      forall n m p : nat, m <= n -> n <= p -> m <= p *)
  (* leq_ltn_trans  forall n m p : nat, m <= n -> n < p -> m < p *)

  (* leq_sub2r  forall p m n : nat, m <= n -> m - p <= n - p *)
  (* addnBA     forall m n p : nat, p <= n -> m + (n - p) = m + n - p *)
  (* addnBAC    forall m n p : nat, n <= m -> m - n + p = m + p - n *)
  (* addnBCA    forall m n p : nat, p <= m -> p <= n -> m + (n - p) = n + (m - p) *)
  (* addnABC    forall m n p : nat, p <= m -> p <= n -> m + (n - p) = m - p + n *)
  (* subnBA     forall m n p : nat, p <= n -> m - (n - p) = m + p - n *)

  move=> H.
Admitted.

Lemma fib_monotone m n :
  m <= n -> fib m <= fib n.
Proof.
Admitted.

Lemma fib_add_succ m n :
  fib (m + n).+1 = fib m.+1 * fib n.+1 + fib m * fib n.
Admitted.

End InductionExercises.



(* Thanks to Mike Potanin for pointing me to this example *)
(* https://en.wikipedia.org/wiki/Eckmann–Hilton_argument *)

Section EckmannHilton.

Context {X : Type}.
Variables f1 f2 : X -> X -> X.

Variable e1 : X.
Hypothesis U1 : left_id e1 f1 * right_id e1 f1.

Variables e2 : X.
Hypothesis U2 : left_id e2 f2 * right_id e2 f2.

Hypothesis I : interchange f1 f2.

Lemma units_same :
  e1 = e2.
Admitted.

Lemma operations_equal :
  f1 =2 f2.
Admitted.

Lemma I1 : interchange f1 f1.
Admitted.

Lemma operations_comm :
  commutative f1.
Admitted.

Lemma operations_assoc :
  associative f1.
Admitted.

End EckmannHilton.
