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
    + by rewrite add0n.
    + by [].
    move=> n IHn n0.
    rewrite addnS addSn.
    move=> H.

  move=> m IHm n.
  rewrite addSn.
  rewrite addnS.
  case: n.
  - by [].
    move=> n.
    rewrite addSn addnS.
    (* S (S x) = S (S y) -> x = y *)
    case.
    move/IHm.
    move=> top.
    rewrite top.
    Undo 2.
    move=>->.
    done.
Qed.


(** Write a tail-recursive variation of the [addn] function
    (let's call it [addn_iter]). *)
Fixpoint add_iter (n m : nat) {struct n}: nat.
Qed.

Lemma add_iter_correct m n :
  add_iter m n = m + n.
Admitted.


Fixpoint fib (n : nat) : nat :=
  if n is (n''.+1 as n').+1 then fib n'' + fib n'
  else n.
Arguments fib n : simpl nomatch.

Lemma leq_add1l p m n :
  m <= n -> m <= p + n.
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
