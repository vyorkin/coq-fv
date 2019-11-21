From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.

(*** Exercise 1 *)

(** 1a. Define [orb_my] function implementing boolean disjunction *)

Definition orb_my (b1 b2:bool) : bool :=
  if b1 then true else b2.

(** 1b. Figure out the implementation of [orb] function in the standard library
        using Coq's interactive query mechanism *)

Print orb.

(** 1c. What's the difference between the standard implementation and
        the following one? *)

Definition orb_table (b c : bool) : bool :=
  match b, c with
  | true,  true  => true
  | true,  false => true
  | false, true  => true
  | false, false => false
  end.

(** Note: the above translates into nested pattern-matching, check this *)

Print orb_table.

(** 1d. Define [addb_my] function implementing exclusive boolean disjunction.
        {The name [addb] comes from the fact this operation behaves like addition modulo 2}
        If you are already familiar with proofs in Coq, think of a prover friendly
        definition, if you are not -- experiment with how different implementations
        behave under symbolic execution. *)

Definition addb_my (a b : bool) : bool :=
  match a, b with
  | true, false => true
  | false, true => true
  | _, _ => false
  end.

Variable x : bool.

Compute addb_my x true.
Compute addb_my true x.

(*** Exercise 2 *)

(** 2a. Implement power function of two arguments [x] and [n],
        raising [x] to the power of [n] *)

Fixpoint power (x n : nat) : nat :=
  match n with
  | O => S O
  | S p => muln x (power x p)
  end.

Compute (power 2 2).
Compute (power 2 3).
Compute (power 2 4).

(*** Exercise 3 *)

(** 3a. Implement division on unary natural numbers *)

Compute subn 4 1.

Fixpoint divn_my (a b : nat) : nat :=
  if b is b'.+1 then
    if subn a b' is n'.+1
    then S (divn_my n' b)
    else O
  else O.

Lemma div_my_n0 : forall x : nat, divn_my x 0 = 0. Proof. by case. Qed.
Lemma div_my_0n : forall x : nat, divn_my 0 x = 0. Proof. by case. Qed.

(* Unit tests: *)
Compute divn_my 0 0.  (* = 0 *)
Compute divn_my 1 0.  (* = 0 *)
Compute divn_my 0 3.  (* = 0 *)
Compute divn_my 1 3.  (* = 0 *)
Compute divn_my 2 3.  (* = 0 *)
Compute divn_my 3 3.  (* = 1 *)
Compute divn_my 8 3.  (* = 2 *)
Compute divn_my 42 1. (* = 42 *)
Compute divn_my 42 2. (* = 21 *)
Compute divn_my 42 3. (* = 14 *)
Compute divn_my 42 4. (* = 10 *)

From mathcomp Require Import div.

Compute divn 42 4. (* = 10 *)

Theorem div_eq_divn_my :
  forall x y : nat, divn_my x y = divn x y.
Proof.
  case.
    - by case; rewrite ?div0n ?divn0.
    - move => x y.
      elim: y => [| y' IHy'].
      + by rewrite divn0.

  (* Тут ничего не поможет из того, что мне на данный момент известно.
     Для доказательства понадобится сильная индукция
     (complete induction, course-of-values). *)

  (* div0n  forall d : nat, 0 %/ d = 0 *)
  (* divn0  forall m : nat, m %/ 0 = 0 *)
Admitted.

(** 3b. Provide several unit tests using [Compute] vernacular command *)


(*** Exercise 4 *)

(** Use the [applyn] function defined during the lecture
    (or better its Mathcomp sibling called [iter]) define

    4a. addition on natural numbers

    4b. multiplication on natural numbers

    Important: don't use recursion, i.e. no [Fixpoint] /
    [fix] should be in your solution.
*)

(** Here is out definition of [applyn]: *)
Definition applyn (f : nat -> nat) :=
  fix rec (n : nat) (x : nat) :=
    if n is n'.+1 then rec n' (f x)
    else x.

Definition addn' (x y : nat) : nat := applyn S x y.

Compute addn' 5 4.
Compute addn' 7 5.

Definition muln' (n x : nat) : nat :=
  applyn (fun v => addn' v x) (predn n) x.

Compute muln' 8 8.
