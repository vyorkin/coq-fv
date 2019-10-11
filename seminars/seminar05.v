From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat div seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section LeftPad.

(**
What is "leftpad"?

Leftpad is a function that takes a character, a length, and a string, and pads the string to that length.
It pads it by adding the character to the left.

Compute leftpad 0 5 [:: 1; 2; 3]. (* = [:: 0; 0; 1; 2; 3] *)
Compute leftpad 0 2 [:: 1; 2; 3]. (* = [:: 1; 2; 3]  *)
*)

(* nseq *)
(* используй [ncons] *)

(* [def] is the default value, i.e. type T is not empty *)
Variables (T : Type) (def : T).

Variables (x a1 a2 a3 : T).

(** Define the leftpad function, modeling strings as sequences of elements of type [T] *)

About ncons.
Definition leftpad (c : T) (n : nat) (s : seq T) : seq T :=
  ncons (subn n (size s)) c s.

Compute (leftpad x 4 [:: a1; a2; a3]).

(** The following properties of the leftpad function *)

Lemma length_max_spec c n s :
  size (leftpad c n s) = maxn n (size s).
Proof.
  rewrite size_ncons.
  rewrite maxnC.
  rewrite maxnE.
  by rewrite addnC.
Qed.

(** Local alias for the [nth] function
    returning the n-th element of the input sequence *)
Local Notation nth := (nth def).

Lemma prefix_spec c n s :
  forall i, i < n - size s -> nth (leftpad c n s) i = c.
Proof.
  by move=> ? H; rewrite nth_ncons H.
Qed.

Lemma suffix_spec c n s :
  forall i, i < size s -> nth (leftpad c n s) (n - size s + i) = nth s i.
Proof.
  move=> i _.

  (* About addnK. *)
  (* forall x : nat, x + n - n = x *)
  (* About addKn. *)
  (* forall x : nat, n + x - n = x *)

  (* About size_ncons. *)
  (* About size_nseq. *)
  (* rewrite /leftpad. *)
  (* rewrite addnC. *)
  (* Search _ "ncons" in seq. *)
  (* About nth_ncons. *)
  rewrite nth_ncons.
  (* About ifN. *)
  rewrite ifN.
  - rewrite addnC.
    by rewrite addnK.
  - Search _ "leq".
    (* leqNgt  forall m n : nat, (m <= n) = ~~ (n < m) *)
    rewrite -leqNgt.
    (* Search "addr" in ssrnat. *)
    by rewrite leq_addr.
Qed.

End LeftPad.



Section MoreInductionExercises.

(** Implement a recursive function performing integer division by 2 *)
Fixpoint div2 (n : nat) : nat :=
  if n is n.+1 then .

(* You might want to uncomment the following: *)
(* Arguments div2 : simpl nomatch. *)

Lemma nat_ind2' (P : nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P n.+2) ->
  forall n, P n.
Proof.
Admitted.

Lemma div2_le n : div2 n <= n.
Proof.
Admitted.

Lemma div2_correct n :
  div2 n = n./2.
Proof.
Admitted.



(** Strong induction principle *)
Lemma lt_wf_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, (k < m) -> P k) -> P m) ->
  forall n, P n.
Proof.
Admitted.


Fixpoint divn_my (n m : nat) {struct n} : nat :=
  if m is m'.+1 then
    if n - m' is d.+1 then
      (divn_my d m).+1
    else 0
  else 0.

Lemma divn_my_correct n m :
  divn_my n m = divn n m.
Proof.
Admitted.




Fixpoint fib (n : nat) : nat :=
  if n is (n''.+1 as n').+1 then fib n'' + fib n'
  else n.
Arguments fib n : simpl nomatch.

Lemma fib3 n :
  fib (3*n).+1 = (fib n.+1)^3 + 3 * fib n.+1 * (fib n)^2 - (fib n)^3.
Proof.
Admitted.

End MoreInductionExercises.
