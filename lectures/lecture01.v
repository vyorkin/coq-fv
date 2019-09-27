From mathcomp Require Import ssreflect.

Module Bool.
  Inductive bool : Type :=
  | true
  | false.

  Check true : bool.
  Check true.

  (* Gallina (курица (по-исп.)),
     e.g. "Gallina blanca" -- белая курица *)
  Definition idb := fun b : bool => b.

  Check (fun b : bool => b).
  Check idb.

  Definition negb (b : bool) :=
    match b with
    | true => false
    | false => true
    end.

  Compute idb true.
  Compute idb false.

  Compute negb true.
  Compute negb false.

  Variable c : bool.

  Compute idb c.
  Compute negb c.

  Definition andb (b c : bool) : bool :=
    match b with
    | true => c
    | false => false
    end.

  Compute andb c true.
  Compute andb c false.

End Bool.

Module Nat.
  Inductive nat : Type :=
  | S of nat
  | O.

  Print nat.

  Check O.
  Check S.
  Check (S O).
  Check S (S O).
  Check S (S (S O)).

  Definition inc := S.
  Definition inc' (n : nat) := S n.

  Print inc.
  Print inc'.

  Compute inc (S (S O)).
  Compute inc' (S (S O)).

  Definition pred (n : nat) : nat :=
    match n with
    | S n' => n'
    | O => O
    end.

  (* struct n -- structural recursion on parameter n *)

  (* doesn't work, coq is unable to guess that (S n') is
  "structurally smaller" than n *)

  (*
  Fixpoint foo (n m : nat) { struct n } : nat :=
    match n with
    | S (S n') => S (S (foo (S n') m))
    | S O => S m
    | O => m
    end.
  *)

  (* to make it work we should use an alias for (S n') -- Sn' *)

  Fixpoint foo (n m : nat) { struct n } : nat :=
    match n with
    | S (S n' as Sn') => S (S (foo Sn' m))
    | S O => S m
    | O => m
    end.

End Nat.

Check Nat.foo.

Module Props.
  Inductive False : Prop := .

  Print False.

  Fail Fixpoint loop (n : nat) : False := loop n.
  Fail Check (loop 0 : False).

  From mathcomp Require Import ssrfun ssrbool ssrnat.

  About nat.
  About S.

  Locate ".+1".

  (* Notation "n .+1" := (S n). *)
  (* Notations can not be partially applied *)

  Locate ".-1".
  Locate "_ <= _".
  Locate "_ `!".
  Locate "_ ^ _".

  (* Apply [n] times a function [f] on
     natural numbers to an input [x] *)
  Definition applyn' (f : nat -> nat) :=
    fix rec (n : nat) (x : nat) :=
      if n is n'.+1 then rec n' (f x)
      else x.

  Definition applyn'' :=
    fix rec (f : nat -> nat) (n : nat) (x : nat) :=
      if n is n'.+1 then rec f n' (f x)
      else x.

  Variable x : nat.

  Compute applyn'  S 5 42.
  Compute applyn'' S 5 42.

  Compute applyn'  S x 42.
  Compute applyn'' S x 42.

  Axiom fun_ext :
    forall (A B : Type) (f g : A -> B),
      (forall x, f x = g x) -> f = g.

  Section Applyn.
    Variable f : nat -> nat.
    Fixpoint applyn (n : nat) (x : nat) : nat :=
      if n is (S n') then applyn n' (f x)
      else x.

    Compute (applyn (S (S O)) O).
    Compute (applyn 42 0).
    Print applyn.
    Check applyn.
    About applyn.
  End Applyn.

End Props.
