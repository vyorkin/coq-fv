From mathcomp Require Import ssreflect ssrfun ssrbool.

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

  Definition negb (b : bool) :=
    match b with
    | true => false
    | false => true
    end.

  Compute (negb false).

  Variable c : bool.

  Compute idb c.
  Compute (negb c).

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
  | O : nat
  | S : nat -> nat.

  (* struct n -- structural recursion on parameter n *)

  (* doesn't work, coq is unable to guess that (S n') is
  "structurally smaller" than n *)

  (* Fixpoint addn' (n m : nat) { struct n } : nat := *)
  (*   match n with *)
  (*   | S (S n') => S (S (addn' (S n') m)) *)
  (*   | S O => S m *)
  (*   | O => m *)
  (*   end. *)

  (* to make it work we should use an alias for (S n') -- Sn' *)

  Fixpoint addn (n m : nat) { struct n } : nat :=
    match n with
    | S (S n' as Sn') => S (S (addn Sn' m))
    | S O => S m
    | O => m
    end.

End Nat.

Module Props.
  Inductive False : Prop := .

  Print False.

  Fail Fixpoint loop (n : nat) : False := loop n.
  Fail Check (loop 0 : False).

  About nat.
  About S.

  Locate ".+1".
  (* Notation "n .+1" := (S n). *)

  (* Notations can not be partially applied *)

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
