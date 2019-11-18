Require Import String.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.

Set Implicit Arguments.

Module Playground2.

  Locate "<=".

  Section Symmetric_Conjunction_Disjunction.
    Lemma andb_sym : forall A B : bool, A && B -> B && A.
    Proof.
      case.
        by case.
      by [].
    Qed.

    Lemma andb_sym' : forall A B : bool, A && B -> B && A.
    Proof.
      by case; case.
      Undo 1.
      (* If there were 10 boolean variables instead of 2,
         one could write do 10! case. *)
      by do 2! case.
    Qed.
  End Symmetric_Conjunction_Disjunction.

  (* https://coq.inria.fr/refman/user-extensions/syntax-extensions.html#custom-entries *)

  (* Example 1 *)

  (*
  Inductive Expr :=
  | One : Expr
  | Mul : Expr -> Expr -> Expr
  | Add : Expr -> Expr -> Expr.
  *)

  Inductive Expr :=
  | One
  | Mul (x y : Expr)
  | Add (x y : Expr).

  Declare Custom Entry expr.
  Notation "[ e ]" := e (e custom expr at level 2).

  Notation "1" := One (in custom expr at level 0).
  Notation "x y" := (Mul x y) (in custom expr at level 1, left associativity).
  Notation "x + y" := (Add x y) (in custom expr at level 2, left associativity).
  Notation "( x )" := x (in custom expr, x at level 2).

  Notation "{ x }" := x (in custom expr, x constr).

  Notation "x" := x (in custom expr at level 0, x ident).
  Axiom f : nat -> Expr.

  Check fun x y z => [1 + y z + {f x}].

  Unset Printing Notations.
  Check fun x y z => [1 + y z + {f x}].
  Set Printing Notations.

  Check fun e => match e with
  | [1 + 1] => [1]
  | [x y + z] => [x + y z]
  | y => [y + e]
  end.

  (* Example 2 *)

  Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

  Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

  Coercion AId : string >-> aexp.
  Coercion ANum : nat >-> aexp.

  Declare Custom Entry bexp.

  Notation "[[ e ]]" := e (e custom bexp at level 10).
  Notation "( x )" := x (in custom bexp, x at level 10).
  Notation "'true'" := (BTrue) (in custom bexp at level 0).
  Notation "'false'" := (BFalse) (in custom bexp at level 0).
  Notation "x <= y" := (BLe x y) (in custom bexp at level 5, no associativity).
  Notation "x = y" := (BEq x y) (in custom bexp at level 5, no associativity).
  Notation "x && y" := (BAnd x y) (in custom bexp at level 4, left associativity).
  Notation "'~' b" := (BNot b) (in custom bexp at level 3, right associativity).
  Notation "x + y" := (APlus x y) (in custom bexp at level 2, left associativity).
  Notation "x - y" := (AMinus x y) (in custom bexp at level 2, left associativity).
  Notation "x * y" := (AMult x y) (in custom bexp at level 1, left associativity).
  Notation "x" := x (in custom bexp at level 0, x constr at level 0).

  Check [[1 + 2 * 3]].
  Unset Printing Notations.
  Check [[1 + 2 * 3]].
  Set Printing Notations.

End Playground2.
