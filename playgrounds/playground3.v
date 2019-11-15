Require Import String.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.

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

End Playground3.
