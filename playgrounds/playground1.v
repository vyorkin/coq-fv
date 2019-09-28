From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.

Set Implicit Arguments.

Module Playground2.

Theorem modus_ponens : forall (P Q : Prop),
  (P -> Q) -> P -> Q.
Proof.
  move=> P Q PiQ P_holds.
  (* apply PiQ. clear PiQ. *)
  apply: PiQ.
  exact: P_holds.
Qed.

(* Since we know that [P -> Q], proving that [P] holds would also
   prove that [Q] holds. Therefore, we use [apply] to transform our goal. *)

Theorem modus_ponens_imp : forall (P Q : Prop),
  (P -> Q) -> P -> Q.
Proof.
  move=> P Q PiQ P_holds.
  (* apply PiQ. clear PiQ. *)
  move: PiQ.
  apply.
  exact: P_holds.
Qed.

(* Alternatively, we notice that [P] holds in our context, and
   because we know that [P -> Q], we can [apply] that implication to
   our hypothesis that [P] holds to transform it. *)

Theorem modus_ponens' : forall (P Q : Prop),
  (P -> Q) -> P -> Q.
Proof.
  move=> P Q PiQ P_holds.
  apply PiQ in P_holds.
  (* clear PiQ. *)
  exact P_holds.
Qed.

(* Note that this replaces our previous hypothesis (and now its
   name is no longer very applicable)! To prevent this, we can give
   our new hypothesis its own name using the [apply..in..as..] syntax. *)

Theorem modus_ponens'' : forall (P Q : Prop),
  (P -> Q) -> P -> Q.
Proof.
  move=> P Q PiQ P_holds.
  apply PiQ in P_holds as Q_holds. (* give a new name to our hypothesis *)
  (* clear PiQ P_holds. *)
  exact Q_holds.
Qed.

Section LongShit.

  Variables A B C D E F G : Prop.

  Lemma long_shit' :
    (A -> B -> C -> D) -> (A -> B -> C) -> (A -> B) -> A -> D.
  Proof.
    move=> H1 H2 H3 H4.
    move: H1.
    apply.
  Qed.

End LongShit.

End Playground2.
