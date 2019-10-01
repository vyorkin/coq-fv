From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Lect3.
  (*** Universal quantifier *)

  Section Motivation.
    Variables A B : Type.

    (** Suppose we wrote two functions:
        a simple (a.k.a. gold) implementation and
        its optimized version.
        How do we go about specifying their equivalence? *)
    Variables fgold fopt : A -> B.

    Lemma fopt_equiv_fgold :
      forall x : A, fgold x = fopt x.
    Abort.

    (* Dependently typed functions *)

    (** ** Dependently typed predecessor function *)

    Definition Pred n :=
      if n is S n' then nat else unit.

    (** the value of [unit] type plays the role of a placeholder *)
    Print unit.

    Definition predn_dep : forall n, Pred n :=
      fun n => if n is S n' then n' else tt.

    Check erefl : predn_dep 7 = 6.
    Fail Check erefl : predn_dep 0 = 0.
    Check predn_dep 0 : unit.
    Check predn_dep 0 : Pred 0.
    Check predn_dep 7 : nat.

    Check erefl : predn_dep 0 = tt.
    Check erefl : Pred 0 = unit.

    (* Annotations for dependent pattern matching *)

    (* Type inference is undecidable *)
    Fail Check (fun n => if n is S n' then n' else tt).

    Check (fun n => if n is S n' as n0 return Pred n0 then n' else tt).

    (* Functional type is just a notation *)
    (* for a special case of [forall] *)

    Locate "->".

    Check predn : nat -> nat.
    Check predn : forall _ : nat, nat.
    Check predn : forall x : nat, (fun _ => nat) x.

  End Motivation.

  Section StandardPredicates.
    Variable T : Type.
    (* ... *)

  End StandardPredicates.

  Definition LEM :=
    forall P : Prop, P \/ ~ P.

  Definition Frobenius2 :=
    forall (A : Type) (P : A -> Prop) (Q : Prop),
      (forall x, Q \/ P x) <-> (Q \/ forall x, P x).

  Lemma lem_implies_Frobenius2 :
    LEM -> Frobenius2.
  Proof.
    rewrite /LEM /Frobenius2.
    move=> lem.
    move=> A P Q.
    split.
    - move=> all_qpx.
      case: (lem Q).
      + move=> q. left. exact q.
      + move=> nq.
        right.
        move=> x.
        (* Check all_qpx x. *)
        case: (all_qpx x).
        (* Check nq : Q -> False. *)
        by move/nq.
        by [].
    case; first by move=> q x; left.
    move=> all_px.
    move=> x.
    by right.
  Qed.

  Lemma Frobenius2_lem : Frobenius2 -> LEM.
  Proof.
    rewrite /Frobenius2=> frob.
    move=> P.
    Check (frob P (fun _ => False) P).
    (* rewrite /not. *)
    case: (frob P (fun _ => False) P).
    move=> H _; move: H.
    by apply=> p; left.
  Qed.

  Module MyExistential.

    Inductive ex_my (A : Type) (P : A -> Prop) : Prop :=
    | ex_intro (x : A) (proof : P x).

    (* Simplified notation *)

    Notation "'exists' x : A , p" :=
      (ex (fun x : A => p)) (at level 200, right associativity).

    Print ex_my.
    Print ex.

  End MyExistential.

  Lemma exists_not_forall A (P : A -> Prop) :
    (exists x, P x) -> ~ (forall x, ~ P x).
  Proof.
    case=> x px.
    move=> all.
    Check (all x).
    exact: (all x px).
  Qed.

  (* Definition curry' {A B C} : *)
  (*   (A * B -> C) -> (A -> B -> C) := *)
  (*   fun f => (fun a b => f (a; b)). *)

  Definition curry {A B C} :
    (A * B -> C) -> (A -> B -> C).
  move=> f a b.
  exact: (f (pair a b)).
  Defined.

  Lemma curry_dep A (P : A -> Prop) Q :
    ((exists x, P x ) -> Q) -> (forall x, P x -> Q).
  Proof.
    move=> f x px.
    exact: (f (ex_intro P x px)).
  Qed.

  Section Symmetric_Transitive_Relation.

    Variables (D : Type) (R : D -> D -> Prop).

    (* [Hypothesis] is a different syntax for [Variable] *)
    Hypothesis Rsym :
      forall x y, R x y -> R y x.

    Hypothesis Rtrans :
      forall x y z, R x y -> R y z -> R x z.

    Lemma relf_if :
      forall x : D, (exists y, R x y) -> R x x.
    Proof.
      move=> x.
      case=> y rxy.
      move: (Rsym rxy); move: rxy.
      by apply: Rtrans.
    Qed.

  End Symmetric_Transitive_Relation.

  Lemma exfalso_quodlibet :
    False -> forall P : Prop, P.
  Proof. by []. Qed.

  Definition exfalso_quodlibet_term :
    False -> forall P : Prop, P :=
    fun f => match f with end.

  Lemma False_implies_false :
    False -> false.
  (* Set Printing Coercions. *)
  (* Set Printing All. *)
  rewrite /is_true.
  Proof. case. Qed.

  (* Unset Printing Notations. *)
  Print is_true.
  (* Coercion is_true : bool -> Sortclass. *)

  Lemma false_implies_False :
    false -> False.
  Proof. by []. Qed.

  Check I : True.

  Definition false_implies_False_term :
    false -> False :=
    fun eq : false =>
      match eq in (_ = b)
            return (if b then False else True)
      with
      | erefl => I
      end.

  (* Injectivity of constructors *)

  Lemma succ_inj n m :
    S n = S m -> n = m.
  Proof.
    case. (* special case for [case] *)
    Show Proof.
    done.
  Qed.

  Lemma pair_inj A B (a1 a2 : A) (b1 b2 : B) :
    (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2).
    Proof. case. move=> ->->. by []. Qed.
    (* Proof. by case=> ->->. Qed. *)

    Lemma addnA :
      associative addn.
    Proof.
      move=> x y z.
      (* elim: x=> //. *)
      (* elim: x. *)
      (* have : 0 + 1 = 1. *)
      (* Set Printing All. *)
      (* rewrite /addn. *)
      elim: x=> // x IH.
      Search _ (_.+1 + _).
      rewrite addSn.
      rewrite IH.
      done.
    Qed.

    Lemma addnA' :
      associative addn.
    Proof.
      by move=> x y z; elim: x=> // x IH; rewrite addSn IH.
    Qed.

    Lemma add0n :
      left_id 0 addn.
    Proof. by []. Qed.

    Lemma addn0 :
      right_id 0 addn.
    Proof.
      by elim=> // x IH; rewrite addSn IH.
    Qed.

    Lemma addSnnS m n :
      m.+1 + n = m + n.+1.
    (* Proof. by elim: m=> // m IH; rewrite addSn IH. Qed. *)
    Proof.
      elim: m=> //.
      move=> m IH.
      rewrite addSn IH.
      done.
    Qed.

    Lemma addnC :
      commutative addn.
    Proof.
      move=> x y.
      elim: x; first by rewrite addn0.
      by move=> x IHn; rewrite addSn IHn -addSnnS.
    Qed.

    Check nat_ind.

    Definition nat_ind_my :
      forall P : nat -> Prop,
        P 0 -> (forall n : nat, P n -> P n.+1) ->
        forall n : nat, P n :=
      fun P p0 step =>
        fix rec n :=
          if n is n'.+1
            then step n' (rec n')
            else p0.
End Lect3.
