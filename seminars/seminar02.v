From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Some basic functions *)

Definition const {A B} (a : A) := fun _ : B => a.

Definition flip {A B C} (f : A -> B -> C) : B -> A -> C :=
  fun b a => f a b.

Arguments const {A B} a _ /.
Arguments flip {A B C} f b a /.

(* move to logic_exercises *)
Section IntLogic.

Variables A B C D : Prop.

Lemma axiomK :
  A -> B -> A.
Proof. exact: const. Qed.

(* note: flip is more general *)
Lemma contraposition :
  (* (A -> (B -> False)) -> (B -> (A -> False)) *)
  (A -> ~ B) -> (B -> ~ A).
(* Proof. exact: flip. Qed. *)
Proof. rewrite /not. Check flip. exact: flip. Qed.

Lemma p_imp_np_iff_np :
  (* Which is equivalent to:
  ((A -> (A -> False)) -> (A -> False))        /\
  ((A -> False)        -> (A -> (A -> False)))
  *)
  (A -> ~A) <-> ~A.
Proof.
  split.
  - move => a_i_not_a a.
    exact: (a_i_not_a a).
  - move => not_a _.
    exact: not_a.
Qed.

(* We can generalize the previous lemma into *)
Lemma p_p_q_iff_p_q : (A -> A -> B) <-> (A -> B).
Proof.
  split.
  - move=> aa_i_b a.
    exact: (const aa_i_b a).
  - move=> a_i_b _.
    exact: a_i_b.
Qed.

Lemma p_is_not_equal_not_p :
  (* ((A -> (A -> False) /\ (A -> False) -> A) -> False) *)
  ~ (A <-> ~ A).
Proof.
  (* unfold not. *)
  (* rewrite /not. *)
  case.
  move=> a_i_not_a not_a_i_a.
  apply: (a_i_not_a).
  apply: not_a_i_a.
  move=> a.
  apply: (a_i_not_a).
  exact: a.
  exact: a.

  apply: not_a_i_a.
  move=> a.
  apply: a_i_not_a.
  exact: a.
  exact: a.
Qed.


Lemma p_is_not_equal_not_p' :
  (* ((A -> (A -> False) /\ (A -> False) -> A) -> False) *)
  ~ (A <-> ~ A).
Proof.
  (* unfold not. *)
  (* rewrite /not. *)
  case.
  move/p_imp_np_iff_np.
  move=> not_a not_a_i_a.
  apply: (not_a).
  by apply: not_a_i_a.
Qed.

Lemma not_not_lem :
  ~ ~ (A \/ ~ A).
Proof.
  rewrite /not.
  move=> not_lem.
  apply: (not_lem).
  left.
  Undo 1.
  right.
  move=> a.
  apply: not_lem.
  left.
  exact: a.
Qed.

Lemma not_not_lem' :
  ~ ~ (A \/ ~ A).
Proof. intuition. Defined.
Eval compute in not_not_lem'.

Lemma constructiveDNE :
  ~ ~ ~ A  ->  ~ A.
Proof.
  rewrite /not.
  move=> H a.
  apply: H.
  apply.
  exact: a.
Qed.

End IntLogic.


(* Boolean logic (decidable fragment enjoys classical laws) *)

Section BooleanLogic.

Lemma LEM_decidable a :
  a || ~~ a.
Proof.
  (* Используя команду [Set Printing Coercions].
     можно увидеть, что целью на самом деле является [is_true (a || ~~ a)],
     где [is_true] определяется как [fun b => b = true] *)
  Set Printing Coercions.
  (* [is_true] -- это стандартный способ поднять булево значение
     на уровень типов, коэрцию Coq вставляет неявно, в зависимости
     от контекста. Поскольку цель -- это всегда какой-то тип, то
     Coq понимает, что нужно булево значение преобразовать в тип,
     используя базу данных коэрций (в которую заранее добавлен [is_true]) *)
  Unset Printing Coercions.
  (* Unset Printing Notations. *)
  (* Search _ (orb _ (negb _)). *)
  (* Print orbN. *)
  (* apply orbN. *)
  (* Set Printing Notations. *)

  (* case a. by []. by []. *)
  (* case a. done. done. *)
  by case a.
Qed.

(* Check erefl. *)
(* Check (erefl true). *)

Lemma disj_implb a b :
  a || (a ==> b).
Proof.
  by case a.
  (* case a. *)
  (* - simpl. done. *)
  (* simpl. done. *)
Qed.

Lemma iff_is_if_and_only_if a b :
  (a ==> b) && (b ==> a) = (a == b).
Proof.
  by case a; case b.
Qed.

Lemma implb_trans : transitive implb.
Proof.
  (* case. case. case. done. done. done. *)
  (* case. done. done. *)

  by do 2! case.
  Undo 1.
  by case; case.
Qed.

Lemma triple_compb (f : bool -> bool) :
  f \o f \o f =1 f.
Proof.
  (* Unset Printing Notations. *)
  (* Print eqfun. *)
  (* Print funcomp. *)
  (* Set Printing Notations. *)

  (* Это моё глупое решение, следующие два более хитрые и короткие. *)

  case. simpl.
  - case E1:(f true).
    + by rewrite E1.
    + case E2:(f false).
      * by rewrite E1.
      * by rewrite E2.
    + simpl.
      * case E2:(f false).
        case E1:(f true).
        - by rewrite E1.
        - by rewrite E2.
      * by rewrite E2.


  Restart.

  (* [rewrite !E1] -- Переписать 1 или более раз
     [rewrite ?E2] -- Переписать 0 или более раз *)

  by case; case E1:(f true)=>/=; case E2:(f false); rewrite ?E1 ?E2. Restart.
  by case=>/=; case E1:(f true); case E2:(f false); rewrite ?E1 ?E2.

  (* [by t1; t2; ...] выполняет вот эти вот [t1; t2; ...] для каждой подцели.
     Т.е [by case;] сгенерить первые пару целей, потом следующие два [case]
     дадут нам ещё несколько случаев. И вот для каждого случая мы
     переписываем пока переписывается. *)
Qed.

(* negb \o odd means "even" *)
Lemma even_add :
  {morph (negb \o odd) : x y / x + y >-> x == y}.
Admitted.

End BooleanLogic.


(* some properties of functional composition *)

Section eq_comp.
Variables A B C D : Type.

(* Search _ involutive. *)

Lemma compA (f : A -> B) (g : B -> C) (h : C -> D) :
  h \o g \o f = h \o (g \o f).
Admitted.

Lemma eq_compl (f g : A -> B) (h : B -> C) :
  f =1 g -> h \o f =1 h \o g.
Admitted.

Lemma eq_compr (f g : B -> C) (h : A -> B) :
  f =1 g -> f \o h =1 g \o h.
Admitted.

Lemma eq_idl (g1 g2 : A -> B) (f : B -> B) :
  f =1 id -> f \o g1 =1 f \o g2 -> g1 =1 g2.
Proof.
Admitted.

Lemma eq_idr (f1 f2 : A -> B) (g : A -> A) :
  g =1 id -> f1 \o g =1 f2 \o g -> f1 =1 f2.
Proof.
Admitted.

End eq_comp.
