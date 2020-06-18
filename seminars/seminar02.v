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
Proof.
  rewrite /not.
  Check flip.
  exact: flip.
Qed.

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

(* [apply] без [:] использует другой движок унификации,
   что может в дальнейшем привести к проблемам, т.е.
   лучше всегда использовать версию c [:], т.e. [apply: whatever] *)

Lemma p_is_not_equal_not_p :
  (* ((A -> (A -> False) /\ (A -> False) -> A) -> False) *)
  ~ (A <-> ~ A).
Proof.
  (* unfold not. *)
  rewrite /not.
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

  (* У нас выше есть доказанная лемма:
     p_imp_np_iff_np : (A -> ~A) <-> ~A *)

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
  ~ ~ ~ A -> ~ A.
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
  (* Search _ (_ || ~~_). *)

  (* Print orbN. *)
  (* apply orbN. *)
  (* Set Printing Notations. *)

  (* case a. by []. by []. *)
  (* case a. done. done. *)
  by case a.
Qed.

(* Check erefl. *)
(* Check (erefl true). *)

About implb.

Lemma disj_implb a b :
  a || (a ==> b).
Proof.
  case a.
  - done.
  done.
  Restart.

  by case a.
Qed.

Lemma iff_is_if_and_only_if a b :
  (a ==> b) && (b ==> a) = (a == b).
Proof.
  Locate "==>".
  (* Definition implb (b1 b2:bool) : bool := if b1 then b2 else true. *)
  by case a; case b.

  Restart.

  move: a b.
  by case; case.

  Restart.

  move: a b=> [[] | []] /=.
  Undo.
  by move: a b=> [[] | []].
Qed.

Lemma implb_trans : transitive implb.
Proof.
  Eval hnf in transitive implb.

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
  Locate "=1".
  (* Set Printing Notations. *)

  (* Это моё глупое решение, следующие два более хитрые и короткие. *)

 (* [simpl] это не ssreflec'овая тактика,
    так больше не делаем :) *)
  case. simpl.

  Undo 2.

  (* Если раскрыть определения [eqfun] и [funcomp],
     то [case] ниже станет более понятным *)
  rewrite /eqfun.
  rewrite /funcomp.

  (* Вот так правильно делать вместo [simpl], [//=] упрощает цель *)
  case=>//=.
  (* Мы можем разобрать возможные результаты
     ф-ции [f : bool -> bool] (их всего 2, тк в [bool] всегда 2 жителя) *)
  - case E1:(f true).
    (* ^ Именуем вариант, когда [f true = true] и сохраняем его в контексте,
         тк дальше будем использовать это равенство для переписывания *)
    + by rewrite E1.
      (* Здесь тоже рассматриваем возможные результаты ф-ции [f false]*)
    + case E2:(f false).
      * by rewrite E1.
      * by rewrite E2.
    + case E2:(f false).
      case E1:(f true).
      * by rewrite E1.
      * by rewrite E2.

    (* Приходится повторять тоже самое ещё раз...
       Если появляется необходимость повторять док-во,
       то обычно это знак, что есть какая-то симметрия,
       которую изначально не уловили и пошли другим путём.
     *)

  Restart.

  (* [rewrite !E1] -- Переписать 1 или более раз
     [rewrite ?E2] -- Переписать 0 или более раз *)

  by case; case E1:(f true)=>/=; case E2:(f false); rewrite ?E1 ?E2. Restart.
  by case=>/=; case E1:(f true); case E2:(f false); rewrite ?E1 ?E2.

  (* [by t1; t2; ...] выполняет вот эти вот [t1; t2; ...] для каждой подцели.
     Т.е [by case;] сгенерит первые пару целей, потом следующие два [case]
     дадут нам ещё несколько случаев. И вот для каждого случая мы
     переписываем пока переписывается. *)

   (* The [;] tactical applies the tactic on the right side of the
      semicolon to all the subgoals produced by tactic on the left
      side. *)
Qed.

(* negb \o odd means "even" *)
Lemma even_add :
  {morph (negb \o odd) : x y / x + y >-> x == y}.
Proof.
  Eval hnf in {morph (negb \o odd) : x y / x + y >-> x == y}.


  Locate "morph".
  Unset Printing Notations.
  Set Printing Notations.
  About morphism_2. (* Print morphism_2. *)
  (* В сущности мы говорим, что можем "продавить" морфизм [f] внутрь аргументов:
     Definition morphism_2 aOp rOp := forall x y, f (aOp x y) = rOp (f x) (f y). *)
  rewrite /morphism_2.
  (* Прикол в том, чтобы научиться доказывать леммы без
     использования индукции и предпочитать переписывания.
     Для этого нужно уметь искать другие леммы, тк
     oбычно значительная часть времени по доказательству
     уходит на поиск уже доказанных подходящих лемм,
     которые можно задействовать/использовать. *)
  move=> x y /=.
  Search _ (odd (_ + _)).
  About odd_add.
  Locate "(+)".
  About addb.
  (* have H: ~~ odd (x + y). rewrite odd_add. *)
  (* C [have H] это альтернативный путь, по которому можно пойти.
     Но можно просто переписывать часть цели/выражения.*)
  rewrite [in ~~ odd (x + y)] odd_add.
  (* Вот такой синтаксис как выше позволяет выпoлнить
     переписывание только в указанной часть выражения. *)
  (* Search _ (~~ _ (+) _). *)
  Search _ (~~ _ == _).
  rewrite eqb_negLR.
  Search _ (~~ ~~ _).
  rewrite Bool.negb_involutive.
  (* Search _ involutive. *)
  (* Search _ (~~ _ = _). *)
  (* rewrite negbK. *)

  Search _ (~~ (_ (+) _)).
  by rewrite negb_add.
Qed.

End BooleanLogic.


(* some properties of functional composition *)

Section eq_comp.
Variables A B C D : Type.

Lemma compA (f : A -> B) (g : B -> C) (h : C -> D) :
  h \o g \o f = h \o (g \o f).
Proof.
  done. Undo.
  Unset Printing Notations.
  (* Search _ (funcomp _). Print invariant. *)
  Set Printing Notations.
  About funcomp.
  (*     (B -> A) ->     (C -> B) -> C -> A *)
  (* (g : B -> C) \o (f : A -> B) -> A -> C  *)
  rewrite /funcomp.
  done.
Qed.

Lemma eq_compl (f g : A -> B) (h : B -> C) :
  f =1 g -> h \o f =1 h \o g.
Proof.
  Unset Printing Notations.
  Set Printing Notations.
  rewrite /eqfun /funcomp.
  move=> H a.
  by rewrite (H a).
Qed.

Lemma eq_compr (f g : B -> C) (h : A -> B) :
  f =1 g -> f \o h =1 g \o h.
Proof.
  by rewrite /funcomp; move=> H a; rewrite (H (h a)).
Qed.

Lemma eq_idl (g1 g2 : A -> B) (f : B -> B) :
  f =1 id -> f \o g1 =1 f \o g2 -> g1 =1 g2.
Proof.
  rewrite /funcomp /eqfun.
  move=> H_id H_eq_comp a.
  move: (H_eq_comp a); clear H_eq_comp.
  rewrite (H_id (g1 a)).
  rewrite (H_id (g2 a)).
  apply.
Qed.

Lemma eq_idr (f1 f2 : A -> B) (g : A -> A) :
  g =1 id -> f1 \o g =1 f2 \o g -> f1 =1 f2.
Proof.
  rewrite /funcomp.
  move=> H_id H_eq_comp a.
  move: (H_eq_comp a); clear H_eq_comp.
  (* Когда смотришь на что-то типа [g =1 id]
     нужно всегда иметь ввиду [foral x : A, g x = x]. *)
  by rewrite (H_id a).
Qed.

End eq_comp.

(* Dependent pattern-matching practice.
   Also see Lecture 3 (+links).
*)

About f_equal.
About eq_add_S.

About f_equal_pred.
Print eq_refl.

(* f_equal_pred : forall x y : nat, x = y -> x.-1 = y.-1 *)

Definition succ_inj (n m : nat) :
  S n = S m -> n = m
:=
  fun eqS =>
    match
      eqS in (_ = S v) (* v = m *)
      return (n = v)
    with
    | erefl => erefl
    end.


Definition false_eq_true_implies_False :
  false = true -> False :=
  fun prf =>
    match prf in (_ = t)
          return (if t then False else True)
    with
    | erefl => I
    end.

(* TL;DR про поиск:

   https://github.com/math-comp/math-comp/wiki/Search
   https://github.com/math-comp/math-comp/blob/master/CONTRIBUTING.md#where

   В общем виде поисковый запрос выглядит так:

   Search (-)?(symbol|pattern)+ (in (module)+)?

   где
     symbol  - какая-то подстрока
     pattern - какой-то шаблон

   Запрос вида Search pattern. ищет только в заключениях.
   Чтобы поискать везде, включая предпосылки, нужно писать:

   Search _ pattern.

*)

Search -(_ < _) -(_ = _) "odd" in ssrnat.

(*
Definition neq_sym A (x y : A) :
  x <> y -> y <> x
:=

Definition f_congr {A B} (f : A -> B) (x y : A) :
  x = y  ->  f x = f y
:=

Definition f_congr' A B (f g : A -> B) (x y : A) :
  f = g  ->  x = y  ->  f x = g y
:=

Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:=
*)
