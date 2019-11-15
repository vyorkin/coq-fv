From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Classical_reasoning.

(** We assert the classical principle of double negation elimination *)
Variable DNE : forall A : Prop, ~ ~ A -> A.

(* Evgeny Dashkov, [13.10.19 21:26]
   Может быть технически проще ввести дизъюнкцию

   (exists x, ~P x) \/ ~(exists x, ~P x)

   - либо    существует такой [x] для которого [P x] не верно
   - либо НЕ существует такой [x] для которого [P x] не верно

   А затем протащить отрицание под
   существование (интуиционизм) и снять его там по DNE. *)

(* https://en.wikipedia.org/wiki/Drinker_paradox *)
Lemma drinker_paradox (P : nat -> Prop) :
  exists x, P x -> forall y, P y.
Proof.
  apply: DNE.
  rewrite /not.
  move=> not_DP.
  apply: (not_DP).

  exists 0.
  Undo.
  apply: (ex_intro _ 0).

  move=> evP0 y.
  apply: DNE.
  rewrite /not.
  move=> not_Py.
  apply: (not_Py).

  (* Здесь паттерн-матчинг делается по доказательству [False] для
     моментального доказательства цели
     (т.е. мы пользуемся приципом "ex falso quodlibet" или "прицип взрыва"),
     а для того, чтобы можно было этим доказательством воспользоваться мы
     должны сначала доказать предпосылку:
     [exists x : nat, P x -> forall y : nat, P y] *)

  (* Другими словами для функций (а [not_DP] является функцией) разбор
     случаев делается для типа результата функции *)

  (* Если у нас есть
     [(P -> False) -> Q]
     то, если мы докажем [False], то мы докажем что угодно (и [Q] в том числе),
     тк [False -> P] означает типа "дай мне нечто, что нельзя сконструировать и
     я сконструирую тебе что угодно".

     Поэтому если сделать [case.] для такой цели [(P -> False) -> Q], то Coq нас
     сразу просит доказать только [P], тк доказав это вот [P] мы "автоматически докажем"
     вообще что угодно *)

  case: not_DP.

  exists y.
  move=> py x.
  move: not_Py.
  case.
  exact: py.

  Restart.

  apply: DNE => not_DP; apply/not_DP.
  exists 0=> _ y.
  apply: DNE => nPy; apply/nPy.
  case: not_DP.
  by exists y => /nPy.
Qed.

Section Arithmetics.

Lemma subn_leq0 n m :
  minn n m = n -> n - m = 0.
Proof.
  Search "minn".
  (* minnC : minn x y = minn y x *)

  rewrite minnC.
  rewrite minnE.
  move=> <-.
  (* n - (n - m) - m = 0 *)

  Search "subn".
  (* subn0  : x - 0 = x *)
  (* subnn  : x - x = 0 *)
  (* subnDA : n - (m + p) = n - m - p *)
  (* subnAC : x - y - z = x - z - y *)

  Search "addn".

  rewrite -subnDA.
  rewrite addnC.
  rewrite subnDA.
  rewrite subnn.
  rewrite sub0n.
  done.
Qed.

Lemma min_plus_r  n m p  :
  minn n m = n -> minn n (m + p) = n.
Proof.
  move/subn_leq0.
  move=> H.
  rewrite minnE.
  rewrite addnC.
  rewrite subnDA.
  rewrite subnAC.
  rewrite H.
  rewrite sub0n.
  by rewrite subn0.
Qed.

Lemma min_plus_minus m n p :
  minn n m + minn (n - m) p = minn n (m + p).
Proof.
  Search "minn".

  (* minnC     commutative minn       minn x y = minn y x
     minnA     associative minn       minn x (minn y z) = minn (minn x y) z
     minnCA    left_commutative minn  minn x (minn y z) = minn y (minn x z)
  *)

  Eval hnf in commutative minn.
  Eval hnf in associative minn.
  Eval hnf in left_commutative minn.

  rewrite [in minn (n - m) p]minnC.
  rewrite !minnE.
  rewrite subnDA.
  rewrite -minnE.
  rewrite addnC.
Qed.

Fixpoint zero (n : nat) : nat :=
  if n is n'.+1 then zero n'
  else 0.

Lemma zero_returns_zero n :
  zero n = 0.
Proof.
Admitted.

(**
Claim: every amount of postage that is at least 12 cents can be made
       from 4-cent and 5-cent stamps. *)
(** Hint: no need to use induction here *)
Lemma stamps n : 12 <= n -> exists s4 s5, s4 * 4 + s5 * 5 = n.
Proof.
Admitted.

End Arithmetics.


(* ======================================== *)

(** Bonus track: properties of functions and their composition.
    Feel free to skip this part.
 *)

(** Solutions for the exercises in seminar02.v, we are going to need them later *)
Section eq_comp.
Variables A B C D : Type.

(** Note: [rewrite !compA] would fail because it keeps adding [id \o ...]
    this is due to the fact that [compA] is a convertible rule,
    so it clashes with Miller pattern unification *)
Lemma compA (f : A -> B) (g : B -> C) (h : C -> D) :
  h \o g \o f = h \o (g \o f).
Proof. by []. Qed.

Lemma eq_compl (f g : A -> B) (h : B -> C) :
  f =1 g -> h \o f =1 h \o g.
Proof. by move=> eq_fg; apply: eq_comp. Qed.

Lemma eq_compr (f g : B -> C) (h : A -> B) :
  f =1 g -> f \o h =1 g \o h.
Proof. by move=> eq_fg; apply: eq_comp. Qed.

Lemma eq_idl (g1 g2 : A -> B) (f : B -> B) :
  f =1 id -> f \o g1 =1 f \o g2 -> g1 =1 g2.
Proof. by move=> f_id g12f a; move: (g12f a)=> /=; rewrite !f_id. Qed.

Lemma eq_idr (f1 f2 : A -> B) (g : A -> A) :
  g =1 id -> f1 \o g =1 f2 \o g -> f1 =1 f2.
Proof. by move=> g_id f12g a; move: (f12g a)=> /=; rewrite g_id. Qed.

End eq_comp.



(** You might want to use the lemmas from seminar02.v, section [eq_comp] *)
Section PropertiesOfFunctions.

Section SurjectiveEpic.
Context {A B : Type}.

(* https://en.wikipedia.org/wiki/Surjective_function *)
(** Note: This definition is too strong in Coq's setting, see [epic_surj] below *)
Definition surjective (f : A -> B) :=
  exists g : B -> A, f \o g =1 id.

(** This is a category-theoretical counterpart of surjectivity:
    https://en.wikipedia.org/wiki/Epimorphism *)
Definition epic (f : A -> B) :=
  forall C (g1 g2 : B -> C), g1 \o f =1 g2 \o f -> g1 =1 g2.

Lemma surj_epic f : surjective f -> epic f.
Proof.
Admitted.

Lemma epic_surj f : epic f -> surjective f.
  (** Why is this not provable? *)
Abort.

End SurjectiveEpic.


Section EpicProperties.
Context {A B C : Type}.

Lemma epic_comp (f : B -> C) (g : A -> B) :
  epic f -> epic g -> epic (f \o g).
Proof.
Admitted.

Lemma comp_epicl (f : B -> C) (g : A -> B) :
  epic (f \o g) -> epic f.
Proof.
Admitted.

Lemma retraction_epic (f : B -> A) (g : A -> B) :
  (f \o g =1 id) -> epic f.
Proof.
Admitted.

End EpicProperties.


(** The following section treats some properties of injective functions:
    https://en.wikipedia.org/wiki/Injective_function *)

Section InjectiveMonic.

Context {B C : Type}.

(** This is a category-theoretical counterpart of injectivity:
    https://en.wikipedia.org/wiki/Monomorphism *)
Definition monic (f : B -> C) :=
  forall A (g1 g2 : A -> B), f \o g1 =1 f \o g2 -> g1 =1 g2.

Lemma inj_monic f : injective f -> monic f.
Proof.
Admitted.

Lemma monic_inj f : monic f -> injective f.
Proof.
Admitted.

End InjectiveMonic.


Section MonicProperties.
Context {A B C : Type}.

Lemma monic_comp (f : B -> C) (g : A -> B) :
  monic f -> monic g -> monic (f \o g).
Proof.
Admitted.

Lemma comp_monicr (f : B -> C) (g : A -> B) :
  monic (f \o g) -> monic g.
Proof.
Admitted.

Lemma section_monic (f : B -> A) (g : A -> B) :
  (g \o f =1 id) -> monic f.
Proof.
Admitted.

End MonicProperties.

End PropertiesOfFunctions.
