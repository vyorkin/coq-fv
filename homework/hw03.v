From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Classical_reasoning.

(** We assert the classical principle of double negation elimination *)
Variable DNE : forall A : Prop, ~ ~ A -> A.

(* https://en.wikipedia.org/wiki/Drinker_paradox *)
Lemma drinker_paradox (P : nat -> Prop) :
  exists x, P x -> forall y, P y.
Proof.
  apply: DNE.
  rewrite /not.
  move=> not_DP.
  (* Применив обратное рассуждение мы показали, что для того, чтобы
     доказать ложь в данном случае достаточно доказать исходное утверждение.
     Но теперь мы имеем в контексте отрицание исходного утверждения,
     которым сможем воспользоваться далее. *)
  apply: (not_DP).
  (* Выберем произвольного человека *)
  exists 0.
  (* То же самое можно сделать и так: *)
  Undo.
  About ex_intro.
  apply: (ex_intro _ 0).
  Check (ex_intro _ 0).

  move=> evP0 y.
  apply: DNE.
  (* rewrite /not. *)
  move=> not_Py.
  (* Здесь используется тот же "трюк", что и выше:
     мы получаем в контексте отрицание доказываемого утверждения. *)
  apply: (not_Py).

  (* Здесь паттерн-матчинг делается по доказательству [False] для
     моментального доказательства цели
     (т.е. мы пользуемся приципом "ex falso quodlibet" или "прицип взрыва"),
     а для того, чтобы можно было этим доказательством воспользоваться мы
     должны сначала доказать предпосылку:
     [exists x : nat, P x -> forall y : nat, P y]. *)

  (* Другими словами для функций (а [not_DP] является функцией) разбор
     случаев делается для типа результата функции. *)

  (* Если у нас есть [(P -> False) -> Q] то, если мы докажем [False],
     то мы докажем что угодно (и [Q] в том числе), тк
     [False -> P] означает типа "дай мне нечто, что
     нельзя сконструировать и я сконструирую тебе что угодно".

     Поэтому если сделать [case.] для такой цели [(P -> False) -> Q], то Coq нас
     сразу просит доказать только [P], тк доказав это вот [P] мы "автоматически докажем"
     вообще что угодно. *)

  case: not_DP.
  Undo. (* Посмотрим на это немного подробнее *)
  move: not_DP.
  (* Получим утв. вида [(P -> False) -> Q] *)
  case. (* Доказав [P] докажем что угодно *)

  (* В формулировке теорем exists - нотация,
     в доказательствах -- тактика, похожая на split *)

  exists y.
  move=> py x.
  move: not_Py.
  rewrite /not.
  (* Аналогично, видим [(P -> False) -> Q] *)
  case.
  exact: py.

  Restart.

  apply: DNE => not_DP; apply/not_DP.
  exists 0=> _ y.
  apply: DNE => nPy; apply/nPy.
  case: not_DP.
  by exists y => /nPy.
Qed.

(* Альтернативная и более общая формулировка леммы:
   не только для натуральных чисел, а для любого обитаемого типа. *)


(* [inhabited] Это просто утверждение (в [Prop] / пропозициональном контекстe)
   о том, что некий тип [A] обитаем. Определение:

   Inductive inhabited (A:Type) : Prop :=
     inhabits : A -> inhabited A. *)

Lemma inhabited_exists A :
  (exists x : A, True) <-> inhabited A.
Proof.
  (* Оставил, чтобы явно прошагать *)

  split.
  case.
  move=> x t.

  (* Многие тактики, унаследованные от ванильного Coq,
     сначала делают [intros (move=> ...)] если работают на
     целях, для которых они не предназначены.

     [split] по сути берет (единственный) конструктор для
     типа данных цели и делает apply с ним.

     В данном случае это эквивалентно:

        move=> x t.
        constructor.

     Но не в общем, т.к. [split] ожидает, что у типа будет
     только один конструктор и выдаст ошибку в противном случае. *)

  split.
  Undo.

  constructor.
  exact: x.
  case.
  move=> x.
  exists.
  exact: x.
  exact: I.
  Undo 3.
  by exists.

  Restart.

  by split; case.
Qed.

(** Bonus: here is a bit more general formulation of the above lemma,
    we don't have to have predicates over [nat]s, having an inhabited type is enough *)
Lemma drinker_paradox' (A : Type) (P : A -> Prop) :
  inhabited A ->
  exists x, P x -> forall y, P y.
Proof.
apply: DNE => not_DP; apply/not_DP.
case=> a; exists a=> _ y.
apply: DNE => nPy; apply/nPy.
case: not_DP.
by exists y => /nPy.
Qed.

(* This closes the section, discharging over DNE *)
End Classical_reasoning.
Check drinker_paradox.

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

  Restart.

  move=> min.
  About maxnE. (* maxn m n = m + (n - m) *)
  (* we need injectivity of addition here *)
  Search _ addn "I".
  Eval hnf in (injective (addn _)).
  (* ?n + x1 = ?n + x2 -> x1 = x2 *)
  apply: (@addnI m).
  rewrite -maxnE.
  rewrite addn0.
  rewrite -min.
  Search _ maxn minn.
  rewrite minKn.
  by [].
Qed.

Lemma prod_inj (A B : Type) (x y: (A * B)) :
  x = y <-> (x.1, x.2) = (y.1, y.2).
Proof.
  split.
  move=> x_eq_y.
  - rewrite x_eq_y. done.
  case.
  case: x.
  case: y.
  move=> /=.
  move=> x y x' y'.
  move=> Heq1 Heq2.
  rewrite Heq1.
  rewrite Heq2.
  done.

  Restart.

  by move: x y=> [x1 x2] [y1 y2].

  Restart.

  move: x y=> [x1 x2] [y1 y2].
  move=> /=.
  split.
  apply.
  apply.
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

  (* minnC  commutative minn       minn x y = minn y x
     minnA  associative minn       minn x (minn y z) = minn (minn x y) z
     minnCA left_commutative minn  minn x (minn y z) = minn y (minn x z)
  *)

  Eval hnf in commutative minn.
  Eval hnf in associative minn.
  Eval hnf in left_commutative minn.

  rewrite [in minn (n - m) p]minnC.
  rewrite !minnE.
  rewrite subnDA.
  rewrite -minnE.
  rewrite addnC.

  (* Ну... я пытался! *)

  Restart.

  (* Решение Антона: *)

  Search _ ((?m <= ?n) || (?n <= ?m)).
  move: (leq_total m n).
  Search _ (_ || _) (_ \/ _).
  move/Bool.orb_prop.  (* vanilla Coq, the idiomatic approach would be move/orP *)
  case.
  - move=> le_mn.
    rewrite minnE.
    rewrite -{1}(subnKC le_mn).
    rewrite -{2}(add0n (n-m)).
    rewrite subnDr.
    rewrite subn0.
    rewrite addn_minr.
    rewrite subnKC.
    + done.
    done.
  - move/minn_idPl.
    move=> min.
    move: (min).
    move/subn_leq0.
    move=>->.
    rewrite min0n.
    rewrite addn0.
    rewrite min.
    move: min.
    by move/min_plus_r->.

Restart.

case: (leqP m n) => [le_mn | /ltnW/minn_idPl min_n].
- rewrite minnE.
  rewrite -{1}(subnKC le_mn) -{2}(add0n (n-m)) subnDr subn0.
  by rewrite addn_minr subnKC.
- move: (min_n)=> /subn_leq0 ->.
  rewrite min0n addn0 min_n.
  by rewrite min_plus_r.
Qed.

Fixpoint zero (n : nat) : nat :=
  if n is n'.+1 then zero n'
  else 0.

Lemma zero_returns_zero n :
  zero n = 0.
Proof. by elim: n. Qed.

(**
Claim: every amount of postage that is at least 12 cents can be made
       from 4-cent and 5-cent stamps. *)
(** Hint: no need to use induction here *)
Lemma stamps n : 12 <= n -> exists s4 s5, s4 * 4 + s5 * 5 = n.
Proof.
  (* Locate "%/". *)
  (* About divn. *)

  (* leq_div2r : forall d m n : nat, m <= n -> m %/ d <= n %/ d *)
  move/leq_div2r.
  move=> leq12n.
  Undo 2.

  move=> /leq_div2r leq12n.

  (* Locate "%%". *)
  (* About modn. *)

  (* Можно набрать сколько возможно монетами по 4 цента,
     а потом остальное монетами по 5 (это грубоватое объяснение идеи) *)

  exists (n %/ 4 - n %% 4). (* Сколько-то целых 4-центовых монет минус остаток *)
  exists (n %% 4).          (* Остаток 5-центовыми *)

  (* mulnBl   : (x - y) * z = x * z - y * z *)
  (* addnABC  : p <= m -> p <= n -> m + (n - p) = m - p + n. *)
  (* leq_mul  : m1 <= n1 -> m2 <= n2 -> m1 * m2 <= n1 * n2. *)
  (* ltnS     : (m < n.+1) = (m <= n). *)
  (* ltn_pmod : 0 < d -> m %% d < d. *)

  rewrite mulnBl -addnABC -?mulnBr ?muln1 ?leq_mul -?divn_eq //.
  by rewrite (leq_trans _ (leq12n 4)) // -ltnS ltn_pmod.
Qed.

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
(* Эпиморфи́зм в категории ― морфизм m : A → B,
   такой что из всякого равенства f ∘ m = h ∘ m следует f = h.
   Другими словами, на m можно сокращать справа. *)
  forall C (g1 g2 : B -> C), g1 \o f =1 g2 \o f -> g1 =1 g2.

Lemma surj_epic f : surjective f -> epic f.
Proof.
  rewrite /epic /surjective.

  case=> g inv_g C g1 g2.

  (* Идея доказательства очень простая, если
     увидеть, что можно использовать наше равенство в предпосылке
     [g1 \o f =1 g2 \o f]
     как аргумент ф-ции (=леммы) [eq_compr]. *)

  move=> eqEv.

  (* eq_compr (f g : B -> C) (h : A -> B) :
     f =1 g -> f \o h =1 g \o h. *)

  (* g : B -> A *)
  (* ev : g1 \o f =1 g2 \o f *)


  (* g1 \o f =1 g2 \o f -> f \o h =1 g \o h.*)
  (* g1 \o f =1 g2 \o f -> (g1 \o f) \o h =1 (g2 \o f) \o h.*)

  move: (eq_compr g eqEv).

  Undo 2.

  move=> /(eq_compr g).

  (*  g1 \o f       =1  g2 \o f       -> g1 =1 g2 *)
  (* (g1 \o f) \o g =1 (g2 \o f) \o g -> g1 =1 g2 *)

  rewrite compA.
  rewrite compA.
  move=> /(eq_idr inv_g).

  done.

  Restart.

  by case=> g inv_g C g1 g2 => /(eq_compr g); rewrite 2!compA => /(eq_idr inv_g).
Qed.

Lemma epic_surj f : epic f -> surjective f.
  (** Why is this not provable? *)
  rewrite /epic /surjective.
  (** A short answer:
      to prove a function surjective we need to explicitly provide its inverse,
      which is not possible in general. We know nothing about type [A],
      so we cannot construct a function of type [B -> A]
      unless there is a contradictory statement in our premises,
      which is not he case here. *)
Abort.

End SurjectiveEpic.


Section EpicProperties.
Context {A B C : Type}.

Lemma epic_comp (f : B -> C) (g : A -> B) :
  epic f -> epic g -> epic (f \o g).
Proof.
  rewrite /epic.
  move=> H1 H2 D g1 g2.

  (* Здесь тоже доказательство основывается на том, чтобы
     догадаться применить гипотезы к предпосылкам из цели. *)

  (* А ещё нужно догадаться переписать. *)

  rewrite -compA.
  rewrite -compA.

  move=> evEq.

  (* move: (H2 D (g1 \o f) (g2 \o f) evEq). *)
  (* Можно попросить Coq вывести типы за нас *)
  move: (H2 _ _ _ evEq).
  move=> evEq'.
  move: (H1 _ _ _ evEq').
  done.
Qed.

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
