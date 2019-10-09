From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section IntLogic.

(* Вот так надо хотеть^W искать! *)
Search _ ((is_true (?m <= ?n)) -> (is_true (?n <= ?p)) -> (is_true (?m <= ?p))).
(* А ещё можно искать в конкретном модуле *)
Search _ involutive in seq.
(* А вот тут [?a], [?b] и [?c] это мета-переменные,
   т.е. все значения, которые может принимать [?имя] в
   разных частях шаблона совпадают *)
Search _ ((?b - ?a) + ?c = (?b + ?c) - ?a).

Search cancel in ssrnat.

(* Frobenius rule: existential quantifiers and conjunctions commute *)
Lemma frobenius A (P : A -> Prop) Q :
  (exists x, Q /\ P x) <-> Q /\ (exists x, P x).
Proof.
  split.
  - case=> x qpx.
    + case: qpx.
      move=> q px.
      split.
      * exact: q.
      * exact: ex_intro P x px.
    + case=> q evx.
      * move: evx.
      * case=> x px.
        (* Есть тактика refine, ей можно скормить
           неполный терм с подчёркиваниями, после чего она
           предложит доказать всё недостающее *)
        refine (ex_intro _ _ (conj _ _)).
        Undo.
        Unset Printing Notations.
        (* Вот так можно посмотреть какой ожидаетcя вместо [P] *)
        Fail refine (ex_intro P _ _).
        Set Printing Notations.
        exact: ex_intro ((fun x : A => Q /\ (P x))) x (conj q px).
Qed.

Lemma exist_conj_commute A (P Q : A -> Prop) :
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  case=> x [px qx].
  split.
  - exact: ex_intro P x px.
  exact: ex_intro Q x qx.
Qed.

Lemma conj_exist_does_not_commute :
  ~ (forall A (P Q : A -> Prop),
        (exists x, P x) /\ (exists x, Q x) -> (exists x, P x /\ Q x)).
Proof.
  (* Нужно найти контр-пример, т.е. такой
     тип [A] и два предиката над ним, что получится доказать
     (exists x, P x) /\ (exists x, Q x), но при этом из
     (exists x, P x /\ Q x) получается противоречие.

     Другими словами:

     Нам нужны два "взаимнообратных" предиката, так чтобы по
     отдельности они были доказуемы на каких-то значениях, а
     вместе -- ни для одного значения.
      *)

  About ex_intro.

  (* ex_intro: forall (A : Type) (P : A -> Prop) (x : A), P x -> exists y, P y
     где [Argument A is implicit]

     т.е. смотрим только на следующее:

     ex_intro:
       (P : A -> Prop)  -- предикат
       (x : A),         -- значение
       P x              -- доказательство, что предикат выполняется на этом значении *)

  Check (ex_intro id).
  (* forall x : Prop, x -> exists x0 : Prop, x0

     Сформулируем на естественном языке. Это значит буквально:
     Для любого утверждения [x] предикат [id] выполняется только в случае,
     если это утверждение истинно.
  *)

  Check (ex_intro not).

  (* forall (x : Prop), ~ x -> exists y, ~ y *)
  (* forall (x : Prop) (_ : not x), ex not *)

  (* Аналогично, на ест. яз. это звучит как:
     Для любого утверждения [x] предикат [not x] истинен,
     если [x] ложь. *)

  move=> H.
  case: (H bool id not).
  - split.
    + exact: (ex_intro is_true true).
    + exact: (ex_intro (not \o is_true) false).
  by move=> b; case.
Qed.

(* helper lemma *)

(* Наличие импликации следующей формулировки
   "Если существет такой [x], для которого [P x] истинно, то выполняется [Q]"
   Влечёт за собой наличие импликации вида
   "Если для любого [x] выполняется [P x], то [Q] истина"

   Интиутивно понятно, что второе утверждение слабее первого, т.к.
   нам достаточно, чтобы утверждение [P] выполнялось хотя бы для одного [x].
*)
Lemma curry_dep A (P : A -> Prop) Q :
  ((exists x, P x) -> Q) -> (forall x, P x -> Q).
Proof. move=> f x px. exact: (f (ex_intro _ x px)). Qed.

(* Если не для всех [x] утверждение [P x] не истинно,
   то существует такой [x], для которого оно истинно. *)
Definition not_forall_exists :=
  forall A (P : A -> Prop),
    ~ (forall x, ~ P x) -> (exists x, P x).

(* Double negation elimination *)
Definition DNE := forall (P : Prop), ~ ~ P -> P.

(* Нужно доказать эквивалетность леммы о
   двойном отрицании и вот этой вот леммы выше. *)
Lemma not_for_all_is_exists_iff_dne :
  not_forall_exists <-> DNE.
Proof.
  rewrite /not_forall_exists /DNE.
  split=> [nfe | dne].
  (* Если присмотреться к форме [nfe], то видно, что там в
     некотором роде происходит снятие двойного отрицания:
     в предпосылку ~ (forall x : A, ~ P x) входят два отрицания,
     а в заключении (exists x : A, P x) их уже нет. *)
  - move=> P nnP.
    (* Подставим в параметр типа [A] в [nfe] "тип истины" -- [True].
       Конечно, до этого нужно ещё догадаться, но истину можно
       тривиально сконструировать, а это уже наводит на мысли ;) *)
    Check (nfe True).
    (* Нам нужно что-то из истины в [Prop], но [Prop] у нас есть, это [P] *)
    Check (nfe True (fun _ => P)).
    move: (nfe True (fun _ => P)).
    move=> H.
    (* А теперь заметим, что мы теперь можем
       сконструировать предпосылку гипотезы [H]:
       ((True -> (P -> False)) -> False)

       Так, посмотрим... Истина у нас есть, это [I].
       Применив её мы получим ((P -> False) -> False).
       Хм, что-то напоминает..., конечно, это же [nnP : ~ ~ P]! *)
    case: (H (fun tnP => nnP (tnP I))).
    (* Тут можно было бы использовать механизм "видов", тк:
       [case/H] ~ [move=> top. case: (H top)] *)
    + case.
      * exact: id.
      * move=> A P all_npx.
        (* Хорошо, давай посмотрим на
           all_npx : ((forall x : A, (P x -> False)) -> False)
           Нам нужен [x : A], любой, где его взять? -- Нигде.

           Посмотрим на цель.
           Заметим, что в цели утверждение о существовании [x : A],
           для док-ва которого нужно предъявить [P x].

           Вспомним, что у нас есть вспомогательная лемма:
           ((exists x, P x) -> Q) -> (forall x, P x -> Q)

           Наша цель немного отличается от формулировки данной леммы,
           а именно -- у нас нет [Q]. Как же добавить [Q] и чем оно может быть?
           Самое простое соображение может быть, что [Q] это [False] и
           тогда нам нужно инвертировать цель.

           А теперь, посмотрим на [dne], заметим, что тут
           мы можем применить backward reasoning, инвертируя цель. *)
        apply: dne.
        (* Вынесем гипотезу в контекст, a [all_npx] перетащим в цель *)
        move=> H.
        (* Отлично, если раскрыть определение [not], то мы увидим следующее:
           all_npx : (forall x : A, P x) -> False)
           Её предпосылка доказывает [False] в цели, применяем обратное рассуждение.*)
        apply: all_npx.
        (* Теперь мы можем воспользоваться леммой [curry_dep].
           Опять же, backward reasoning, всегда помним об этом принципе. *)
        apply: curry_dep.
        (* А это и есть наша гипотеза [H]! *)
        exact: H.
Qed.

End IntLogic.


Section BooleanLogic.

(** [==] is decidable equality operation for types with dec. eq.
    In case of booleans it means [if and only if]. *)
Fixpoint mostowski_equiv (a : bool) (n : nat) :=
  if n is n'.+1 then mostowski_equiv a n' == a
  else a.

(* ((a == a ...) == a) == a *)

Lemma mostowski_equiv_even_odd a n :
  mostowski_equiv a n = a || odd n.
Proof.
  elim: n=> [|n IHn] /=.
  - by rewrite Bool.orb_false_r.
  rewrite IHn. clear IHn.
  by case: a=> //=; rewrite eqbF_neg.
Qed.

End BooleanLogic.


Section Arithmetics.

Lemma addnCB m n : m + (n - m) = m - n + n.
Proof.
Admitted.

Lemma addnBC m n : n - m + m = m - n + n.
Proof.
Admitted.

Lemma addnBC' : commutative (fun m n => m - n + n).
Proof.
Admitted.

Lemma example_for_rewrite_patterns m n :
  m * n + m * n + m * n + n * m
  =
  m * n + m * n + m * n + n * m.
Proof.
(*
  Parenthesized goal:
         X
  /--------------\
  ((m * n + m * n) + m * n) + n * m
  =
  ((m * n + m * n) + m * n) + n * m
    \___________/
         X
*)
rewrite [in X in X + _ + _]mulnC.
done.
Abort.

Lemma subn_sqr m n : m ^ 2 - n ^ 2 = (m - n) * (m + n).
Proof.
Admitted.

Lemma leq_sub_add n m p : n - m <= n + p.
Proof.
Admitted.

(* prove by induction *)
Lemma odd_exp m n : odd (m ^ n) = (n == 0) || odd m.
Proof.
Admitted.

End Arithmetics.



Section Misc.
(** Exlpain why the folloing statement is unprovable *)

Definition const {A B} : A -> B -> A := fun a _ => a.

Lemma const_eq A B (x y : A) :
  @const A B x = const y -> x = y.
Abort.

End Misc.
