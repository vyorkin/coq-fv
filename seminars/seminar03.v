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
  (* Сначала глупое решение, до которого я додумался сам: *)
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

  Restart.
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
  (* Было бы неплохо как-то элиминировать [m].
     Для этого нужно для начала раскрыть скобки. *)

  (*           m + (n - m) = m - n + n *)
  (* m <= n -> m + (n - m) = m + n - m *)
  rewrite addnBA.
  rewrite addKn.

  (* Search _ (?a + ?b - ?b = ?a). *)
  (* Так не получится.
     Найти нужную лемму можно вот так: *)
  (* Search _ cancel addn subn. *)

  (* Как же догадаться поискать такое?
     Существует такая штука, как [cancel]:

     fun (rT aT : Type) (f : aT -> rT) (g : rT -> aT) =>
       forall x : aT, g (f x) = x

     Т.е. ф-ция [g] нейтрализует [f] *)
  (* Print cancel. *)

  (* About addKn. Eval hnf in cancel (addn n) (subn^~ n). *)
  (* n + x - n = x *)
  (* About addnK. Eval hnf in cancel (addn^~ n) (subn^~ n). *)

  (* apply: eqP. *)
  (* Eval hnf in self_inverse 0 subn. *)

  (* addn_eq0   forall m n   : nat, (m + n == 0) = (m == 0) && (n == 0) *)
  (* eqn_add2l  forall p m n : nat, (p + m == p + n) = (m == n) *)
  (* eqn_add2r  forall p m n : nat, (m + p == n + p) = (m == n) *)

  (* Search _ addn _ in ssrnat. *)
  (* Search _ subn _ in ssrnat. *)

  (* About addnC. *)
  (* Eval hnf in commutative addn. *)
  (* rewrite [in _ - n + n] addnC. *)

  (* About subnn. *)
  (* Eval hnf in self_inverse 0 subn. *)
  (* About addn0. *)
  (* Eval hnf in right_id 0 addn. *)
  (* About add0n. *)
  (* Eval hnf in left_id 0 addn. *)

  (* rewrite [in _ - _] subnn. *)

  Restart.

  (* В общем, фиг его знает, этим путём не пройти. *)
  (* Попробуем поискать что-то типа. *)

  Search _ (?m + (?n - ?m)) in ssrnat.
  (* Находятся 2 леммы:

     subnKC forall m n : nat, m <= n -> m + (n - m) = n
     ^^ подобным путём мы уже ходили -- он никуда не приводит,
     тк доказать m <= n в не получится.

     maxnE  forall m n : nat, maxn m n = m + (n - m)
     ^^ А вот это можно и попробовать. *)
  rewrite -maxnE.

  (* Если посмотреть внутрь [rewrite /maxn.], то
     можно увидеть как это будет работать на натуральных числах:

     (if 2 < 3 then 3 else 2) = 2 - 3 + 3 <=>
                  3         =   0     + 3 <=>
                  3         =           3
  *)

  (* Поищем что у нас ещё есть про "maxn" подходящего для док-ва:
     maxn m n = m - n + n
  *)
  Search _ "maxn" in ssrnat.
  (* maxnE  forall m n : nat, maxn m n = m + (n - m) *)
  (* maxnC  commutative maxn *)
  Eval hnf in commutative maxn.

  rewrite maxnC.
  rewrite maxnE.
  rewrite addnC.
  done.
Qed.

Lemma addnBC m n : n - m + m = m - n + n.
Proof. by rewrite addnC addnCB. Qed.

Lemma addnBC' : commutative (fun m n => m - n + n).
Proof.
  (* Eval hnf in commutative (fun m n => m - n + n). *)
  (* forall x y : nat, x - y + y = y - x + x *)
  (* rewrite /commutative. *)
  move=> m n.
  by rewrite addnBC.
Qed.

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
  (* About mulnC. *)
  (* Eval hnf in commutative muln. *)
  (* x * y = y * x *)

  (* Вот так мы фокусируемся на
     переписывани "подвыражения подвыражения" *)
  rewrite [in X in X + _ + _]mulnC.
  done.
Abort.

Lemma subn_sqr m n : m ^ 2 - n ^ 2 = (m - n) * (m + n).
Proof.
  (* Начнём максимально наивно --
     попробуем поискать подходящие леммы по наибольшим запросам/шаблонам. *)
  Search _ (?m ^ 2 - ?n ^ 2).
  Search _ ((?m - ?n) * _).
  Search _ (_ * (?m + ?n)).
  (* Только наша лемма, ничего больше.
     Что у нас есть из менее общего (по мере уменьшения уникальности и общности)?
     - возведение в квадрат
     - возведение в степень
     - умножение
     - вычитание *)
  Search _ (?m ^ 2).
  Search _ (?m ^ ?n).
  (* Что-то нашли. Полезным пока кажется только [mulnn].
     А ещё у нас есть скобки, и нам нужно их раскрыть. *)
  Search _ (muln (?m _ ?n) _).
  Search _ "muln" in ssrnat.
  (* Cледующие несколько лемм выглядят полезными: *)

  (* mulnDl left_distributive muln addn *)
  (* Eval hnf in left_distributive muln addn. *)
  (* (x + y) * z = x * z + y * z *)

  (* mulnDr right_distributive muln addn *)
  (* Eval hnf in right_distributive muln addn. *)
  (* x * (y + z) = x * y + x * z *)

  (* mulnBl left_distributive muln subn *)
  (* Eval hnf in left_distributive muln subn. *)
  (* (x - y) * z = x * z - y * z *)

  (* mulnBr right_distributive muln subn *)
  (* Eval hnf in right_distributive muln subn.  *)
  (* x * (y - z) = x * y - x * z *)

  (* Начнём раскрывать скобки: *)
  rewrite mulnDr.
  do 2! rewrite mulnBl.
  do 2! rewrite mulnn.
  (* Приведём вхождения [n * m] & [m * n] к одному виду *)
  rewrite [in n * m]mulnC.
  (* Нужно раскрыть скобки и избавиться от [m * n] *)

  Search _ (_ + (_ - _)).
  (* addnCB forall m n : nat, m             + (n     - m)     = m - n + n *)
  (*                          m ^ 2 - m * n + (m * n - n ^ 2) *)
  (* Нет, это не то, попробуем поискать что ещё можно сделать.

     У нас
     m ^ 2 - m * n + (m * n - n ^ 2)
     это по сути вот такое выражение:
     x - y + (y - z)
  *)
  Search _ (?x - ?y + (?y - ?z)).
  Search _ ( _ - _  + (_ - _)).
  Search _ ((_ - _) +  _ - _).
  (* Но ничего подобного нет. Поищем что-то более общее. *)
  Search _ (?x - ?y + ?z).
  Search _ (?z + ?x - ?y).
  (* subnDl forall p m n : nat, p + m - (p + n) = m - n *)
  (* subnDr forall p m n : nat, m + p - (n + p) = m - n *)
  (* Тоже не подходит. *)

  rewrite addnC.

  Search _ "add" in ssrnat.

  (* Ну вот, тупик. Возможно, стоит попробовать иначе раскрыть скобки.
     Кажется, мне нужно, чтобы сложение оказалось внутри скобок каким-то образом. *)

  Restart.

  rewrite mulnC.
  rewrite mulnBr.
  do 2! rewrite mulnDl.
  rewrite [in m * n] mulnC.
  (* Ок, тепеpь у нас сложение внутри скобок. Посмотрим... *)
  (* m * m + n * m - (n * m + n * n) *)
  (* subnDr forall p m n : nat, m + p - (n + p) = m - n *)
  (* Выглядит очень похоже, применим коммутативность сложения: *)
  rewrite [in (n * m + n * n)]addnC.
  (* О да, теперь мы можем применить *)
  rewrite subnDr.
  by do 2! rewrite mulnn.

  Restart.

  (* Не уверен, что это круто так писать, но ситаксически это корректно. *)
  by rewrite
       mulnC mulnBr 2!mulnDl
       [in m * n]mulnC
       [in (n * m + n * n)]addnC
       subnDr 2!mulnn.
Qed.

Lemma leq_sub_add n m p : n - m <= n + p.
Proof.
  (* Применим ту же схему решения.
     Cначала ищем максимально специализированные леммы.
     Если ничего подходящего не находится -- ищем более общие.
     Пробуем идти разными путями. Если заходим в тупик,
     возвращаемся на "развилку" и пробуем идти другой тропинкой. *)
  Search _ (?n - ?m <= ?n + ?p).

  Search _ (_ -> _ <= ?n + ?p).
  Search _ (_ -> _ <= _).

  (* Импликацию и булевы предикаты лучше не смешивать в шаблонах поиска --
     коэрция [is_true] не вставляется, когда работает [Search].
     Правильно было бы написать запрос вот так: *)
  Search _ ((is_true _) -> is_true (_ <= _)).
  Search _ ((is_true _) -> is_true (_ <= ?n + ?p)).

  Search _ (_ - _ <= _ + _).
  (* Ничего, попробуем найти более общие. *)
  Search _ (_ <= _ + _).
  Search _ (_ - _ <= _).
  (* Если не получается искать по шаблону,
     то нужно пробовать искать по имени. *)
  Search eq subn addn leq.

  (* leq_subLR  (m - n <= p) = (m <= n + p) *)
  (* subnKC      m <= n -> m + (n - m) = n *)
  (* subnK       m <= n -> n - m + m = n *)

  (* Идея в том, чтобы перенести вычитание из левой в правую
     часть (для этого уже есть стандартная лемма). *)

  rewrite leq_subLR.
  do 2! rewrite addnA addnC.

  (* Search _ (?n <= ?n + _). *)
  (* leq_addr  forall m n : nat, n <= n + m *)
  by rewrite leq_addr.
Qed.

(* prove by induction *)
Lemma odd_exp m n : odd (m ^ n) = (n == 0) || odd m.
Proof.
  (* Вспомним, что у нас уже было нечто похожее...
     Что-то про эквивалентность Мостовского, можно переписать *)
  About mostowski_equiv_even_odd.
  rewrite -mostowski_equiv_even_odd.
  (* Но пока не понятно что именно это нам даёт, вернём обратно *)
  rewrite mostowski_equiv_even_odd.
  (* Посмотрим что у нас есть про нечётные числа и про степени. *)
  Search (_ ^ _) in ssrnat.
  elim: n.
  - by rewrite expn0.
  - move=> n IHn //=.
    (* expnS  forall m n : nat, m ^ n.+1 = m * m ^ n *)
    rewrite expnS.
    Search _ "odd" in ssrnat.
    (* odd_mul  forall m n : nat, odd (m * n) = odd m && odd n *)
    rewrite odd_mul.
    rewrite IHn.
    case: (odd m) => //=.
    by rewrite Bool.orb_true_r.
Qed.

End Arithmetics.



Section Misc.
(** Exlpain why the following statement is unprovable *)

Definition const {A B} : A -> B -> A := fun a _ => a.

Lemma const_eq A B (x y : A) :
  @const A B x = const y -> x = y.
Abort.

End Misc.
