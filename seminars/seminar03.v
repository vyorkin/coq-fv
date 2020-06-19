From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section IntLogic.

(* Вот так надо искать (впихивая коэрции самостоятельно\явно) *)
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
        Undo.
        exists x. exact: px.
    + case=> q.
      case=> x px.
      by exists x.
      Undo.
      exists x.
      split.
      exact: q.
      exact: px.
      Undo 4.

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
      Undo.

      (* То же самое можно было бы записать проще:
         сначала утверждаем, что существует [x], затем
         предъявляем предикат (который выполняется) для этого [x]. *)
      exists x.
      split.
      - exact: q.
      exact: px.

  Restart.

  (* idiomatic solution *)

  split.
  - by case=> x [q px]; split=> //; exists x.
  by case=> [q [x px]]; exists x.
Qed.

Lemma exist_conj_commute A (P Q : A -> Prop) :
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  case=> x [px qx].
  split.

  exists x.
  exact: px.
  exists x.
  exact: qx.
  Undo 4.

  - exact: ex_intro P x px.
  exact: ex_intro Q x qx.

  Restart.

  by case=> [x [px qx]]; split; exists x.
Qed.

(* Locate "~".  Print not.  *) (* Логическое отрицание: A -> False *)
(* Locate "~~". Print negb. *) (* Вычислительное отрицание: bool -> bool *)

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
    + by exists true.
      Undo.
      exact: (ex_intro is_true true).
    + by exists false.
      Undo.
      exact: (ex_intro (not \o is_true) false).
  move=> b.
  case.
  rewrite /not.
  clear H.
  move=> eb H.
  exact: (H eb).

  Undo 6.
  by move=> b; case.

  Restart.

  move/(_ bool id not); case=> [|x [] //].
  by split; [exists true | exists false].
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
Proof. by move=> f x px; apply: f; exists x. Qed.

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
  rewrite /not_forall_exists /DNE /not.

  (* например, для биимпликации (IFF)
     [split=> [H1 | H2]] для каждой импликации помещает в контекст
     соответствующую ей предпосылку (левую или правую соответственно) *)
  split=> [nfe | dne].

  (* Если присмотреться к форме [nfe] (развернув not для наглядности),
     то видно, что там в некотором роде происходит снятие двойного отрицания:
     в предпосылку ~ (forall x : A, ~ P x) входят два отрицания,
     а в заключении (exists x : A, P x) их уже нет.

     Если мы сможем привести предпосылку [nfe] к снятию двойного отрицания,
     то мы сможем доказать её следствие -- существование x: [exists x : A, P x] *)

  - move=> P nnP.

    (* Подставим в параметр [nfe] типа [A] "тип истины" -- [True].
       Конечно, до этого нужно ещё догадаться, но истину можно
       тривиально сконструировать, а это уже наводит на мысли ;) *)

    (* Посмотрим на тип получившегося выражения *)
    Check (nfe True).

    (* В (nfe True) нужно какое-то утверждение [P : True -> Prop]
       из истины в [Prop], но [Prop] у нас есть, это [P],
       а истину всегда можно тривиально сконструировать *)

    Check (fun (I : True) => P).
    Check (nfe True (fun (I : True) => P)).

    (* Введём в нашу цель предпосылку для
       только что найденного "частного случая" гипотезы [nfe] *)
    move: (nfe True (fun I => P)).

    move=> H.
    (* А теперь заметим, что мы теперь можем
       сконструировать предпосылку гипотезы [H]:
       ((True -> (P -> False)) -> False)

       Истина у нас есть, это [I].
       Применив её мы получим [(P -> False) -> False].
       А вспомним, что для оставшейся части предпосылки
       у нас в контексте есть [nnP : ~ ~ P] *)

    case: (H (fun tnP => nnP (tnP I))).

    (* Тут можно использовать механизм "видов", тк:
       [case/H] ~ [move=> top. case: (H top)] *)

    Undo 2.

    case/(_ (fun tnP => nnP (tnP I))).

    + case.
      * done. Undo. exact: id.
      * move=> A P all_npx.
        (* Посмотрим на
           all_npx : ((forall x : A, (P x -> False)) -> False)
           Нам нужен [x : A], любой, где его взять? -- Нигде.

           Посмотрим на цель.
           Заметим, что в цели утверждение о существовании [x : A],
           для док-ва которого нужно предъявить [P x].

           Вспомним, что у нас есть вспомогательная лемма [curry_dep]:
           ((exists x, P x) -> Q) -> (forall x, P x -> Q)

           Наша цель немного отличается от формулировки данной леммы,
           а именно -- у нас нет [Q].
           Как же добавить [Q] и чем оно может быть?
           Самое простое соображение может быть, что [Q] это [False] и
           тогда нам нужно инвертировать цель.

           А теперь, посмотрим на [dne], заметим, что тут
           мы можем применить backwards reasoning, инвертируя цель. *)
        apply: dne.
        (* Вынесем гипотезу в контекст, a [all_npx] перетащим в цель *)
        move=> H.
        (* Отлично, если раскрыть определение [not], то мы увидим следующее:
           all_npx : (forall x : A, P x) -> False)
           Её предпосылка доказывает [False] в цели, применяем обратное рассуждение.*)
        apply: all_npx.

        (* Теперь мы можем воспользоваться леммой [curry_dep]:
           ((exists x, P x) -> Q) -> (forall x, P x -> Q)
           Опять же, backward reasoning, всегда помним об этом принципе. *)

        apply: curry_dep.

        (* А это и есть наша гипотеза [H]! *)
        exact: H.

  Restart.

  (* Теперь более идиоматичная запись этого доказательства: *)

  rewrite /not_forall_exists /DNE; split=> [nfe | dne].
  - move=> P nnP. move: (nfe True (fun _ => P)).
  by case/(_ (fun t_notP => nnP (t_notP I))).
  by move=> A P nAll; apply: dne=> /curry_dep/nAll.
Qed.

End IntLogic.


Section BooleanLogic.

(** [==] is decidable equality operation for types with dec. eq.
    In case of booleans it means [if and only if]. *)

(*
  [==] это перегруженная функция проверки на равенство
  ([eq_op] из модуля [eqtype]), а [=] это конструктор типов [eq].

  Конечно, [eq] и [eq_op] между собой связаны:
  [forall x y, x = y <-> x == y]
  ([x == y] здесь значит [x == y = true] из-за коэрции [is_true]).

  Между этими двумя представлениями можно переключаться при
  помощи вида [eqP]: если в голове цели находится [x == y], то
  [move/eqP] переключит голову на [x = y] и наоборот.

  Чтобы воспользоваться [eqP] нужно импортировать модуль [eqtype]. *)

Fixpoint mostowski_equiv (a : bool) (n : nat) :=
  if n is n'.+1 then mostowski_equiv a n' == a
  else a.

(* Т.е. у нас имеется некоторое количество равенств вида
   ((true == true ...) == true) == true
   или
   ((false == false ...) == false) == false
   в зависимости от [a : bool] у нас равенства
   между жителями [bool]: [true] или [false].
   Это количество равенств равно числу [n]. *)

(* ((a == a ...) == a) == a *)

Compute mostowski_equiv false 0. (* false *)
Compute mostowski_equiv false 1. (* false == false *-> true *)
Compute mostowski_equiv false 2. (* false == (false == false) *-> false == true *-> false *)

Compute (odd 0). (* false *)

Lemma mostowski_equiv_even_odd a n :
  mostowski_equiv a n = a || odd n.
Proof.
  (* Моё решение: *)

  elim: n=> [|n IHn].
  - by rewrite Bool.orb_false_r. (* b || false = b *)
    move=> /=.
    rewrite IHn. clear IHn.

  (* eqbF_neg b : (b == false) = ~~ b. *)
  case: a=> //=.
  rewrite eqbF_neg.

  Restart.

  (* Решение здорового человека: *)

  by elim: n=> [|n /= ->]; case: a=> //; rewrite eqbF_neg.
Qed.

End BooleanLogic.


Section Arithmetics.

Lemma addnCB m n : m + (n - m) = m - n + n.
Proof.
  Search _ (?m + (?n - ?m)) in ssrnat.

  rewrite -maxnE.

  (* Если посмотреть внутрь [rewrite /maxn.], то
     можно увидеть как это будет работать на натуральных числах:

     (if 2 < 3 then 3 else 2) = (2 - 3) + 3 <=>
                    3         =    0    + 3 <=>
                    3         = 3

     В результате вычитания натуральных чисел не может
     получиться отрицательное число.
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

  Restart.

  (* idiomatic solution *)
  by rewrite -maxnE maxnC maxnE addnC.
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


  Restart.

  by rewrite mulnBl !mulnDr addnC mulnC subnDl.
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

  Restart.

  by rewrite leq_subLR addnCA leq_addr.
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

  Restart.

  (* idiomatic solution: *)
  by elim: n=> //= n IHn; rewrite expnS odd_mul IHn orKb.
Qed.

End Arithmetics.


Section Misc.
(** Exlpain why the following statement is unprovable *)

Definition const {A B} : A -> B -> A := fun a _ => a.

(* [/] means "allow simplification after all the
   arguments before the slash symbol are supplied" *)
Arguments const {A B} a b /.

Lemma const_eq A B (x y : A) :
  @const A B x = const y -> x = y.
(** Explanation:
    If we had an inhabitant of type [B], i.e. some [b : B],
    we could apply [const x] and [const y] to [b], getting
    [x = y] after redusing the beta-redexes as follows: *)

have b: B by admit. (* assume we can construct [b] of type [B] *)

by move=> /(congr1 (@^~ b)).

(** [@^~ b] stands for (fun f => f b), i.e. application at [f].

    move/(congr1 (@^~ b))

turns an equality between two functions [f1] and [f2], i.e. [f1 = f2],
into the following equality [f1 b = f2 b] *)

(** Now, the problem here is that [B] is an
    arbitrary type, so it might be empty meaning we
    would never come up with a proof for the admitted goal. *)
Abort.

(* Если [B] пустой тип, то мы никогда не сможем "вызвать" [const],
   что необходимо сделать, чтобы сконструировать\предъявить
   нужные нам два соответствующих (равных) терма. *)

(** Yet another explanation of the above unprovability fact
    It is known that Coq's theory is compatible with the axiom of functional extensionality.
    This means that if we assume that axiom, then proving [const_eq] must not
    lead to a contradiction.
    Let's show this is not the case here.
 *)

Axiom fext : forall A (B : A -> Type) (f1 f2 : forall x, B x),
               (forall x, f1 x = f2 x) -> f1 = f2.

Lemma not_const_eq : ~ (forall A B (x y : A),
  @const A B x = const y -> x = y).
Proof.
move=> /(_ bool Empty_set false true) H.
apply/notF/H.
by apply: fext.
Qed.


End Misc.
