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

    Print erefl.
    Print Logic.eq_refl.

    Check erefl : predn_dep 7 = 6.
    Compute predn_dep 7.
    Fail Check erefl : predn_dep 0 = 0.
    Check predn_dep 0 : unit.
    Check predn_dep 0 : Pred 0.
    Check predn_dep 7 : nat.

    Check erefl : predn_dep 0 = tt.
    Check erefl : Pred 0 = unit.

    (** ** Annotations for dependent pattern matching *)

    (** Type inference is undecidable *)

    (* Тут мы просим вывести ф-цию над типами,
       а это алгоритмически не разрешимая задача. *)
    Fail Check (fun n => if n is S n' then n' else tt).

    Check (
        fun n =>
          if n is S n' as n0 return Pred n0
          then n'
          else tt).

    (**
    General form of pattern matching construction:
    [match expr as T in (deptype A B) return exprR].

    - [return exprR] denotes the dependent type of the expression
    - [as T] is needed when we are matching on complex expressions,
    not just variables
    *)

    (* Functional type is just a notation *)
    (* for a special case of [forall] *)

    (*
       "A -> B" := forall _ : A, B
       Это зависимая ф-ция, в том случае, когда возвращаемый тип
       никак не зависит от входного значения.

       Это нотация из стандартной библиотеки, которая означает:
       для неважно какого значения из типа [A] мы всегда
       возвращаем один и тот же тип [B].
    *)
    Locate "->".

    (* Следующие записи эквивалентны *)
    Check predn : nat -> nat.
    (* Мы можем назвать как-то входное значение в типе ф-ции, но
       [Check] распечатает без него, тк в выходном типе оно никак не используется *)
    Check predn : forall _ : nat, nat.
    (* Аналогично *)
    Check predn : forall x : nat, (fun _ => nat) x.

  End Motivation.

  (** * Usage of [forall] in standalone expressions *)

  Section StandardPredicates.
    Variable T : Type.
    Implicit Types (op add : T -> T -> T).

    Definition associative op :=
      forall x y z, op x (op y z) = op (op x y) z.

    Definition left_distributive op add :=
      forall x y z, op (add x y) z = add (op x z) (op y z).

    Definition left_id e op :=
      forall x, op e x = x.
  End StandardPredicates.

  (* Закон исключённого третьего влечёт
     за собой дуальноe правило Фробениуса *)

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
      + move=> q.
        left.
        exact q.
      + move=> nq.
        right.
        move=> x.
        Check all_qpx x.
        case: (all_qpx x).
        Undo.
        move: (all_qpx x).
        case.
        (* Check nq : Q -> False. *)
        (* Конструкция "вид" [move/H] это приблизительный аналог
           [move=> top. move: (H top)]

           Соотвественно это работает и с [case/H],
           что будет эквивалентно [move=> top. case: (H top)] *)
        * move/nq.
          Undo.
          move=> q. move: (nq q).
          done.
        * by [].
    (* case. *)
    (* - move => q x. *)
    (*   left. *)
    (*   exact: q. *)
    (* - move => all_qpx x. *)
    (*   right. *)
    (*   exact: all_qpx x. *)
    case; first by move=> q x; left.
    move=> all_px x.
    right. exact: all_px.
    Undo 2.
    by right.
  Qed.

  (* Давайте докажем, что это работает и в обратную сторону *)

  Lemma Frobenius2_lem : Frobenius2 -> LEM.
  Proof.
    rewrite /Frobenius2=> frob.
    rewrite /LEM. Undo.
    (* Поскольку мы знаем определение [LEM], то
       мы можем сразу ввести [P] в контекст и
       Coq развернёт определение автоматически *)
    move=> P.
    (* rewrite /not. *)
    Check (frob P (fun _ => False) P).
    (* frob : forall (A : Type) (P : A -> Prop) (Q : Prop), *)
    (*        (forall x : A, Q \/ P x) <-> Q \/ (forall x : A, P x) *)
    (* frob P (fun _ : P => False) P *)
    (*      : (P -> P \/ False) <-> P \/ (P -> False) *)
    case: (frob P (fun _ => False) P).
    (* Переносим в контекст первые два, но
       второе пропускаем и сразу возвращаем первое в цель *)
    move=> H _; move: H.
    (* [apply.] это "дефективная форма" тактики [apply],
       что значит по сути "использование тактики без модификаторов" *)
    apply. move=> x. left. exact: x.
    Undo 4.
    (* Т.е. получается, что [left]/[right] переносит
       всё до первой дизъюнкии в контекст? Да.
       Это плохо. Способ выше -- правильный *)
    apply. left. exact: x.
    Undo 3.
    by apply; left.
  Qed.

  Module MyExistential.

    Inductive ex_my (A : Type) (P : A -> Prop) : Prop :=
    (* Кодируем introduction rule (правило ввода) следующим образом:
       конструктор "содержит" 2 значения:
       некоторый [x : A] и док-во, что [P x] выполняется
       (на самом деле -- просто некоторое утверждение, параметризованное [x],
       "выполняется" это всего лишь наша интерпретация, оно может и не выполняться,
       но в таком случае система станет противоречивой, что станет понятно позже) *)
    | ex_intro (x : A) (proof : P x).

    (* ex_intro [предикат] [значение] [доказательство, что предикат выполняется на этом значении] *)

    (* Если у нас написано, что существует [x] для
       которого выполняется [P x], то мы имеем дело с некой парой.
       Для того, чтобы воспользоваться этой парой мы должны сделать
       по ней pattern-matching типа [case x px] и получим в контексте 2 значения.
       Зависимая типизация тут это ключевая особенность. *)

    (* В Coq уже есть [ex], определение выше нужно было просто,
       чтобы посмотреть как оно устроено под капотом. *)

    (** Simplified notation *)
    Notation "’exists’ x : A , p" :=
      (ex (fun x : A => p))
        (at level 200, right associativity).

    (** Full-blown notation: multiple binders *)
    Notation "'exists' x .. y , p" :=
      (ex_my (fun x => .. (ex_my (fun y => p)) ..))
        (at level 200, x binder, right associativity,
         format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
      : type_scope.

    Print ex_my.
    Print ex.

  End MyExistential.

  (* Т.е. если существует [x] для которого утверждение истинно,
     то не для всех [x] оно не истинно. *)
  Lemma exists_not_forall A (P : A -> Prop) :
    (exists x, P x) -> ~ (forall x, ~ P x).
  Proof.
    case=> x px.
    move=> all.
    Check (all x).
    exact: (all x px).
  Qed.

  (* Можно имитировать обычную пару при помощи exists:
     A /\ B
     exists _ : A, B

     Т.е. существует некоторое
     утверждение _ (которое мы никак не именуем) типа [A]
     и утверждение типа [B].

     Если ты совсем тупой (как я), то
     попробуй посмотреть на подстановку:

     Notation "’exists’ _ : A, B" :=
      (ex (fun x : A => B))
        (at level 200, right associativity).
  *)

  (* Definition curry' {A B C} : *)
  (*   (A * B -> C) -> (A -> B -> C) := *)
  (*   fun f => (fun a b => f (a; b)). *)

  Definition curry {A B C} :
    (A * B -> C) -> (A -> B -> C).
  (* Не будем тут писать слово [Proof], тк тут мы
     имеем ввиду некую вычислительную сущность, а не док-во *)
  move=> f a b.
  (* exact: (f (pair a b)). *)
  exact: (f (a, b)).
  (* Используем Defined, тк мы хотим уметь считать при помощи этой ф-ции. *)
 Defined.

  Lemma curry_dep A (P : A -> Prop) Q :
    ((exists x, P x) -> Q) -> (forall x, P x -> Q).
  Proof.
    move=> f x px.
    (* Print ex_intro. *)
    (* ex_intro : forall x : A, P x -> exists y, P y *)
    exact: (f (ex_intro P x px)).
  Qed.

  Section Symmetric_Transitive_Relation.
    (* У нас есть некоторое отношение [R] над типом [D] *)
    Variables (D : Type) (R : D -> D -> Prop).

    (* [Hypothesis] is a different syntax for [Variable] *)

    (* Отношение симметрично *)
    Hypothesis Rsym :
      forall x y, R x y -> R y x.

    (* Отношение транзитивно *)
    Hypothesis Rtrans :
      forall x y z, R x y -> R y z -> R x z.

    (* Если нам известно про некое соотношение,
       в котором есть хотя бы одна пара (оно не пустое),
       то такое отношение ещё и рефлексивно, т.е. любой [x]
       находится в отношении [R] с самим собой. *)
    Lemma relf_if :
      forall x : D, (exists y, R x y) -> R x x.
    Proof.
      move=> x.
      case=> y rxy.
      move: (Rsym rxy).
      move: rxy.
      apply: Rtrans.
    Qed.

  End Symmetric_Transitive_Relation.

  Lemma exfalso_quodlibet :
    False -> forall P : Prop, P.
  Proof. by []. Qed.

  (* Импликация это ф-ция, которая принимает [f : False] и
     производит некоторую ф-цию, которая принимает
     произвольное утверждение [P] и производит его доказательство. *)
  Definition exfalso_quodlibet_term :
    False -> forall P : Prop, P :=
    fun f =>
      (* Поскольку [False] это индуктивный тип, то
         по его значениям можно паттерн-матчить.
         А конструкторов у нас 0, столько и запишем :) *)
      match f with end.

  (* Частный случай *)
  Lemma False_implies_false :
    False -> false.
  Check false : Type.
  Print false.
  Set Printing Coercions.
  (* Set Printing All. *)
  rewrite /is_true.
  (* Теперь мы видим, что на самом деле от нас требуется доказать, что:
     False -> false = true

     Мы тут видим [false = true], потому что
     is_true = fun b : bool => eq b true : forall _ : bool, Prop

     Вообще говоря, у нас это не тайпчекается,
     потому что здесь должен быть тип.

     Коэрции это такой способ реализовать в Coq подтипирование.
     Поскольку в теории типов, на которой основан Coq подтипирования нет,
     то это реализовано при помощи такого мета-механизма.
     Как только Coq видит, что есть некий терм, который
     не проходит проверку типов (у нас это [false = true]),
     то он ищет в своей базе коэрций способ преобразовать его так,
     чтобы он тайпчекался. В нашем случае наиболее простой выход,
     который он находит это использовать [is_true].

     False -> is_true false

     forall _ : False, @eq bool false true
  *)
  Proof. case. Qed.

  (* Вот так, например, определена коэрция [is_true]: *)
  Unset Printing Notations.
  Print is_true.
  Set Printing Notations.

  (* Coercion is_true : bool >-> Sortclass. *)
  (* Print Coercions. *)

  (* Going in the other direction *)
  Lemma false_implies_False :
    false -> False.
  Proof. by []. Qed.

  Check I : True.

  (* Чтобы разобраться что происходит под капотом,
     можно построить следующий пруф-терм: *)
  Definition false_implies_False_term :
    false -> False :=
 (* Раскроем коэрцию: *)
 (* fun eq : false         => *)
 (* fun eq : is_true false => *)
    fun eq : false = true  =>
      (* тут false не меняется, а true меняется (тк это индекс) *)
      (* [in] это по сути [:],
         т.е. это нужно читать как [eq : eq _ b]*)
      match eq in (_ = b)
            return (if b then False else True)
      (* до паттерн-матчинга:
            return True *)
      (* после паттерн-матчинга:
            return False *)
      with
      | erefl => I : True
      end.

  (* See:
     https://coq.inria.fr/refman/addendum/extended-pattern-matching.html#dependent-pattern-matching
     https://github.com/coq/coq/wiki/MatchAsInReturn.

     [match] allows the result type to depend on both
     the input value, and the parameters of the input type. *)

  (* Все параметры индуктивного типа заменяются на _,
     а всем индексам можно дать имена *)

  (* fun     eq : false = true => *)
  (*   match eq : (_    = b) *)


  (* Injectivity of constructors *)

  Lemma succ_inj n m :
    S n = S m -> n = m.
  Proof.
    case. (* special case for [case] *)
    (* Тактика [case] работает специальным образом в таком случае.
       Если мы на таком равенстве с конструкторами используем её, то
       она нам преобразует в соотв. форму -- "распаковывает" конструкторы.
     *)
    Show Proof.
    done.
  Qed.

  Lemma pair_inj A B (a1 a2 : A) (b1 b2 : B) :
    (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2).
  Proof.
    case.
    move=> H1 H2.
    rewrite H1.
    rewrite H2.
    by [].

    Restart.

    case.
    move=> ->->.
    by [].

    Restart.

    by case=> ->->.
  Qed.

    Lemma addnA :
      associative addn.
    Proof.
      (* Мы знаем определение ассоциативности,
         поэтому можем сразу переместить x, y и z в контекст и
         Coq поймёт, что нужно развенуть определение *)

      Eval hnf in associative addn.

      move=> x y z.
      (* Есть такая эвристика, что если ф-ция определена рекурсивно по
         1-му аргументу, то идукцию следует тоже делать по 1-му аргументу.

         Индукция есть в некотором смысле символическое вычисление. *)

      elim: x.
      - by [].

      (* Мы хотим избавляться от таких тривиальных целей,
         как в первом случае. Это можно сделать при помощи
         флага [//], который делает тоже самое, что и [by []]. *)
      Undo 3.

      elim: x=> //.
      Undo 1.

      elim: x.
      have : 0 + 1 = 1.

      Print addn.
      (* Модификатор [/=] запускает классическую тактику [simpl],
         которая двойные определения не разворачивает:
         [addn = nosimpl addn_rec] *)

      (* Set Printing All. *)
      (* rewrite /addn. *)
      move=> /=.
      (* Unset Printing All. *)
      done.

      Restart.

      move=> x y z.
      elim: x=> // x IH.
      Search _ (_.+1 + _).
      rewrite addSn.
      rewrite IH.
      done.

      Restart.

      by move=> x y z; elim: x=> // x IH; rewrite addSn IH.
    Qed.

    Lemma add0n :
      left_id 0 addn.
    Proof.
      (* Это просто вычисляется (по определению суммы [add_n]) *)
      rewrite /left_id.
      by [].
    Qed.

    Lemma addn0 :
      right_id 0 addn.
    Proof.
      rewrite /right_id.
      (* А вот тут уже только по индукции *)

      elim.
      - by [].
      - move=> n IHn.
        About addSn.
        rewrite addSn.
        rewrite IHn.
        done.

      Restart.

      move=> x.
      elim: x=> // x IHn.

      Restart.

      by elim=> // x IH; rewrite addSn IH.
    Qed.

    Lemma addSnnS m n :
      m.+1 + n = m + n.+1.
    Proof.
      elim: m=> //.
      move=> m IH.
      rewrite addSn IH.
      done.

      Restart.

      by elim: m=> // m IH; rewrite addSn IH.
    Qed.

    Lemma addnC :
      commutative addn.
    Proof.
      move=> x y.
      elim: x.
      - rewrite addn0. done.
      - move=> n IHn.
        rewrite addSn.
        rewrite -addSnnS.
        rewrite IHn.
        rewrite addSn.
        done.

      Restart.

      move=> x y.
      elim: x; first by rewrite addn0.
      by move=> x IHn; rewrite addSn IHn -addSnnS.
    Qed.

    Check nat_ind.

    (* Определим элиминатор индукции.
       В теории типов индукция кодируется через рекурсию,
       т.е. у нас нет отдельно рекурсии и отдельно индукции. *)

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
