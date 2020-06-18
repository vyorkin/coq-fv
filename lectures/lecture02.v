From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.

Set Implicit Arguments.

Module Lect2.
  Section ProductType.

    (* Чтобы лучше разобраться как разные вещи работают "под
       капотом", мы делаем вид, что изначально у нас нет ничего
       в языке и мы начинаем всё самостоятельно постепенно
       добавлять. *)

    Inductive prod (A B : Type) : Type :=
      | pair of A & B.

    About pair.

    (* Without "Set Implicit Arguments" we have to pass types explicitly: *)
    (* Check pair nat bool 42 true : prod nat bool. *)

    Check pair 42 true : prod nat bool.

    Fail Check pair nat bool 42 true : prod nat bool. (* Inconvenient *)

    (* Оператор [@] локально отменяет вывод неявных аргументов. *)

    Check @pair nat bool 42 true.

    (* Писать везде [prod] не очень удобно, в Coq есть механизм
       нотаций, который позволяет динамически изменить парсер.
       Как только Coq встречает подобную запись, то он добавляет
       соотвествующее правило в некоторую свою таблицу
       грамматических правил. *)

    Notation "A * B" :=
      (prod A B) (at level 40, left associativity) : type_scope.

    (** Notation scopes *)

    Fail Check nat * bool.

    (* Нужно подсказать Coq'у, что это не оператор умножения, а
       тип произведения двух других типов. *)

    (* Например, это можно сделать вот так: *)

    Check (nat * nat)%type.

    (* Или так: *)

    Check (nat * nat) : Type.

    (* Ещё можно открыть скоуп и работать в нём. Последний
       открытый скоуп помещается на вершину стека и по умолчанию
       Coq будет считать, что мы работаем в нём. *)

    Open Scope type_scope.
    Check (nat * nat).
    Close Scope type_scope.
    Fail Check (nat * nat).

    Check ((nat * bool) * nat)%type.
    Check (nat * bool * nat)%type.

    (* У нас уже есть нотация для типов, теперь мы хотим нотацию
       для термов. Пробелы после открывающей и до закрывающей
       скобки обязательны *)

    Notation "( p ; q )" := (pair p q).

    (* Можно определять n-арные нотации *)

    Notation "( p , q , .. , r )" :=
      (pair .. (pair p q) .. r) : core_scope.

    Check (1, false) : nat * bool.

    Unset Printing Notations.
    Check (1, false) : nat * bool.
    Set Printing Notations.

    Definition fst {A B : Type} : A * B -> A :=
      (* fun p => match p with | pair a b => a end. *)
      (* fun p => let (a, b) := p in a. *)
      fun '(a, _) => a.

    Definition snd {A B : Type} : A * B -> B :=
      fun '(_, b) => b.

    Notation "p .1" := (fst p).
    Notation "p .2" := (snd p).

    Compute (true, 42).1.
    Compute (true, 42).2.

    Definition swap {A B : Type} : A * B -> B * A :=
      fun '(a, b) => (b, a).

    (* A /\ B -> B /\ A *)

  End ProductType.

  Check fst.
  Check snd.
  Check @pair _ _.

  Section IPL.

    (* Implication *)

    Definition A_implies_A (A : Prop) :
      A -> A :=
      fun proof_A : A => proof_A.

    Definition A_implies_B_implies_A (A B : Prop) :
      A -> B -> A := (* const *)
      fun proof_A => fun proof_B => proof_A.

    (* Conjunction *)

    Inductive and (A B : Prop) : Prop :=
      | conj of A & B.
      (* | conj (_ : A) (_ : B). *)

    Notation "A /\ B" := (and A B) : type_scope.

    Definition andC (A B : Prop) :
      A /\ B -> B /\ A :=
      fun '(conj proof_A proof_B) => conj proof_B proof_A.


    (* Можно переиспользовать одну и ту же нотацию в
       разных скоупах, но не идиоматично.

      Notation "a /\ b" := (conj a b).

      Definition andC' (A B : Prop) :
        A /\ B -> B /\ A :=
        fun '(proof_A /\ proof_B) => proof_B /\ proof_A.
    *)

    Definition andA (A B C : Prop) :
      (A /\ B) /\ C -> A /\ (B /\ C) :=
      fun '(conj (conj a b) c) => conj a (conj b c).

    (* Bi-implication, a.k.a. if and only if *)

    Definition iff (A B : Prop) : Prop :=
      (A -> B) /\ (B -> A).

    Notation "A <-> B" := (iff A B) : type_scope.

    Definition andA_iff (A B C : Prop) :
      (A /\ B) /\ C <-> A /\ (B /\ C) :=
      conj
        (fun '(conj (conj a b) c) => conj a (conj b c))
        (fun '(conj a (conj b c)) => conj (conj a b) c).

    (* Disjunction *)

    Inductive or (A B : Prop) : Prop :=
    | or_introl of A
    | or_intror of B.

    (* Максимально вставленные аргументы {A B} отличаются от
       не максимально вставленных тем, что даже если конструктор типа
       ни к чему не применяется, то они всё равно считаются "вставленными". *)

    Arguments or_introl {A B} a, [A] B a.
    Arguments or_intror [A B] b, A [B] b.

    Notation "A \/ B" := (or A B) : type_scope.

    (* Если отключить максимально вставленные аргументы
       [Arguments or_introl {A B} a], то Coq не сможет вывести правильный тип,
       тк конструктор явно ни к чему не применяется.
       Чтобы подсказать ему контекст [A -> A \/ B] для вывода типа
       в данном случае можно использовать "максимально вставленные аргументы". *)
    Definition left' (A B : Prop) : A -> A \/ B
      := or_introl.

    Definition left'' (A B : Prop) : A -> A \/ B :=
      fun a => or_introl a.

    Definition right' : forall (A B : Prop), B -> A \/ B :=
      or_intror.

    Compute (left' True).
    Compute (right' False).

    Definition or1 (A B : Prop) :
      A -> A \/ B :=
      fun proofA => or_introl proofA.
      (* @or_introl A B. *)

    Definition orC A B :
      A \/ B -> B \/ A :=
      fun a_or_b =>
        match a_or_b with
        | or_introl proofA => or_intror proofA
        | or_intror proofB => or_introl proofB
        end.

    (*
    Definition orBad A B :
      A \/ B -> A :=
      fun a_or_b =>
        match a_or_b with
        | or_introl proofA =>  proofA
        | or_intror proofB => ?proofA?
        end.
    *)

    Definition or_and_distr A B C :
      (A \/ B) /\ C -> (A /\ C) \/ (B /\ C) :=
      fun '(conj a_or_b c) =>
        match a_or_b with
        | or_introl a => or_introl (conj a c)
        | or_intror b => or_intror (conj b c)
        end.

    (* Кодируем ложное утверждение:
       Это утверждение, которое невозможно сконструировать\построить.
       В нём 0 конструкторов, что показывает точка в определении. *)
    Inductive False : Prop := .

    (* Кодируем истинное утверждение.
       Истина это некоторое утверждениe, которое можно доказать тривиально.
       Мы всегда-всегда можем доказать истину, ну она просто есть.
       Чтобы её "предъявить" у нас есть единственный
       конструктор, который называется [I]. *)
    Inductive True : Prop := | I.

    (* Например, если мы хотим доказать истину,
       то наше доказательство будет выглядеть следующим образом: *)
    Definition t : True := I.
    (* Т.е. мы знаем как его построить --
       тривиально, используя единственный конструктор. *)

    (* Аналогично, истина И истина. *)
    Definition t_and_t : True /\ True := conj I I.

    (* Ложное утверждение или отрицание утверждения это
       просто ф-ция, которая принимает некоторое утверждение и
       возвращает то, что нельзя сконструировать. Сечёшь, да? ;) *)
    Definition not (A : Prop) := A -> False.

    Notation "~ A" := (not A) : type_scope.

    Definition A_implies_not_not_A (A : Prop) :
      A -> ~ ~ A := (* A -> ((A -> False) -> False) *)
      fun a => fun not_a => not_a a.

    (* DNE (Double negation elimination) is
       not provable in Intuitionistic Logic *)
    Fail Definition DNE (A : Prop) :
      (* Подчёркивание это что-то типа [Fail],
         позволяет нам пройти дальше, несмотря на ошибку. *)
      ~ ~ A -> A := fun nna => __. (* can't call [nna] *)

     (* Если развернуть нотацию отрицания, то видим, что у нас есть
        ((A -> False) -> False) -> A
        Это означает, что нам нужно сконструировать терм типа [A].
        Чтобы это сделать, нам нужно "не А":
        (A -> False), которого у нас нет. *)

    (* ELM (Law of excluded middle) is equivalent to
       DNE so it isn't provable either *)
    Fail Definition LEM (A : Prop) :
      (* A \/ (A -> False) *)
      A \/ ~A := __.
      (* Имея произвольное [A] мы не можем доказать ложь [False]. *)
      (* or_intror (fun a : A => ?False) *)

  End IPL.

  Section Propositional_Equality.

    (* Тип пропозиционального равенства *)

    (* Indexed data type (or a type family -- many different types),
       the first parameter is fixed, the second parameter occurs to the
       right hand side of the ":", it is called a type index and
       it is allowed to vary between different constructors of the inductive type.
       --
       Similar to GADT *)
    Inductive eq (A : Type) (a : A) : A -> Prop :=
    | eq_refl : eq a a.
 (* | eq_refl1 b : eq b b. -- invalid *)
 (* | eq_refl2 b : eq a b. -- correct *)

    (* Типы  это утверждения *)
    (* Термы это доказательства *)

    About eq.
    About eq_refl.

    (* Если ты не понял всё, что написано выше,
       то вот как это понимаю я:

    У нас есть тип [eq (A : Type) (a : A) : A -> Prop], он
    - параметризован некоторым типом (A : Type)
    - значением этого типа [a : A] и
    - индексирован некоторым [A] (стоит справа от ":")

    Так вот, типов таких существует дофига, например:
    - @eq nat 1 1.
    - @eq nat 3 2.
    - @eq nat 9 4.

    Но вот сконструировать жителей последних двух
    типов у тебя не получится. Чтобы понять почему --
    глянь на конструктор eq: [eq_refl : eq a a].
    Т.е. там одинаковые буковки: [eq a a].
    У нас есть один единственный конструктор [eq_refl],
    который конструирует значение типа [eq] и он накладывает
    очень важное ограничение -- параметр типа и
    его индекс должны совпадать, а иначе тип не сконструируешь.
    Это похоже на хаскельные GADTs. *)

    (* Например, вот такой тип есть *)
    Check @eq bool false true.
    (* Но жителя этого типа создать нельзя, тк
       [eq_refl false] это конструктор типа [@eq bool false false]. *)
    Fail Check eq_refl false : @eq bool false true.

    (* Аналогично и здесь *)
    Check @eq nat 1 1.
    Check eq_refl 1 : @eq nat 1 1.
    Check eq_refl 2 : eq 2 2.
    (* Первый параметр типа неявный, а второй явный. *)
    Fail Check eq_refl 1 : eq 1 2.
    (* ^^ The term [eq_refl 1] as type [eq 1 1] while
           it is expected to have type [eq 1 2] *)
    Check @eq nat 1 2.
    Check eq_refl 1 : @eq nat 1 1.

    Notation "a = b" := (eq a b) : type_scope.

    Definition eq_reflexive A (x : A) :
   (* x = x := eq_refl x. *)
      eq x x := eq_refl x.

    (* Inductive eq (A : Type) (a : A) : A -> Prop := *)
    (* | eq_refl : eq A a a. *)

    Definition eq_sym A (x y : A) :
    (* x = y -> y = x := *)
      eq x y -> eq y x :=
      fun proof_x_eq_y =>
        match proof_x_eq_y with
        | (* x = y *) eq_refl => (* y := x *) eq_refl x
     (* |             eq_refl =>              eq_refl x : eq x x *)
        end.

    (* Experiments *)

    Inductive bad_eq (A : Type) (a : A) (b : A) : Prop :=
      | bad_eq_refl : bad_eq a b.

    About bad_eq.
    Check bad_eq_refl 1 2 : bad_eq 1 2.

    Inductive bad_eq' (A : Type) : A -> A -> Prop :=
      | bad_eq_refl' a : bad_eq' a a.

    About bad_eq'.

    Check bad_eq_refl' 1 : bad_eq' 1 1.
    Fail Check bad_eq_refl' 1 : bad_eq' 1 2.

    Check bad_eq'_ind.
    Check eq_ind.

    Definition bad_eq'_sym A (x y : A) :
      bad_eq' x y -> bad_eq' y x :=
      fun prf =>
        match prf with
        | bad_eq_refl' x => bad_eq_refl' x
        end.

    Definition eq_trans A (x y z : A) :
      x = y -> (y = z -> x = z) :=
      fun x_eq_y : x = y =>
        match x_eq_y with
     (* | eq_refl => ??? : y = z -> x = z *)
     (* | eq_refl => ??? : x = z -> x = z *)
        | eq_refl => id
        end.

    (* Cм. коментарии к [eq_sym'] нижe и
       Coq-чатик в телеге (поиск по eq_trans_ann) *)

    Definition eq_trans_ann A (x y z : A) :
      x = y -> (y = z -> x = z) :=
      fun x_eq_y : x = y =>
        match
          x_eq_y in (_ = b)
          return (b = z -> x = z) with
        | eq_refl => fun (prf_xz : x = z) => prf_xz
        end.

    Definition eq_bar (x y z : nat) :
      x = y + z -> x + z = (y + z) + z :=
      fun x_eq_y_plus_z : x = y + z =>
        match x_eq_y_plus_z with
        | eq_refl => eq_refl (x + z)
        end.

    Definition eq_sym' A (x y : A) :
      x = y -> y = x :=
      fun (prf_xy : x = y) =>
        match
          (* Это примерно [prf_xy : (_ = b)]
             [b] это новое имя для [y] и
             [b] является связанной переменной дальше *)
          prf_xy in (_ = b)
          (* подчеркивание в [(_ = b)] - это обязательно,
             т.к. [x] - это параметр и меняться не может *)
          (* мы возвращаем все тот же [y = x],
             но с учетом переименования в [b] *)
          return (b = x) with
        | eq_refl =>
          (* Внутри матч-выражения [b] идентичен [x] и
             возвращаемый тип из [b = x] превращается в [x = x] *)
          eq_refl x
      end.

    Definition eq_foo (x y z : nat) :
      x + y = y + z -> ((x + y) + z = (y + z) + z) :=
      fun prf_eq : x + y = y + z =>
        (* x + y = x + y -> ((x + y) + z = (x + y) + z) := *)
        match prf_eq with
     (* | eq_refl => eq_refl ??? : (x + y) + z = (y + z) + z *)
        | eq_refl => eq_refl ((x + y) + z)
        end.

    Definition eq_foo_ann (x y z : nat) :
      x + y = y + z -> ((x + y) + z = (y + z) + z) :=
      fun prf_eq : x + y = y + z =>
        match
          prf_eq in (_ = b) (* x + y = b *)
       (* Аннотация типа возвращаемого типa заматченного выражения.
          В нужную часть типа подставляем связанную типовую переменную [b]:
          return ((x + y) + z = (y + z) + z)
                                   ^
                                   b
                                 x + y
       *)
          return ((x + y) + z = b + z) with
        | eq_refl => eq_refl ((x + y) + z)
        end.

    Inductive foo (A : Type) (a : A) : A -> A -> Prop :=
      | foo_ctor : foo a a a.

    Definition foo_blah A (x : A) :
      foo x x x := foo_ctor x.

    Lemma A_implies_A' (A : Prop) :
      A -> A.
    Proof. (* <-- optional *)
      Show Proof. (* (fun A : Prop => ?Goal) *)
      move=> a.
      (* Когда мы это написали, по сути мы сказали следующее: *)
      (* fun a => ??? *)
      (* Т.е. что у нас есть ф-ция от переменной [a],
         тело которой следует после точки. *)
      Show Proof. (* (fun (A : Prop) (a : A) => ?Goal) *)
      exact: a.
      Show Proof.
      Undo 2.
      by [].
    Qed.

    (* Язык тактик можно применять, чтобы писать код.
       Код и доказательства это одно и тоже. *)

    Lemma or_and_distr' A B C :
      (A \/ B) /\ C -> A /\ C \/ B /\ C.
    Proof.
      case. (* делает паттерн-матчинг *)
            (* "case" по сути тоже самое, что и "move=> []" *)
      Show Proof.
      case.
      (* Show Proof. *)
      - move=> a c.
        left.  (* доказываем/строим (конструктор) [or_introl] *)
               (* нам нужно доказать/построить и [A] и [C]    *)
        (* можно либо сразу построить терм конъюнкции,
           либо разбить цель на 2 подцели, применив тактику [split] *)
        split. (* разбиваем это на 2 подцели тактикой [split] *)
               (* и строим каждое док-во/терм отдельно *)
        + exact: a.
          exact c. (* тут [+] не ставим (тк этo последняя ветка) *)
      - move=> b c.
        right.
        split.
        + exact b.
          apply c. (* [exact] и [apply] - синонимы *)
    Qed.
    (* Когда мы пишем [Defined], то тело
       доказательства становится достуным тайпчекеру (прозрачным).
       Позволяет управлять производительностью.
       Прозрачные определения\док-ва позволяют "считать" с их помощью. *)
    (* Defined. *)
    About or_and_distr'.

    Lemma or_and_distr'' A B C :
      (A \/ B) /\ C -> A /\ C \/ B /\ C.
    Proof.
      (* Делает паттерн-матчинг по голове\вершине стека *)
      (* Здесь квадратные скобочки это по сути это аналог [case] *)
      move=> [].
      Undo.
      (* Можно сразу переносить в контекст *)
      move=> [a_or_b c].
      Undo.

      (* Соответственно вложенные квадратные скобки это вложенный [case].
         Здесь будут созданы 2 подцели. *)
      move=> [[a | b] c].
      Restart.

      (* Подцели можно сразу доказывать, указывая док-ва (для каждой
         подцели, в соотв. порядке) в следующем выражении в кв. скобках *)

      (* Тактикал [;] применяет каждую из тактик
         справа к соответствующей подцели слева. *)
      by move=> [[a | b] c]; [left | right].

      (* В данном случае термы, доказывающие цели уже будут находиться в
         контексте после паттерн-матчинга, поэтому док-во тривиально с помощью [by]. *)
    Qed.

    Section HilbertSaxiom.

      Variables A B C : Prop.

      Lemma HilbertS :
        (A -> B -> C) -> (A -> B) -> A -> C.
      Proof.
        move=> hAiBiC hAiB hA.
        (* Можно построить пруф-терм сразу *)
        exact: (hAiBiC hA (hAiB hA)).
        Undo.
        move: hAiBiC.
        (* A -> B -> C
                     C *)
        apply.
        (* - exact hA. move: hA. exact hAiB. *)
        - by [].
        move: hAiB.
        apply.
        by [].
        Undo 3.
        exact: (hAiB hA).
        Undo.
        by apply: hAiB.
      Qed.

    End HilbertSaxiom.

    (* Alternative proof *)
    Section HS2.
      Variables A B C : Prop.
      Hypotheses (hAiBiC : A -> B -> C) (hAiB : A -> B) (hA : A).

      Lemma HilbertS': C.
      Proof.
        (* apply [hAiBiC] and apply [hA] only to the first subgoal
           generated by the [hAiBiC].
        *)
        apply hAiBiC; first by apply: hA.
        (* If the tactical [first], which is called a
           selector, were not written, the system would attempt to perform
           [apply: hA] in both subgoals, and would fail on the second subgoal. *)
        exact: hAiB.
        Undo 1.
        move: hAiB. apply. exact hA.
        Undo 1.
        move: hAiB. exact.
        (* Terminator [exact] is a sort of combination between [apply] and [by []]. *)
      Qed.

      Lemma HilbertS'': C.
      Proof. by apply: hAiBiC; last exact: hAiB. Qed.

      Check hAiB hA.
      Check (hAiBiC hA) (hAiB hA).
      Check hAiBiC hA (hAiB hA).

      Lemma HilbertS''': C.
      Proof.
        exact: hAiBiC hA (hAiB hA). Undo 1.
        exact: hAiBiC _ (hAiB _). Undo 1.
        exact: hAiBiC (hAiB _).
      Qed.

      Print HilbertS.
      Check HilbertS.

      Print HilbertS''.
      Print HilbertS'''.

      Print HilbertS'.
      Check HilbertS'.
    End HS2.

    Print HilbertS'.
    Check HilbertS'.

    Section Rewrite.

      Variable A : Type.

      Implicit Types x y z : A.

      Lemma eq_reflexive' x :
        x = x.
      (* Proof. exact: (eq_refl). Qed. *)
      Proof. by []. Qed.

      Lemma eq_sym'' x y :
        x = y -> y = x.
      Proof.
        move=> x_eq_y.
        rewrite x_eq_y.
        done.
        Undo 2.
        rewrite -x_eq_y.
        by [].
        Show Proof.
      (* QED. *)
      Defined.

      (* Мы использовали выше Defined, тк он
         позвляет заглянуть в структуру пруф-терма. *)

      Eval compute in eq_sym''.

      Lemma eq_sym_shorter x y :
        x = y -> y = x.
      Proof.
        by move=> ->.
      Qed.

      Lemma eq_trans' x y z :
        x = y -> y = z -> x = z.
      Proof. move=> ->. by apply. Qed.
      (* Proof. move=> ->. move=> ->. by []. Qed. *)
      (* Proof. move=> ->->. by []. Qed. *)
      (* Proof. move=> ->->. apply: eq_reflexive'. Qed. *)
      (* Proof. move=> a; rewrite a; clear a; by apply. Qed. *)
      (* Proof. move=> ->. apply id. Qed. *)

    End Rewrite.

  End Propositional_Equality.

End Lect2.
