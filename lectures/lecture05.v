From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*** [reflect] predicate *)

Section MotivationalExample.

Variable T : Type.

Variable p : pred T.
Print pred.
Check p : T -> bool.

Lemma all_filter (s : seq T) :
  all p s -> filter p s = s.
Proof.

(* Notation "[ 'seq' x <- s | C ]" := (filter (fun x => C) s) *)

(* Print all. *)
(* Print filter. *)

elim: s=> //= x s IHs.
rewrite /is_true.
(* About andP. *)
move=> /andP.
(* Set Printing Coercions. *)
rewrite /is_true.
move=> [].
move=> ->.
move/IHs. (* move=> top. move: (IHs top). *)
move=>->.
done.

Restart.

by elim: s => //= x s IHs /andP[-> /IHs->].
Qed.

End MotivationalExample.


(** How does [andP] from above work? *)

About andP.

Print reflect.
Print Bool.reflect.

(* Таким образом кодируем соответствие между
   [Prop] (логическими утверждениями) и типом [bool] *)

(**
    Inductive reflect (P : Prop) : bool -> Set :=
    | ReflectT :   P -> reflect P true
    | ReflectF : ~ P -> reflect P false
 *)

Search _ reflect.

(** First, let us show that [P] if and only if [b = true]
    as two separate lemmas *)

Lemma introT_my (P : Prop) (b : bool) :
  reflect P b -> P -> b -> b.
Proof.
  (* Set Printing Coercions. *)
  (* rewrite /is_true. *)
  (* Unset Printing Coercions. *)
  case.
  - move=> _ _.
    done.
    move=> np.
    move=> top.
    exact: id.
    Undo.
    move: (np top).
    Undo 2.
    move/np.
    (* Конструкторов у False нет, поэтому это доказывается
       просто вот так (разбором всех конструкторов, которых нет): *)
    case.
Qed.

About introTF.
About elimTF.

Lemma elimT_my (P : Prop) (b : bool) :
  reflect P b -> b -> P.
Proof.
  case.
  - move=> p _. exact: p.
    move=> _.
    done.
    (* [done] uses the [discriminate] tactic under the hood *)
    Undo.
    (* The discriminate tactic proves that different
       constructors of an inductive type cannot be equal.
       In other words, if the goal is an inequality consisting of
       two different constructors, discriminate will solve the
       goal. Discriminate also has another use: if the context
       contains a equality between two different constructors
       (i.e. a false assumption), you can use discriminate to prove any goal.
       https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html#discriminate
       *)
    discriminate.
Qed.

(** Essentially, a [reflect] predicate connects
    a _decidable_ proposition to its decision procedure.
 *)
Lemma reflect_lem P b :
  reflect P b -> P \/ ~ P.
Proof.
  (* case. *)
  case=> H.
  - left. exact: H.
  - right. exact: H.
  Restart.

  by case=> H; [left | right].
Qed.

(** Lets look at some standard [reflect] predicates *)

Lemma andP_my (b c : bool) :
  reflect (b /\ c) (b && c).
Proof.
  (* Locate "/\". *)
  (* Locate "&&". *)
  About and.
  (* About andb. *)
  (* Set Printing Coercions. *)
  (* Check (is_true b). *)
  case b.
  - case c=> /=.
    (* Тактика [constructor] подбирает тот конструктор,
       который нужен в данном контексте. В данном случае конструктор
       можно восстановить единственным образом. *)
    + constructor. by [].
    + constructor. by case.
    + case c=> /=.
      * constructor. by case.
      * constructor. by case.

  Restart.

  by case: b; case: c; constructor=> //; case.
Qed.


Lemma orP_my (b c : bool) :
  reflect (b \/ c) (b || c).
Proof.
  case b => /=.
  - case c.
    + constructor.
      by apply or_introl.
      Undo 2.
      by do 2! constructor.
    by do 2! constructor.
    case c.
    + constructor. by apply or_intror.
      Undo 2.
      constructor.
      by constructor 2.
    constructor. by case.

  (* case: b=> /=; case c; do 2? constructor. *)
Qed.

Lemma nandP_my b c : reflect (~~ b \/ ~~ c) (~~ (b && c)).
Proof.
  case: b.
  - case: c.
    constructor.
    auto.
    case.

  Restart.

  by case: b; case: c; constructor; auto; case.
Qed.



(** * Using reflection views in intro patterns *)

Lemma special_support_for_reflect_predicates b c :
  b && c -> b /\ c.
Proof.
move/andP.
Show Proof.

(**
SSReflect implicitly inserts the so-called view hints to
facilitate boolean reflection. In this case it's [elimTF] view hint.

Here is the syntax to do that (see ssrbool.v file):
Hint View for move/ elimTF|3 elimNTF|3 elimTFn|3 introT|2 introTn|2 introN|2.

The optional natural number is the number of implicit arguments
to be considered for the declared hint view lemma.

The ssrbool.v module already declares a numbers of view hints,
so adding new ones should be justtified. For instance, one might need to do it
if one defines a new logical connective.
 *)

(* Set Printing All. *)
(* Show Proof. *)

About elimTF.

Restart.

move=> Hb.
Check @elimTF (b /\ c) (b && c) true (@andP b c) Hb.
move: Hb.
move/(@elimTF (b /\ c) (b && c) true (@andP b c)).

exact: id.
Qed.


(** Reflection views generally work in both directions *)
Lemma special_support_for_reflect_predicates' (b c : bool) :
  b /\ c -> b && c.
Proof.
move/andP.
Show Proof.
About introT.  (** [introT] view hint gets implicitly inserted *)
exact: id.
Qed.



(** * Switching views at the goal *)

Lemma special_support_for_reflect_predicates'' (b c : bool) :
  b /\ c -> b && c.
Proof.
move=> ab.
apply/andP.  (** [apply/] syntax *)
Show Proof.  (** [introTF] view hint gets inserted *)
done.
Qed.



(** Specification for [eqn] -- decision procedure for equality on [nat]s *)
Lemma eqnP_my (n m : nat) : reflect (n = m) (eqn n m).
Proof.
  elim: n m.
  Undo.
  elim: n m=> [|n IHn] [|m].
  - by constructor.
  - by constructor.
  - by constructor.
  - move=> /=. Restart.

(* Убираем/доказываем все не интересные случаи *)

elim: n m=> [|n IHn] [|m]; try constructor=> //.
move=> /=.

(* reflect (n.+1 = m.+1) (eqn n m)

   Справа у нас нет ни [true] ни [false] в явном виде,
   поэтому мы не знаем какой конструктор выбрать. *)

(** Need to convert a [reflect]-based propositions into bi-implications *)
Search reflect -seq -"or" -"and" -"mem" -negb -minn.

(* Позволяет преобразовывать цель, которая
   выражена через [reflect], в логическую эквивалентность. *)
About iffP.

(* forall (P Q : Prop) (b : bool),
   reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b *)

(* Мы должны показать, что [P] и [b] связаны друг с другом (предъявить [reflect P b]).
   После этого [iffP] нам позволит перейти к доказательству би-импликации [P <-> Q],
   если мы покажем, что за [Q] мы имеем ввиду. *)

Check (IHn m).
(* reflect (n = m) (eqn n m) *)
Check iffP (IHn m).
(* (n = m -> ?Q) -> (?Q -> n = m) -> reflect ?Q (eqn n m) *)

(**
How the conclusion of [iffP (IHn m)] matches with the goal:

                                  reflect (n.+1 = m.+1) (eqn n m)
(n = m -> ?Q) -> (?Q -> n = m) -> reflect ?Q            (eqn n m)

Coq infers [?Q] existential variable to be [n.+1 = m.+1]
*)

apply: (iffP (IHn m)).
(* Теперь нужно доказать эквивалентность [n = m] и [eqn n m] *)
- move=> H. rewrite H. done.
- About succn_inj.
  by move/succn_inj.
  Undo.
  apply: succn_inj.
Undo 7.

by apply: (iffP (IHn m)) => [-> | /succn_inj].

Restart.

About iffP.
About idP.
Check (iffP idP).
apply: (iffP idP). (** [idP] -- the trivial reflection view *)
- by elim: n m => [|n IHn] [|m] //= /IHn->.
- move=> ->. by elim: m.
Qed.


Variable b1 : bool.

Lemma idP' : reflect b1 b1.
Proof.
case b1.
- by constructor.
by constructor.
Qed.

Lemma silly_example_iffP_andP (b c : bool) :
  reflect (b /\ c) (b && c).
Proof.
apply: (iffP idP).
Undo.
Check (iffP andP).
apply: (iffP andP).
done.
done.
Qed.


(** A better example of using [iffP] with a non-[idP] argument *)
Lemma nseqP (T : eqType) n (x y : T) :
  reflect (y = x /\ n > 0) (y \in nseq n x).
Proof.
(* rewrite mem_nseq andbC. *)

(* [iffP andP] позволяет одновременно разбить цель на 2 подцели и
   булево [&&] внутри правой части заменить на логическое [/\] *)
(* apply: (iffP andP). *)

(* Тут [eqP] используется, чтобы перейти от булева к пропозициональному
   равенству, с которым мы можем делать переписывания *)
(* case. move/eqP. move=>->. done. *)
(* Undo 4. *)

(* case=> /eqP->. done. *)
(* Тут делаем то же самое, только у нас тут сразу имеется пропозициональное равенство,
   поэтому вид применять не нужно *)
(* case=>->. done. *)

(* Restart. *)

(* by rewrite mem_nseq andbC; apply: (iffP andP) => -[/eqP]. *)
Admitted.



(** * Rewriting with [reflect] predicates *)


About maxn_idPl.

Lemma leq_max m n1 n2 :
  (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
  case/orP: (leq_total n2 n1) => [le_n21 | le_n12].
  Undo.

  About leq_total.
  move: (leq_total n2 n1).
  (* Но это лемма доказана для булева [||], а не для логического.
     Поэтому применим вид [move/orP], чтобы можно было разобрать по случаям с [case]. *)
  move/orP.
  case.
  move=> le_n21.
  Undo 2.
  (* Называем как-то оба случая и помещаем их в контекст. *)
  case=> [le_n21 | le_n12].
  - About maxn_idPl.
    rewrite (maxn_idPl le_n21).
    Undo.
    rewrite (@maxn_idPl n1 n2 le_n21).

(** Why does this work?
    [maxn_idPl] is _not_ a function but behaves like one here *)

Check (maxn_idPl le_n21).  (** OK, this is an ordinary equation,
                               no wonder [rewrite] works. *)

Set Printing Coercions.
Check (maxn_idPl le_n21).   (** [elimT] get implicitly inserted *)
Unset Printing Coercions.

About elimT.

(** [elimT] is a coercion from [reflect] to [Funclass],
    This means it gets inserted when one uses a reflect view as a function.
  *)

(** Essentially we invoke the following tactic: *)

Undo.
rewrite (elimT maxn_idPl le_n21).
Abort.


(** * An example of a specification for a [seq] function *)

(** [all] specification *)
About allP.
(**
    forall (T : eqType) (a : pred T) (s : seq T),
    reflect {in s, forall x : T, a x} (all a s)
*)

(** Check out some other specs in the [seq] module! *)
Search _ reflect in seq.




(*** Specs as rewrite rules *)

Example for_ltngtP m n :
  (m <= n) && (n <= m) -> (m == n) || (m > n) || (m + n == 0).
Proof.
by case: ltngtP.

Restart.

case: ltngtP.
done. done.
move=>/=.
Abort.


Module Trichotomy.

Variant compare_nat m n :
  bool -> bool -> bool -> bool -> bool -> bool -> Set :=
| CompareNatLt of m < n : compare_nat m n true  false true  false false false
| CompareNatGt of m > n : compare_nat m n false true  false true  false false
| CompareNatEq of m = n : compare_nat m n true  true  false false true  true.

Lemma ltngtP m n : compare_nat m n (m <= n) (n <= m) (m < n)
                                   (n < m)  (n == m) (m == n).
Proof.
rewrite !ltn_neqAle [_ == m]eq_sym; case: ltnP => [mn|].
  by rewrite ltnW // gtn_eqF //; constructor.
rewrite leq_eqVlt; case: ltnP; rewrite ?(orbT, orbF) => //= lt_nm eq_mn.
  by rewrite ltn_eqF //; constructor.
by rewrite eq_mn; constructor; apply/eqP.
Qed.

(** One more example *)
Lemma maxnC : commutative maxn.
Proof.
move=> m n.
rewrite /maxn.
case: ltngtP.
done.
done.
done.
Qed.

End Trichotomy.






(*** Coercions summary *)


(** * [is_true] coercion *)

(** We have already been using [is_true] coercion regularly.
    It's defined in ssrbool.v as follows:

    Coercion is_true : bool >-> Sortclass.
 *)

(** E.g. [is_true] makes the following typecheck *)
Check (erefl true) : true.

(* Это работает потому, что на самом деле тут
   стоит коэрция [is_true], которая делает следующее: *)
Check (erefl true) : (true = true).
(* Можно в этом убедиться вот так: *)
Set Printing Coercions.
Check (is_true true).
Unset Printing Coercions.



(** * [elimT] coercion *)

(**  Allow the direct application of a reflection lemma to a boolean assertion.

    Coercion elimT : reflect >-> Funclass.
 *)

Section ElimT_Example.

Variables b c : bool.
Hypothesis H : b || c.

(* У нас есть лемма, которая связывает булеву и пропозициональную конъюнкцию, то
   мы может это использовать как ф-цию, благодаря тому, что (как было показано выше)
   не явно вставляется [elimT : forall (P : Prop) (b : bool), reflect P b -> b -> P] *)
Check orP H.

Set Printing Coercions.
Check orP H.
Unset Printing Coercions.

End ElimT_Example.



(** * [nat_of_bool] coercion *)

About nat_of_bool.

About leq_b1.
About mulnb.

About count_nseq.

(** You can learn more using the following search query: *)
Search _ nat_of_bool.
