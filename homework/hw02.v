From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section IntLogic.

Variables A B C : Prop.

Lemma notTrue_iff_False : (~ True) <-> False.
Proof.
  rewrite /not.
  exact. Undo 1.
  by []. Undo 1.
  by split; exact; exact. Undo 1.
  split. exact. exact.

  Restart.

  rewrite /not.
  split.
  - apply. exact: I.
  exact.
Qed.

Lemma dne_False : ~ ~ False -> False.
Proof.
  rewrite /not.
  apply. exact. Undo 2.
  exact.
Qed.

Lemma dne_True : ~ ~ True -> True.
Proof.
  rewrite /not.
  by []. Undo 1.
  exact. Undo 1.
  by move=> //.
Qed.

Lemma weak_peirce : ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
  move=> H1.
  apply: (H1).
  apply.
  move=> a.
  apply: H1.
  by [].
Qed.

Lemma imp_trans : (A -> B) -> (B -> C) -> (A -> C).
Proof.
  move=> H1 H2 a.
  by apply H2; apply H1.
Qed.

End IntLogic.


(** Let's get familiarize ourselves with some lemmas from [ssrbool] module.
    The proofs are very easy, so the lemma statements are more important here.
 *)
Section BooleanLogic.

Variables (A B : Type) (x : A) (f : A -> B) (a b : bool) (vT vF : A).

Lemma negbNE : ~~ ~~ b -> b.
Proof. by case b. Qed.

(** Figure out what [involutive] and [injective] mean
    using Coq's interactive queries. Prove the lemmas.
    Hint: to unfold a definition in the goal use [rewrite /definition] command.
*)
Lemma negbK : involutive negb.
Proof.
  rewrite /involutive. (* cancel negb negb *)
  rewrite /cancel.     (* ~~ ~~ x0 = x0 *)
  by case.
Qed.

Lemma negb_inj : injective negb.
Proof.
  rewrite /injective.
  by case; case.
Qed.

Lemma ifT : b -> (if b then vT else vF) = vT.
Proof. by case b. Qed.

Lemma ifF : b = false -> (if b then vT else vF) = vF.
Proof. by case b. Qed.

Lemma if_same : (if b then vT else vT) = vT.
Proof. by case b. Qed.

Lemma if_neg : (if ~~ b then vT else vF) = if b then vF else vT.
Proof. by case b. Qed.

Lemma fun_if : f (if b then vT else vF) = if b then f vT else f vF.
Proof. by case b. Qed.

Lemma if_arg (fT fF : A -> B) :
  (if b then fT else fF) x = if b then fT x else fF x.
Proof. by case b. Qed.

Lemma andbK : a && b || a = a.
Proof. by case a; case b. Qed.

(** Find out what [left_id], [right_id] mean
    using Coq's interactive queries. Prove the lemmas.
 *)
Lemma addFb : left_id false addb.
(* [addb] means XOR (eXclusive OR operation) *)
Proof.
  (* https://en.wikipedia.org/wiki/Identity_element *)

  (* Левая "единица" (нейтральный элемент) *)
  About  left_id. (* S -> (S -> T -> T)           *)
  Print  left_id. (* op (e : S) (x : T) = (x : T) *)

  (* Правая "единица" (нейтральный элемент) *)
  About right_id. (* T -> (S -> T -> S)           *)
  Print right_id. (* op (x : S) (e : T) = (x : T) *)

  (* Search _ ( left_id _ _). *)
  (* Search _ (right_id _ _). *)
  rewrite /left_id.
  move=> v. rewrite /addb. done.
  Undo 2.
  by [].
Qed.

Lemma addbF : right_id false addb.
Proof.
  by case.
  Undo.
  rewrite /addb.
  case.
  - rewrite /negb. done.
  - done.
Qed.

Lemma addbC : commutative addb.
Proof.
  by case; case.
  Undo.
  (* Если есть желание посмотреть что происходит под капотом,
     то можно прошагать вот эту дичь, которую я написал далее. *)
  rewrite /commutative.
  case. case.
  - rewrite /addb. done.
  - rewrite /addb. rewrite /negb. done.
  - case. rewrite /addb. rewrite /negb. done.
  - rewrite /addb. done.
Qed.

Lemma addbA : associative addb.
Proof.
  rewrite /associative.
  move=> m n k.
  (* Я тут уже не буду расписывать так же как выше,
     но тут происходит ровно тоже самое, только уже с 3 переменными. *)
  Undo 2.
  by case; case; case.
Qed.

(** Formulate analogous laws
    (left/right identity, commutativity, associativity)
    for boolean AND and OR and proove those.
    Find the names of corresponding lemmas in the standard library using
    [Search] command. For instance: [Search _ andb left_id.]
    Have you noticed the naming patterns?
 *)

Lemma orbF : right_id false orb.
Proof.
  by case.
  Undo.
  (* Оставил просто для того,
     чтобы пошагать и посмотреть что происходит *)
  rewrite /right_id.
  case.
  - done.
  - done.
Qed.

(* Аналогично и всё остальное *)

Lemma orFb : left_id false orb. Proof. by case. Qed.

Lemma andbT : right_id true andb. Proof. by case. Qed.
Lemma andTB : left_id true andb. Proof. by case. Qed.

Lemma orbC : commutative orb. Proof. by case; case. Qed.
Lemma andbC : commutative andb. Proof. by case; case. Qed.

Lemma orbA : associative orb. Proof. by case; case; case. Qed.
Lemma andbA : associative andb. Proof. by case; case; case. Qed.

End BooleanLogic.



Section NaturalNumbers.
(** Figure out what [cancel], [succn], [predn] mean
    using Coq's interactive queries. Prove the lemmas.
 *)
Lemma succnK : cancel succn predn.
Proof.
  About cancel.
  About succn. Print succn. Print predn.
  by [].
  Undo.
  rewrite /cancel.
  done.
Qed.

Lemma add0n : left_id 0 addn.
Proof. by []. Qed.

Lemma addSn m n : m.+1 + n = (m + n).+1.
Proof. by []. Qed.

Lemma add1n n : 1 + n = n.+1.
Proof. by []. Qed.

Lemma add2n m : 2 + m = m.+2.
Proof. by []. Qed.

Lemma subn0 : right_id 0 subn.
Proof.
  rewrite /right_id.
  by case.
Qed.

End NaturalNumbers.
