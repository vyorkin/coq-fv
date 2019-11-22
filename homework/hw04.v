(**
Exercises on Generalizing the Induction Hypothesis
https://homes.cs.washington.edu/~jrw12/InductionExercises.html
by James Wilcox (2017)

Adapted to SSReflect syntax and Mathcomp library.
*)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint sum (l : seq nat) : nat :=
  if l is (x :: xs) then x + sum xs
  else 0.

Fixpoint sum_iter' (l : seq nat) (acc : nat) : nat :=
  if l is (x :: xs) then sum_iter' xs (x + acc)
  else acc.

Definition sum_iter (l : seq nat) : nat :=
  sum_iter' l 0.

Lemma sum_iter'_correct l x0 :
  sum_iter' l x0 = x0 + sum l.
Proof.
  move: x0.
  elim: l=> [|x xs] //= IH_x0 x0.
  - rewrite addnCA.
    rewrite IH_x0.
    rewrite addnA.
    done.

  Restart.

  elim: l x0=> [|x xs] //= IH_x0 x0.
  by rewrite addnCA IH_x0 addnA.
Qed.

Theorem sum_iter_correct l :
  sum_iter l = sum l.
Proof.
  elim: l=>// l.
  rewrite /sum_iter /= addn0=> l0 H.
  by rewrite sum_iter'_correct.
Qed.

(** Continuation-passing style
    https://en.wikipedia.org/wiki/Continuation-passing_style
 *)
Fixpoint sum_cont' {A} (l : seq nat) (k : nat -> A) : A :=
  if l is (x :: xs) then sum_cont' xs (fun ans => k (x + ans))
  else k 0.

Definition sum_cont (l : seq nat) : nat :=
  sum_cont' l (fun x => x).

Lemma sum_cont'_correct A l (k : nat -> A) :
  sum_cont' l k = k (sum l).
Proof.
  by elim: l k=> //= x l H k; rewrite H.
Qed.

Theorem sum_cont_correct l :
  sum_cont l = sum l.
Proof.
  elim: l=> // l.
  rewrite /sum_cont=> l0 H.
  by rewrite sum_cont'_correct.
Qed.

Fixpoint rev_rec {A : Type} (xs : seq A) : seq A :=
  if xs is (x :: xs') then
    rev_rec xs' ++ [:: x]
  else xs.

About catrev.

Lemma rev_correct A (l1 l2 : seq A) :
  catrev l1 l2 = rev_rec l1 ++ l2.
Proof.
  elim: l1 l2=> //= x xs IH l.
  rewrite IH.
  (* Search _ "cat" in seq. *)
  by rewrite -catA cat1s.
Qed.

Theorem rev_iter_correct A (l : seq A) :
  rev l = rev_rec l.
Proof.
  elim: l=> //= l.
  move=> l0 H.
  Search "cat" in seq.
  rewrite -H.
  rewrite -cat1s.
  Search "rev" in seq.
  by rewrite rev_cat.

  Restart.

  by elim: l=> //= l l0 <-; rewrite -cat1s rev_cat.
Qed.

Fixpoint map_iter' {A B}
    (f : A -> B) (l : seq A) (acc : seq B) : seq B :=
  if l is (x :: l') then map_iter' f l' (f x :: acc)
  else rev acc.

Definition map_iter {A B} (f : A -> B) l :=
  map_iter' f l [::].

(* [rev] это просто [catrev s [::]] *)

Lemma map_iter'_correct A B (f : A -> B) l1 l2 :
  map_iter' f l1 l2 = rev l2 ++ (map f l1).
Proof.
  elim: l1 l2=> //= l.
  - by rewrite cats0.
  move=> l0 IH_l0 l2.
  (* map_iter' f l0 (f l :: l2) = rev l2 ++ f l :: [seq f i | i <- l0] *)
  rewrite IH_l0.
  clear IH_l0.
  (* rev (f l :: l2) ++ [seq f i | i <- l0] = rev l2 ++ f l :: [seq f i | i <- l0] *)
  Search "rev" in seq.
  Search "map" in seq.
  rewrite rev_cons.
  (* rewrite -!catrevE. *)
  (* catrev (f l :: l2) [seq f i | i <- l0] = catrev l2 (f l :: [seq f i | i <- l0]) *)
  (* Search "catrev" in seq. *)

  (* map_cat : [seq f i | i <- s1 ++ s2] = [seq f i | i <- s1] ++ [seq f i | i <- s2] *)

  (* rewrite -map_rev. *)
  (* rewrite -map_cons. *)
  (* catrev (f l :: l2) [seq f i | i <- l0] = catrev l2 [seq f i | i <- l :: l0] *)

  (* map_iter' f l0 (f l :: l2) = catrev l2 (f l :: [seq f i | i <- l0]) *)
  (* Search "catrev" in seq. *)

  (* map_rev : [seq f i | i <- rev s] = rev [seq f i | i <- s] *)

  Restart.

  elim: l1 l2=> [|x1 l1 IHl1 /=] l2.
  - by rewrite cats0.
    rewrite IHl1.
    rewrite rev_cons.
    (* Хех, a я был близок... До [-cats1] не додумался! *)
    (* cats1 : s ++ [:: z] = rcons s z. *)
    rewrite -cats1.
    (* catA  : s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3. *)
    rewrite -catA /=.
    done.
Qed.

Theorem map_iter_correct A B (f : A -> B) l :
  map_iter f l = map f l.
Proof.
  exact: map_iter'_correct.
Qed.

Inductive expr : Type :=
| Const of nat
| Plus of expr & expr.

Fixpoint eval_expr (e : expr) : nat :=
  match e with
  | Const n => n
  | Plus e1 e2 => eval_expr e1 + eval_expr e2
  end.

Fixpoint eval_expr_iter' (e : expr) (acc : nat) : nat :=
  match e with
  | Const n => n + acc
  | Plus e1 e2 => eval_expr_iter' e2 (eval_expr_iter' e1 acc)
  end.

Definition eval_expr_iter e := eval_expr_iter' e 0.

Lemma eval_expr_iter'_correct e acc :
  eval_expr_iter' e acc = acc + eval_expr e.
Proof.
  (* В посылках будут 2 гипотезы индукции,
     по одной для каждого параметры конструктора
     [Plus e1 e2] из определения [eval_expr_iter'] *)
  elim: e acc.
  move=> n acc.
  move=> /=.
  - by rewrite addnC.
  move=> e1 IH1 e2 IH2 acc.
  move=> /=.
  rewrite addnA.
  rewrite IH1.
  rewrite IH2.
  done.

  Restart.

  elim: e acc=> [n | e1 IH1 e2 IH2 /=] acc.
  - by rewrite addnC.
  rewrite addnA.
  rewrite IH1.
  rewrite IH2.
  done.

  Restart.
  elim: e acc=> [n | e1 IH1 e2 IH2 /=] acc; first by rewrite addnC.
  by rewrite IH1 IH2 addnA.
Qed.

(* В intro-паттернах пока нельзя сразу же переписывать с
   использованием уже ранее доказанных лемм, но скоро будет
   можно, используя новые паттерны, которые в Coq 8.10
   добавили. Гипотезой индукции можно переписывать сразу же,
   как и всем, что будет лежать в стеке-цели *)


Theorem eval_expr_iter_correct e :
  eval_expr_iter e = eval_expr e.
Proof. exact: eval_expr_iter'_correct. Qed.

Fixpoint eval_expr_cont' {A} (e : expr) (k : nat -> A) : A :=
  match e with
  | Const n => k n
  | Plus e1 e2 => eval_expr_cont' e2 (fun n2 =>
                  eval_expr_cont' e1 (fun n1 => k (n1 + n2)))
  end.

Definition eval_expr_cont (e : expr) : nat :=
  eval_expr_cont' e (fun n => n).

Lemma eval_expr_cont'_correct A e (k : nat -> A) :
  eval_expr_cont' e k = k (eval_expr e).
Proof.
  elim: e k=> //=.
  move=> e1 IH1 e2 IH2 k.
  rewrite IH2.
  rewrite IH1.
  done.

  Restart.
  by elim: e k=> [|e1 IH1 e2 IH2] k //=; rewrite IH2 IH1.
Qed.

Theorem eval_expr_cont_correct e :
  eval_expr_cont e = eval_expr e.
Proof. exact: eval_expr_cont'_correct. Qed.

Inductive instr :=
| Push (n : nat)
| Add.

Definition prog := seq instr.

Definition stack := seq nat.

Fixpoint run (p : prog) (s : stack) : stack :=
  if p is (i :: p') then
    let s' :=
        match i with
        | Push n => n :: s
        | Add => if s is (a1 :: a2 :: s') then a2 + a1 :: s'
                 else s
        end
    in
    run p' s'
  else s.

Fixpoint compile (e : expr) : prog :=
  match e with
  | Const n => [:: Push n]
  | Plus e1 e2 => compile e1 ++ compile e2 ++ [:: Add]
  end.

Lemma run_append p1 p2 s :
  run (p1 ++ p2) s = run p2 (run p1 s).
Proof.
  elim: p2 p1=> [|i p IHp1] p1.
  - by rewrite cats0.
  (* IHp1 : forall p1 : seq instr, run (p1 ++ p) s = run p (run p1 s) *)
  (* run (p1 ++ i :: p) s = run (i :: p) (run p1 s) *)
  Search "cat" in seq.
  rewrite -cat_rcons.
  rewrite -cats1.
  rewrite IHp1.
  (* run p (run (p1 ++ [:: i]) s) = run (i :: p) (run p1 s) *)
  (* rewrite cats1. *)
  (* run p (run (rcons p1 i) s) = run (i :: p) (run p1 s) *)
  Search "cons" in seq.

  Restart.

  elim: p1 p2 s => //.
  move=> i l H s s0 /=.
  rewrite -H.
  done.

  Restart.

  elim: p1 s => //=.
Qed.

Lemma compile_correct_generalized e s :
  run (compile e) s = (eval_expr e) :: s.
Proof.
Admitted.

Theorem compile_correct e :
  run (compile e) [:: ] = [:: eval_expr e].
Proof.
Admitted.
