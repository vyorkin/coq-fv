From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.

Module Playground4.
  (* [iota] is a natural numbers generator:
     [:: m; m+1; ...; m+n-1] *)

  Fixpoint iota m n :=
    if n is u.+1
    then m :: iota m.+1 u
    else [::].

  (* Sigma-notation: *)
  Notation "\sum_ ( m <= i < n ) F" :=
    (foldr (fun i acc => F + acc)
           0 (* initial value *)
           (iota m (n - m))). (* iota-generated sequence *)

  Compute \sum_ (1 <= i < 5) (i * 2 - 1).
  (*             ^- m  n -^    ^ F ^ *)
  Compute \sum_ (1 <= i < 5) i.
  (*                      F -^ *)

  (* Fixpoint all_words (n : nat) (l : seq nat) : seq (seq nat) := *)
  (*   if l is h :: tl then *)
  (*     if n is i.+1 then *)
  (*       [seq h :: w | w <- all_words i l] *)
  (*     else *)
  (*       [:: l] *)
  (*   else *)
  (*     [::]. *)

  (*  [:: [:: 1; 1]; [:: 1; 2]; [:: 1; 3];
          [:: 2; 1]; [:: 2; 2]; [:: 2; 3];
          [:: 3; 1]; [:: 3; 2]; [:: 3; 3]
      ] *)

  (* Compute (all_words 2 [:: 1; 2; 3]). *)

End Playground4.
