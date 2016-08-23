Require Import List.
Import ListNotations.
Set Implicit Arguments.
Require Import Coq.Program.Wf.
Require Import Arith.

Section Array.
  Definition array T := list T.
  Variable (A : Set).
  Fixpoint set (l:list A) (n:nat) (v:A) :=
    match n, l with
      | O, x :: l' => v :: l'
      | O, [] => []
      | S m, [] => []
      | S m, x :: t => x :: (set t m v)
    end.
  Theorem set_nth : forall l n v, nth n (set l n v) v = v.
  Proof.
    intros. generalize dependent n. induction l; intros. simpl. destruct n; auto.
    simpl. destruct n. reflexivity. simpl. apply IHl.
  Qed.
End Array.

Example div1 : 10 / 2 = 5.
Proof. auto. Qed.

Example div2 : 10 / 3 = 3.
Proof. auto. Qed.

Example leb1 : leb 0 1 = true.
Proof. auto. Qed.

Example leb2 : leb 0 0 = true.
Proof. auto. Qed.

Lemma term_justification : forall i j, i <= j -> ~ ((j - i) <= 1) -> ((i + j) / 2) - i < i - j.
Proof.
  intros. induction i. simpl. destruct j.  contradiction H0. auto.
  simpl.
  

Program Fixpoint slowsort_help (l : list nat) (i j : nat) {measure (j - i)} :=
  if leb (j - i) 1 
  then l
  else let m := (i + j) / 2 in
       let partially_sorted := slowsort_help (slowsort_help l i m) m j in
       let lm := nth (pred m) partially_sorted 0 in
       let lj := nth (pred j) partially_sorted 0 in
       if Nat.ltb lj lm
       then slowsort_help (set (set partially_sorted (pred m) lj) (pred j) lm)
                          i (pred j)
       else slowsort_help partially_sorted i (pred j).
Next Obligation. 
                 
  
Definition slowsort l := slowsort_help l 0 (length l).

Example sort_empty
