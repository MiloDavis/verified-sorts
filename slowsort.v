Require Import List.
Import ListNotations.
Set Implicit Arguments.
Require Import Coq.Program.Wf.
Require Import Arith.

Fixpoint div2 n :=
  match n with
    | O | 1 => 0
    | S (S n) => S (div2 n)
  end.

Theorem div2_correct : forall n, div2 n = n / 2.
Proof.
  intros. induction n. compute. reflexivity.
  simpl. 
  
                     

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

Lemma div_gt : forall i j, (j - i) <=? 1 = false -> (i + j) / 2 >= 1.
Proof.
  admit.
Admitted.


Program Fixpoint slowsort_help (l : list nat) (i j : nat) {measure (j - i)} :=
  if (j - i) <=? 1 
  then l
  else let m := (i + j) / 2 in
       let partially_sorted := slowsort_help (slowsort_help l i m) m j in
       let lm := nth (pred m) partially_sorted 0 in
       let lj := nth (pred j) partially_sorted 0 in
       if  lj <? lm
       then slowsort_help (set (set partially_sorted (pred m) lj) (pred j) lm)
                          i (pred j)
       else slowsort_help partially_sorted i (pred j).
Next Obligation. admit. Admitted.
Next Obligation. admit. Admitted.
Next Obligation. admit. Admitted.
Next Obligation. admit. Admitted.
  
Definition slowsort l := slowsort_help l 0 (length l).

Example slowsort_test1 : slowsort [1;20;0; 3000; 10] = [0; 1; 10; 20; 3000].
Proof. auto. Qed.

Example slowsort_test2 : slowsort [] = [].
Proof. auto. Qed.

Example slowsort_test3 : slowsort [1] = [1].
Proof. auto. Qed.

Inductive max_list : list nat -> nat -> Prop :=
| max_nil : max_list [] 0
| max_cons : forall n hd l, max_list l n -> max_list (hd :: l) (max hd n).

Theorem slowsort_help_correct : forall i j l, LocallySorted le (slowsort_help l i j)
                                         /\ max_list (nth l (slowsort_help l i j) pred j) l.
