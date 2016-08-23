Require Import List.
Import ListNotations.
Set Implicit Arguments.
Require Import Coq.Program.Wf.
Require Import Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Program.Combinators.
Import WfExtensionality.

Lemma filter_length : forall T (f : T -> bool) (l : list T),
                          List.length (List.filter f l) <= List.length l.
Proof.
  intros.
  induction l.
  constructor.
  simpl. destruct (f a). simpl. apply le_n_S. assumption.
  constructor. assumption.
Qed.

Lemma tl_length : forall T (hd : T) (tl : list T), List.length tl < List.length (hd :: tl).
Proof.
  intros. auto.
Qed.

Theorem tl_filter : forall T (hd : T) (f : T -> bool) (tl : list T),
                      List.length (filter f tl) < List.length (hd :: tl).
Proof.
  intros. induction tl. auto.
  simpl. destruct (f a). simpl. apply lt_n_S. auto.
  auto.
Qed.
  
Program Fixpoint qsort l {measure (length l) l}:=
  match l with
    | [] => []
    | hd :: tl => List.app (qsort (List.filter (fun x => Nat.ltb x hd) tl))
                          (hd :: (qsort (List.filter (fun x => Nat.leb hd x) tl)))
  end.
Next Obligation. apply tl_filter. Qed.
Next Obligation. apply tl_filter. Qed.

Lemma cons_sorted : forall A (R : A -> A -> Prop) (hd : A) (tl : list A),
                      (forall b, In b tl -> R hd b) ->
                      LocallySorted R tl -> LocallySorted R (hd :: tl).
Proof.
  intros. induction tl. constructor. constructor. assumption.
  apply H. constructor. reflexivity.
Qed.

Lemma app_lt_sorted : forall A R pivot (l1 l2 : list A),
                        LocallySorted R l1 -> LocallySorted R l2 ->
                        (forall a, In a l1 -> R a pivot) ->
                        (forall b, In b l2 -> R pivot b) ->
                        LocallySorted R (List.app l1 (pivot :: l2)).
Proof.
  intros. generalize dependent l2. induction l1; intros.
  simpl.
  inversion H0. constructor. apply LSorted_consn. constructor.
  apply H2. rewrite <- H3. constructor. reflexivity.
  apply LSorted_consn. rewrite <- H5 in H0. apply H0. apply H2.
  rewrite <- H5. constructor. reflexivity.
  inversion H. simpl. constructor. rewrite <- H5 in *. simpl in *.
  apply IHl1. constructor. intros. contradiction. assumption. assumption.
  apply H1. constructor. reflexivity.
  simpl. constructor. rewrite <- H4 in *. simpl in *.
  apply IHl1. assumption. intros. apply H1. inversion H7.
  right. left. assumption.
  right. right. assumption.
  assumption.
  assumption. assumption.
Qed.

Lemma app_lt_sorted_old : forall A R pivot (l1 l2 : list A),
                        LocallySorted R l1 -> LocallySorted R l2 ->
                        (forall a l1, In a l1 -> R a pivot) ->
                        (forall b l2, In b l2 -> R pivot b) ->
                        LocallySorted R (List.app l1 (pivot :: l2)).
Proof.
  intros. generalize dependent l2. induction l1; intros.
  simpl.
  inversion H0. constructor. apply LSorted_consn. constructor.
  apply H2 with (l2 := l2). rewrite <- H3. constructor. reflexivity.
  apply LSorted_consn. rewrite <- H5 in H0. apply H0. apply H2 with (l2 := l2).
  rewrite <- H5. constructor. reflexivity.
  inversion H. simpl. constructor. rewrite <- H5 in IHl1. simpl in IHl1.
  apply IHl1. constructor. assumption. apply H1 with (l1 := (a :: l1)).
  constructor. reflexivity.
  simpl. constructor. rewrite <- H4 in IHl1. simpl in IHl1. apply IHl1.
  assumption. assumption. assumption.
Qed.

Lemma lt_let_true : forall n m, n <=? m = true \/ m <? n = true.
Proof.
  intros. pose Nat.le_gt_cases. assert (H := o n m).
  inversion H. left. apply leb_correct. assumption.
  right. apply Nat.ltb_lt. assumption.
Qed.

Program Fixpoint in_filters n pivot l {measure (length l)} : In n l ->
                                In n (List.filter (fun x => Nat.ltb x pivot) l)
                                \/ In n (List.filter (fun x => Nat.leb pivot x) l) :=
  match l with
    | [] => _
    | hd :: tl => _
  end.
Next Obligation. inversion H. assert (pivot <=? hd = true \/ hd <? pivot = true).
                 apply lt_let_true. inversion H1. right. rewrite H2.
                 rewrite H0. constructor. reflexivity.
                 rewrite H2. left. constructor. assumption.
                 

  
Program Fixpoint qsort_permutation m l {measure (length l)}: In m (qsort l) -> In m l :=
  match l with
    | [] => _
    | hd :: tl => _
  end.
Next Obligation. assert ((qsort (hd :: tl)) =
                         List.app (qsort (List.filter (fun x => Nat.ltb x hd) tl))
                                  (hd :: (qsort (List.filter (fun x => Nat.leb hd x) tl)))).
                 unfold_sub qsort (qsort (hd :: tl)). reflexivity.
                 rewrite H0 in H. apply in_app_or in H. inversion H.
                 apply qsort_permutation in H1.
  
  
  

Hint Constructors LocallySorted.
Theorem qsort_correct : forall l, LocallySorted le (qsort l).
Proof.
  intros. remember (length l) as n. assert (length l <= n). subst. constructor.
  clear Heqn. generalize dependent l.
  induction n; intros.
  destruct l. compute. constructor. inversion H.

  destruct l. compute. constructor.
  simpl in H. apply le_S_n in H.
  unfold_sub qsort (qsort (n0 :: l)).
  assert (LocallySorted le (qsort (filter (fun x => Nat.ltb x n0) l))).
  apply IHn. apply le_trans with (length l). apply filter_length. assumption.
  assert (LocallySorted le (qsort (filter (fun x => Nat.leb n0 x) l))).
  apply IHn. apply le_trans with (length l). apply filter_length. assumption.
  apply app_lt_sorted. assumption. assumption.
  intros. apply Nat.leb_le. 
  apply qsort_permutation in H2. apply filter_In in H2.
  inversion H2. apply Nat.ltb_lt in H4. apply leb_correct. auto with arith.
  intros. apply qsort_permutation in H2. apply filter_In in H2. inversion H2.
  apply leb_complete. assumption.
Qed.
