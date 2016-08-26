Require Import List.
Import ListNotations.
Set Implicit Arguments.
Require Import Coq.Program.Wf.
Require Import Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
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

Lemma filter_In_strong : forall A (m : A) (l : list A) (f : A -> bool), In m (filter f l) -> In m l.
Proof.
  intros. generalize dependent m. induction l; intros. inversion H.
  simpl. simpl in H. destruct (f a). destruct H. auto. auto.
  auto.
Qed.

Lemma ltb_leb : forall n m, (n <=? m = true /\ m <? n = false)
                       \/ (n <=? m = false /\ m <? n = true).
Proof.
  intros. pose Nat.leb_antisym. assert ((n <=? m) = negb (m <? n)).
  apply e. destruct (n <=? m). left. split. reflexivity.
  apply Bool.negb_true_iff. auto. right. split. reflexivity.
  apply Bool.negb_false_iff. auto.
Qed.

Lemma in_filters : forall m n0 l, In m l -> In m (filter (fun x : nat => x <? n0) l)
                                      \/ In m (filter (fun x : nat => n0 <=? x) l).
Proof.
  intros. remember (length l) as n. assert (length l <= n). subst. constructor.
  clear Heqn. generalize dependent l. generalize dependent m.
  induction n; intros. destruct l. inversion H. inversion H. inversion H0.
  inversion H0. destruct l. inversion H. simpl. inversion H.
  assert ((n0 <=? n1 = true /\ n1 <? n0 = false)
          \/ (n0 <=? n1 = false /\ n1 <? n0 = true)). apply ltb_leb.
  destruct H2; inversion H2. rewrite H3. rewrite H4. right. rewrite H1.
  constructor. reflexivity. rewrite H3. rewrite H4. left. constructor. assumption.
  assert ((n0 <=? n1 = true /\ n1 <? n0 = false)
          \/ (n0 <=? n1 = false /\ n1 <? n0 = true)). apply ltb_leb.
  inversion H2. inversion H3. rewrite H4. rewrite H5. simpl. apply or_comm.
  apply or_assoc. right. apply or_comm. apply IHn. assumption.
  simpl in H0. apply le_S_n in H0. apply H0. inversion H3. rewrite H4. rewrite H5.
  simpl. apply or_assoc. right. apply IHn. assumption. simpl in H0. apply le_S_n in H0.
  assumption.
Qed.

Lemma filters_permutation : forall y l,
                              Permutation l
                                          ((filter (fun x : nat => x <? y) l)
                                             ++  (filter (fun x : nat => y <=? x) l)).
Proof.
  intros. remember (length l) as n. assert (length l <= n). subst. constructor.
  clear Heqn. generalize dependent l. generalize dependent y.
  induction n; intros; destruct l. auto. inversion H. auto. simpl.
  assert ((y <=? n0) = true /\ (n0 <? y) = false \/
                              (y <=? n0) = false /\ (n0 <? y) = true).
  apply ltb_leb. inversion H0. inversion H1. rewrite H2. rewrite H3.
  apply Permutation_cons_app. apply IHn. apply le_S_n. simpl in H. assumption.
  inversion H1. rewrite H2. rewrite H3. simpl. constructor. apply IHn.
  apply le_S_n. simpl in H. assumption.
Qed.

Theorem qsort_permutation : forall l, Permutation l (qsort l). 
Proof.
  intros. intros. remember (length l) as n. assert (length l <= n). subst. constructor.
  clear Heqn. generalize dependent l. induction n; intros.
  destruct l. constructor. inversion H. destruct l. constructor.
  unfold_sub qsort (qsort (n0 :: l)). apply Permutation_cons_app.
  assert (Permutation l ((filter (fun x : nat => x <? n0) l) ++
                                                        (filter (fun x : nat => n0 <=? x) l))).
  apply filters_permutation.
  apply Permutation_trans with (l' := (filter (fun x : nat => x <? n0) l ++
                                              filter (fun x : nat => n0 <=? x) l)).
  assumption. simpl in H. apply le_S_n in H.
  apply Permutation_app; apply IHn; 
  apply le_trans with (m := length l). apply filter_length. assumption.
  apply filter_length. assumption.
Qed.

Lemma qsort_member : forall m l, In m (qsort l) <-> In m l.
Proof.
  intros. assert (Permutation (qsort l) l). apply Permutation_sym. apply qsort_permutation.
  split; intros. apply Permutation_in with (l := (qsort l)). assumption. assumption.
  apply Permutation_sym in H. apply Permutation_in with (l := l). assumption. assumption.
Qed.

Lemma qsort_member2 : forall m l, In m l -> In m (qsort l).
Proof.
  intros. remember (length l) as n. assert (length l <= n). subst. constructor.
  clear Heqn. generalize dependent l. generalize dependent m.
  induction n; intros. destruct l. inversion H. inversion H0.
  destruct l. inversion H. inversion H. unfold_sub qsort (qsort (n0 :: l)).
  apply in_or_app. right. rewrite H1. constructor. reflexivity.
  unfold_sub qsort (qsort (n0 :: l)). apply in_or_app. assert (In m l). assumption.
  apply in_filters with (n0 := n0) in H1. inversion H1. left. apply IHn. assumption.
  simpl in H0. apply le_S_n in H0. apply le_trans with (length l). apply filter_length.
  assumption. right. simpl. right. apply IHn. assumption.
  simpl in H0. apply le_S_n in H0. apply le_trans with (length l). apply filter_length.
  assumption.
Qed. 

Hint Constructors LocallySorted.
Theorem qsort_sorted : forall l, LocallySorted le (qsort l).
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
  apply -> qsort_member in H2. apply filter_In in H2.
  inversion H2. apply Nat.ltb_lt in H4. apply leb_correct. auto with arith.
  intros. apply -> qsort_member in H2. apply filter_In in H2. inversion H2.
  apply leb_complete. assumption.
Qed.
