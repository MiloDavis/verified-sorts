Require Import List.
Import ListNotations.
Set Implicit Arguments.
Require Import Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Combinators.
Require Import quicksort.

Inductive bt :=
| Leaf : bt
| Node : nat -> bt -> bt -> bt.

Inductive in_bt : nat -> bt -> Prop :=
| Curnode : forall n1 n2 tl tr, n1 = n2 -> in_bt n1 (Node n2 tl tr)
| Lefttree : forall n1 n2 tl tr, in_bt n1 tl -> in_bt n1 (Node n2 tl tr)
| Righttree : forall n1 n2 tl tr, in_bt n1 tr -> in_bt n1 (Node n2 tl tr).

Inductive bst : bt -> Prop :=
| BSTLeaf : bst Leaf
| BSTNode : forall n1 tl tr, (forall n2, in_bt n2 tl -> n2 < n1)
                        -> (forall n2, in_bt n2 tr -> n2 >= n1)
                        -> bst tl
                        -> bst tr
                        -> bst (Node n1 tl tr).

Fixpoint insert n1 t :=
  match t with
  | Leaf => Node n1 Leaf Leaf
  | Node n2 tl tr => if n1 <? n2
                    then Node n2 (insert n1 tl) tr
                    else Node n2 tl (insert n1 tr)
  end.


Lemma insert_in : forall t n, in_bt n (insert n t).
Proof.
  intros. induction t. compute. constructor. reflexivity.
  simpl. destruct (n <? n0); [ apply Lefttree | apply Righttree ]; assumption.
Qed.

Lemma insert_still_in : forall t n n1, in_bt n1 t -> in_bt n1 (insert n t).
Proof.
  intros. induction t. inversion H.
  simpl. destruct (n <? n0); inversion H.
  constructor. auto.
  apply Lefttree. apply IHt1. assumption.
  apply Righttree. assumption.

  constructor. auto.
  apply Lefttree. assumption.
  apply Righttree. apply IHt2. assumption.
Qed.
  
Lemma insert_inversion : forall t n n2, in_bt n2 (insert n t) -> in_bt n2 t \/  n2 = n.
Proof.
  intros. induction t.
  simpl in H. inversion H. right. assumption.
  inversion H2. inversion H2.

  simpl in *. destruct (n <? n0) eqn:res; inversion H.
  subst. left. constructor. reflexivity.
  assert (in_bt n2 t1 \/ n2 = n). apply IHt1. assumption.
  destruct H5. left. apply Lefttree. assumption.
  subst. right. reflexivity.
  subst. left. apply Righttree. assumption.

  subst. left. constructor. reflexivity.
  left. apply Lefttree. assumption.
  assert (in_bt n2 t2 \/ n2 = n). apply IHt2. assumption.
  destruct H5. subst. left. apply Righttree. assumption.
  right. assumption.
Qed.

Theorem insert_bst : forall t n, bst t -> bst (insert n t).
Proof.
  intros. induction H.
  compute. constructor; intros; try inversion H; try constructor.
  simpl. destruct (n <? n1) eqn:res.
  constructor. intros. apply insert_inversion in H3. destruct H3.
  apply H. assumption. rewrite <- H3 in res. apply Nat.ltb_lt in res.
  assumption. intros. apply H0. assumption. assumption. assumption.

  constructor. assumption. intros. apply insert_inversion in H3.
  destruct H3. apply H0. assumption. rewrite H3. apply Nat.ltb_nlt in res.
  apply not_gt in res. assumption. assumption. assumption.
Qed.

Definition insert_list l := List.fold_right insert Leaf l.

Lemma insert_list_bst : forall l, bst (insert_list l).
Proof.
  intros. induction l. compute. constructor.
  unfold insert_list in *. simpl. apply insert_bst. assumption.
Qed.

Fixpoint marshall t :=
  match t with
  | Leaf => []
  | Node a tl tr =>  (marshall tl) ++ (a :: (marshall tr))
  end.
  
Theorem in_marshall : forall x t, in_bt x t <-> In x (marshall t).
Proof.
  intros. split; intros.
  induction t. inversion H.
  simpl. apply in_app_iff. inversion H.
  subst. right. constructor. reflexivity.
  subst. left. apply IHt1. assumption.
  subst. right. apply in_cons. apply IHt2. assumption.

  induction t. inversion H. simpl in H. apply in_app_iff in H.
  destruct H. apply Lefttree. apply IHt1. assumption.
  simpl in H. destruct H. subst. constructor. reflexivity.
  apply Righttree. apply IHt2. assumption.
Qed.
  
Lemma lt_gt : forall n1 n2, n1 <= n2 <-> n2 >= n1.
Proof.
  intros. split;
  auto with arith.
Qed.
  

Theorem marshall_sorted : forall t, bst t -> LocallySorted le (marshall t).
Proof.
  intros. induction t. compute. constructor.
  simpl. inversion H. subst.
  assert (LocallySorted le (marshall t1)).
  apply IHt1. assumption.
  assert (LocallySorted le (marshall t2)).
  apply IHt2. assumption. 
  apply app_lt_sorted. assumption. assumption.
  intros. assert (a < n). apply H3. apply in_marshall.
  assumption. auto with arith.
  intros. apply lt_gt. apply H4. apply in_marshall. assumption.
Qed.

Definition treesort l :=
  marshall (insert_list l).

Theorem treesort_sorted : forall l, LocallySorted le (treesort l).
Proof.
  intros. unfold treesort. apply marshall_sorted.
  apply insert_list_bst.
Qed.

Fixpoint tree_size t :=
  match t with
  | Leaf => 0
  | Node n tl tr => 1 + (tree_size tl) + (tree_size tr)
  end.

Lemma le_plus_l_elim : forall n m p, n + m <= p -> n <= p.
Proof.
  intros. induction m. rewrite plus_comm in H. simpl in H.
  assumption.
  apply IHm. rewrite plus_comm in H. inversion H.
  rewrite plus_comm. simpl. auto. constructor.
  rewrite plus_comm. apply le_Sn_le. simpl in H0.
  assumption.
Qed.
  
Lemma permutation_append : forall {A : Type} (l1 l2 l3 l4  : list A) a,
    Permutation l1 l2 -> Permutation l3 l4 ->
    Permutation (a :: (l1 ++ l3)) (l2 ++ (a :: l4)).
Proof.
  intros. apply Permutation_cons_app. apply Permutation_app.
  assumption. assumption.
Qed.

Lemma insert_permutation : forall a t,
    Permutation (a :: (marshall t))
                (marshall (insert a t)).
Proof.
  intros. remember (tree_size t) as n.
  assert ((tree_size t) <= n). rewrite Heqn. constructor.
  clear Heqn. generalize dependent t. induction n; intros.
  destruct t. auto.
  inversion H.

  destruct t. auto. simpl. destruct (a <? n0). simpl.
  assert (Permutation (a :: (marshall t1)) (marshall (insert a t1))).
  apply IHn. simpl in H. apply le_S_n in H. apply le_plus_l_elim in H.
  assumption. remember (n0 :: (marshall t2)) as l2.
  apply Permutation_app_tail with (tl := l2) in H0.
  simpl in H0. assumption.

  simpl.
  assert (Permutation (a :: marshall t2) (marshall (insert a t2))).
  apply IHn. simpl in H. apply le_S_n in H.
  rewrite plus_comm in H. apply le_plus_l_elim in H. assumption.
  remember (n0 :: marshall (insert a t2)) as x.
  remember (marshall t1) as y.
  assert
    (Permutation (a :: y ++ n0 :: (marshall t2)) (y ++ a :: n0 :: (marshall t2))).
  apply Permutation_cons_app. auto.
  apply Permutation_trans with (l' := (y ++ a :: n0 :: marshall t2)).
  assumption. rewrite Heqx. rewrite Heqy. apply Permutation_app.
  auto. assert (Permutation (a :: n0 :: marshall t2) (n0 :: a :: marshall t2)).
  apply perm_swap. apply Permutation_trans with (l' := (n0 :: a :: marshall t2)).
  assumption. constructor. assumption.
Qed.


Theorem treesort_permutation : forall l, Permutation l (treesort l).
Proof.
  intros. induction l. auto.
  unfold treesort in *. simpl.
  assert (Permutation (a :: marshall (insert_list l))
                      (marshall (insert a (insert_list l)))).
  apply insert_permutation.
  apply Permutation_trans with (l' := (a :: marshall (insert_list l))).
  constructor. assumption. assumption.
Qed.
