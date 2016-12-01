Require Import List.
Import ListNotations.
Set Implicit Arguments.
Require Import Coq.Program.Wf.
Require Import Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Combinators.
Import WfExtensionality.

Inductive bt :=
| Leaf : bt
| Node : nat -> bt -> bt -> bt.

Check Node 100 Leaf Leaf.

Inductive in_bt : nat -> bt -> Prop :=
| Curnode : forall n1 n2 tl tr, n1 = n2 -> in_bt n1 (Node n2 tl tr)
| Lefttree : forall n1 n2 tl tr, in_bt n1 tl -> in_bt n1 (Node n2 tl tr)
| Righttree : forall n1 n2 tl tr, in_bt n1 tr -> in_bt n1 (Node n2 tl tr).

Inductive bst : bt -> Prop :=
| BSTLeaf : bst Leaf
| BSTNode : forall n1 tl tr, (forall n2, in_bt n2 tl -> n2 < n1)
                        -> (forall n2, in_bt n2 tl -> n2 >= n1)
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
  constructor. inversion H1. subst. intros. 
