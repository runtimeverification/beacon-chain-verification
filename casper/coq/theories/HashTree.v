Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Note **)
(* We consider the checkpoint tree of blocks, and so a "block" refers
   to a "checkpoint block" throughout the specs below.
 *)

(* We assume finite hash values (block identifiers) *)
Parameter Hash : finType.

(* This relation links blocks (b,b'), written b <~ b', if b is a (the)
   parent of b' in the block tree
 *)
Parameter hash_parent : rel Hash.

Notation "h1 <~ h2" := (hash_parent h1 h2) (at level 50).

(* A block cannot be a parent of itself *)
Axiom hash_parent_irreflexive:
  forall h1 h2, h1 <~ h2 -> h1 <> h2.

(* A block cannot have two parent blocks *)
Axiom hash_at_most_one_parent :
  forall h1 h2 h3, h2 <~ h1 -> h3 <~ h1 -> h2 = h3.

(* The ancestor reltion `<~*`: the reflexive-transitive closure of `<~` *)
Definition hash_ancestor h1 h2 := connect hash_parent h1 h2.

Notation "h1 <~* h2" := (hash_ancestor h1 h2) (at level 50).

Notation "h1 </~* h2" := (~ hash_ancestor h1 h2) (at level 50).

(* The genesis block *)
Parameter genesis : Hash.

(* We will need to use several properties of ancestry
   inherited from the reflexive-transitive closure operation "connect".
   We define these lemmas rather than unfolding the hash_ancestor
   definition inside other proofs.
 *)

(* A block is an ancestor of itself *)
Lemma hash_self_ancestor :
  forall h, h <~* h.
Proof.
by apply/connect0.
Qed.

(* A parent block is a proper ancestor block *)
Lemma hash_parent_ancestor :
  forall h1 h2,
    h1 <~ h2 -> h1 <~* h2 /\ h1 <> h2.
Proof.
split.
by apply/connect1.
by apply/hash_parent_irreflexive.
Qed.

(* A parent of an ancestor is an ancestor *)
Lemma hash_ancestor_stepL :
  forall h1 h2 h3,
    h1 <~ h2 -> h2 <~* h3 -> h1 <~* h3.
Proof.
move => h1 h2 h3.
move/connect1.
by apply/connect_trans.
Qed.

(* An ancestor of a parent is an ancestor *)
Lemma hash_ancestor_stepR :
  forall h1 h2 h3,
    h1 <~* h2 -> h2 <~ h3 -> h1 <~* h3.
Proof.
move => h1 h2 h3 H1 H2.
apply: connect_trans; eauto.
by apply/connect1.
Qed.

(* An ancestor of an ancestor is an ancestor *)
Lemma hash_ancestor_concat :
  forall h1 h2 h3,
    h1 <~* h2 -> h2 <~* h3 -> h1 <~* h3.
Proof.
move => h1 h2 h3 H2 H1.
by apply: connect_trans; eauto.
Qed.

(* A block can never conflict with itself *)
Lemma hash_nonancestor_nonequal:
  forall h1 h2,
    h1 </~* h2 -> h1 <> h2.
Proof.
intros h1 h2 Hna.
contradict Hna.
replace h1 with h2.
apply hash_self_ancestor.
Qed.

(* A conflicting block cannot belong to the ancestry of that block *)
Lemma hash_ancestor_conflict:
  forall h1 h2 p,
    h1 <~* h2 -> p </~* h2 -> p </~* h1.
Proof.
move => h1 h2 p H1 H2 Hp.
destruct H2.
move: Hp H1.
by apply/connect_trans.
Qed.

(* This definition of ancestry makes the exact number of steps explicit *)
Inductive nth_ancestor : nat -> Hash -> Hash -> Prop :=
| nth_ancestor_0 : forall h1, nth_ancestor 0 h1 h1
| nth_ancestor_nth : forall n h1 h2 h3,
    nth_ancestor n h1 h2 -> h2 <~ h3 ->
    nth_ancestor n.+1 h1 h3.

(* The nth_ancestor is an ancestor *)
Lemma nth_ancestor_ancestor :
  forall n s t,
    nth_ancestor n s t -> (s <~* t).
Proof.
induction 1.
apply connect0.
apply connect_trans with h2;[|apply connect1];assumption.
Qed.

(* a parent is a first-level ancestor *)
Example parent_ancestor : forall h1 h2,
  h1 <~ h2 -> nth_ancestor 1 h1 h2.
Proof.
move => h1 h2 Hp.
apply: nth_ancestor_nth; eauto.
exact: nth_ancestor_0.
Qed.
