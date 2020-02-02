Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* We consider the checkpoint tree of blocks, and so a "block" refers to a 
   "checkpoint block" throughout the specs below. *)

Parameter Hash : finType.

(* This relation links blocks (b,b') if b is an ancestor of b' and
   b' is at the next checkpoint level above b *)
Parameter hash_parent : rel Hash.

Notation "h1 <~ h2" := (hash_parent h1 h2) (at level 50).

Axiom hash_parent_irreflexive: 
  forall h1 h2, h1 <~ h2 -> h1 <> h2.

Definition hash_ancestor h1 h2 :=
 connect hash_parent h1 h2.

Notation "h1 <~* h2" := (hash_ancestor h1 h2) (at level 50).

Notation "h1 </~* h2" := (~ hash_ancestor h1 h2) (at level 50).

(* a hash can have one parent *)
Axiom hash_at_most_one_parent :
  forall h1 h2 h3, h2 <~ h1 -> h3 <~ h1 -> h2 = h3.

(* The genesis block. *)
Parameter genesis : Hash.

(* [ADDED] *)
Axiom genesis_ancestor :
  forall h, genesis <~* h.

(* We will need to use several property of ancestry
   inherited from the transitive closure operation "connect".
   We define these lemmas rather than unfolding the hash_ancestor
   definition inside other proofs.
 *)

Lemma hash_self_ancestor :
  forall h, h <~* h.
Proof.
by apply/connect0.
Qed.

Lemma hash_parent_ancestor : 
  forall h1 h2,
    h1 <~ h2 -> h1 <~* h2 /\ h1 <> h2.
Proof.
split.
by apply/connect1.
by apply/hash_parent_irreflexive.
Qed.

Lemma hash_ancestor_stepL : 
  forall h1 h2 h3,
    h1 <~ h2 -> h2 <~* h3 -> h1 <~* h3.
Proof.
move => h1 h2 h3.
move/connect1.
by apply/connect_trans.
Qed.

Lemma hash_ancestor_stepR :
  forall h1 h2 h3, 
    h1 <~* h2 -> h2 <~ h3 -> h1 <~* h3.
Proof.
move => h1 h2 h3 H1 H2.
apply: connect_trans; eauto.
by apply/connect1.
Qed.

Lemma hash_ancestor_concat :
  forall h1 h2 h3, 
    h1 <~* h2 -> h2 <~* h3 -> h1 <~* h3.
Proof.
move => h1 h2 h3 H2 H1.
by apply: connect_trans; eauto.
Qed.

Lemma hash_nonancestor_nonequal:
  forall h1 h2,
    h1 </~* h2 -> h1 <> h2.
Proof.
intros h1 h2 Hna.
contradict Hna.
replace h1 with h2.
apply hash_self_ancestor.
Qed.

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

(* The nth_ancestor of t is an ancestor of t *)

(* [This is roughly ancestor_means in A.S.] *)
Lemma nth_ancestor_ancestor : 
  forall n s t,
    nth_ancestor n s t -> (s <~* t).
Proof.
  induction 1.
  apply connect0.
  apply connect_trans with h2;[|apply connect1];assumption.
Qed.

(* a parent is a first ancestor *)
Example parent_ancestor : forall h1 h2,
  h1 <~ h2 -> nth_ancestor 1 h1 h2.
Proof.
move => h1 h2 Hp.
apply: nth_ancestor_nth; eauto.
exact: nth_ancestor_0.
Qed.
