Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

From Casper
Require Import Quorums HashTree State.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Now we define justification *)
(* First a definition of supermajority links *)
Definition link_supporters st s t s_h t_h : {set Validator} :=
  [set v | vote_msg st v s t s_h t_h ].

Definition supermajority_link (st:State) (s t : Hash) (s_h t_h : nat) : Prop :=
  link_supporters st s t s_h t_h \in quorum_2.
  
Lemma supermajority_weaken: forall (st st':State)
  (HSub:forall (v: Vote), v \in st -> v \in st'),
    forall s t s_h t_h,
      supermajority_link st s t s_h t_h
      -> supermajority_link st' s t s_h t_h.
Proof.
  move=> st st' Hsub s t s_h t_h.
  unfold supermajority_link, link_supporters, vote_msg.
  apply quorum_2_upclosed.
  apply/subsetP. intro. rewrite in_set. rewrite in_set.
  apply Hsub. 
Qed.

(* We define justification of a block inductively in terms of a path from 
   the genesis block all the way to that block.
 *)
Inductive justified (st:State) : Hash -> nat -> Prop :=
| justified_genesis : justified st genesis 0
| justified_link : forall s s_h t t_h,
    justified st s s_h ->
    t_h > s_h ->
    nth_ancestor (t_h - s_h) s t ->
    supermajority_link st s t s_h t_h ->
    justified st t t_h.

(* Some properties of justification *)
Lemma justified_weaken: forall (st st':State)
    (HSub:forall (v: Vote), v \in st -> v \in st'),
  forall t t_h, justified st t t_h -> justified st' t t_h.
Proof.
  move=> st st' Hsub t t_h.
  induction 1. constructor.
  apply (justified_link IHjustified).
  assumption. assumption.
  revert H2.
  apply supermajority_weaken.
  assumption.
Qed.

(* a finalized block is a justified block that has a child who is also justified 
   by a supermajority link to the block *)
Definition finalized st b b_h :=
  justified st b b_h /\ 
  exists c, (b <~ c /\ supermajority_link st b c b_h b_h.+1).

Lemma finalized_means_justified_child: forall st p p_h,
  finalized st p p_h -> exists c, p <~ c /\ justified st c p_h.+1.
Proof.
intros st p p_h Hfin.
unfold finalized in Hfin.
destruct Hfin as [Hjustified_p Hchild].
destruct Hchild as [c [Hc_parent Hc_sm]].
exists c. split. assumption.
have Hp := parent_ancestor Hc_parent.
have Hc_h : p_h.+1 > p_h by trivial.
replace 1 with (p_h.+1 - p_h) in Hp by (rewrite subSnn;reflexivity).
apply (justified_link Hjustified_p Hc_h Hp Hc_sm).
Qed.
