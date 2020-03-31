Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

Require Import Nat. 
From mathcomp.finmap
Require Import finmap.

From Dynamic
Require Import Validator HashTree State Slashing Quorums.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Tactic Notation "spec" hyp(H) :=
  match type of H with ?a -> _ => 
    let H1 := fresh in (assert (H1: a); [|generalize (H H1); clear H H1; intro H]) end.
Tactic Notation "spec" hyp(H) constr(a) :=
  (generalize (H a); clear H; intro H). 
Tactic Notation "spec" hyp(H) constr(a) constr(b) :=
  (generalize (H a b); clear H; intro H).

(* Definitions of justification and finalization *)

(* The set of validators voted for a given link *)
Definition link_supporters st s t s_h t_h : {set Validator} :=
  [set v | vote_msg st v s t s_h t_h ].

(* The assumption that votes originate only from the vset of the target block
   being voted for (Needed for liveness) *)
Axiom votes_from_target_vset: forall x st s s_h t t_h, 
  x \in link_supporters st s t s_h t_h -> x \in vSet.[vs_fun t].

(* The voter set for a link constitute a supermajority *)
Definition supermajority_link (st:State) (s t : Hash) (s_h t_h : nat) : bool :=
  quorum_2 (link_supporters st s t s_h t_h) t.

(* Adding more votes (from the same validators) to a state preserves supermajority links *)
(** Note: Needed the assumption that the extra votes must have come from vSet.[target] **)
Lemma supermajority_weaken: forall (st st':State) s t s_h t_h
  (HSub:forall (v: Vote), v \in st -> v \in st'),
      supermajority_link st s t s_h t_h
      -> supermajority_link st' s t s_h t_h.
Proof.
  move=> st st' s t s_h t_h Hsub.
  unfold supermajority_link, link_supporters, vote_msg.
  apply quorum_2_upclosed.
    apply/subsetP. intro. rewrite in_set. rewrite in_set.
    apply Hsub.
  apply/subsetP. intro.
  apply votes_from_target_vset.
Qed.

Definition justification_link (st:State) (s t : Hash) (s_h t_h : nat) : Prop :=
  t_h > s_h /\
  nth_ancestor (t_h - s_h) s t /\
  supermajority_link st s t s_h t_h.

(* We define justification of a block inductively in terms of a path
   from the genesis block all the way to that block.
 *)
Inductive justified (st:State) : Hash -> nat -> Prop :=
| justified_genesis : justified st genesis 0
| justified_link : forall s s_h t t_h,
    justified st s s_h ->
    justification_link st s t s_h t_h ->
    justified st t t_h.

(* Justification is preserved when the state is expanded with new votes
   (coming from validators in the v-set of the justified block) *)
Lemma justified_weaken: forall (st st':State) t t_h
    (HSub:forall (v: Vote), v \in st -> v \in st'),
  justified st t t_h -> justified st' t t_h.
Proof.
  move=> st st' t t_h Hsub.
  induction 1. constructor.
  destruct H0 as [Hh [Ha Hsm]].
  apply (justified_link IHjustified).
  unfold justification_link;repeat (split; try assumption).
  revert Hsm.
  apply supermajority_weaken. assumption.
Qed.

(* A finalized block is a justified block that has a child who is also
   justified by a supermajority link to the block *)
Definition finalized st b b_h :=
  justified st b b_h /\
  exists c, (b <~ c /\ supermajority_link st b c b_h b_h.+1).

(* A k-finalized block is a justified block that has a k-descendent who is also justified by a supermajority link to the block, and all blocks to the descendent are also justified *)
Definition k_finalized st b b_h k :=
  k >= 1 /\ 
  exists ls, size ls = k.+1 /\
        head b ls = b /\
        (forall n, n <= k ->
              justified st (nth b ls n) (b_h+n) /\
              nth_ancestor n b (nth b ls n)
        ) /\
        supermajority_link st b (last b ls) b_h (b_h+k). 

Lemma leq_one_means_zero_or_one : forall n,
    n <= 1 -> n = 0 \/ n = 1. 
Proof.
  intros n H_leq.
  induction n. left; reflexivity.
  spec IHn. intuition. destruct IHn. right.
  subst. easy. subst. inversion H_leq.
Qed.

(* 1-finalized <-> k-finalized *)
Lemma finalized_means_one_finalized : forall st b b_h,
    finalized st b b_h <->
    k_finalized st b b_h 1. 
Proof.
  intros st b b_h.
  split; intro Hfin. 
  (* -> *)
  destruct Hfin as [Hjust [c [H_rel H_link]]]. 
  split. 
  easy.
  exists [::b;c].  
  repeat split.
  apply leq_one_means_zero_or_one in H.
  destruct H as [H_zero | H_one]; subst. 
  simpl. rewrite <- plus_n_O. exact Hjust. 
  apply justified_link with b b_h. exact Hjust.
  repeat split. rewrite <- addn1.
  easy. rewrite Minus.minus_plus.
  apply parent_ancestor. assumption.
  rewrite PeanoNat.Nat.add_1_r. exact H_link.
  apply leq_one_means_zero_or_one in H.
  destruct H as [H_zero | H_one]; subst. 
  simpl. apply nth_ancestor_0.
  simpl. apply parent_ancestor. exact H_rel.
  simpl. rewrite PeanoNat.Nat.add_1_r. exact H_link.
  (* <- *)
  destruct Hfin as [H_k [ls [H_size [H_hd [H_rel H_link]]]]].
  split. spec H_rel 0. spec H_rel. easy. destruct H_rel as [H_just H_an].
  rewrite <- nth0 in H_hd.
  rewrite H_hd in H_just.
  rewrite PeanoNat.Nat.add_0_r in H_just.
  exact H_just.
  spec H_rel 1. 
  spec H_rel. easy.
  destruct H_rel as [H_just H_an].
  exists (nth b ls 1). split.
  inversion H_an; subst.
  apply parent_ancestor. exact H_an. 
  rewrite <- nth_last in H_link. 
  rewrite H_size in H_link.
  replace (2.-1) with 1 in H_link by auto.
  rewrite PeanoNat.Nat.add_1_r in H_link.
  assumption.
Qed. 

(* A k-finalized block is justified *)
Lemma k_finalized_means_justified: forall st b b_h k,
    k_finalized st b b_h k ->
    justified st b b_h. 
Proof. 
  intros st b b_h k [H_k [ls [H_size [H_hd [H_rel H_link]]]]].
  spec H_rel 0. spec H_rel.
  easy. destruct H_rel.
  rewrite <- nth0 in H_hd.
  rewrite H_hd in H.
  replace (b_h + 0) with b_h in H.
  assumption.
  rewrite PeanoNat.Nat.add_0_r. reflexivity.
Qed. 

(* A finalized block has a child who is justified *)
Lemma finalized_means_justified_child: forall st p p_h,
  finalized st p p_h -> exists c, p <~ c /\ justified st c p_h.+1.
Proof.
intros st p p_h Hfin.
unfold finalized in Hfin.
destruct Hfin as [Hjustified_p Hchild].
destruct Hchild as [c [Hc_parent Hc_sm]].
exists c. split. assumption.
assert (Hpc := parent_ancestor p c). 
destruct Hpc as [Hp _].
spec Hp Hc_parent. 
have Hc_h : p_h.+1 > p_h by trivial.
have Hjl : justification_link st p c p_h p_h.+1. split.
assumption. split. 2: assumption.
rewrite <- Minus.minus_Sn_m.
rewrite PeanoNat.Nat.sub_diag. assumption.
by trivial.
apply (justified_link Hjustified_p Hjl).
Qed.
