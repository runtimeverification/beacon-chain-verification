Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

From Hammer
Require Reconstr.

Require Import Classical. 

From Casper
Require Import StrongInductionLtn.

From Casper
Require Import Quorums HashTree State Slashing Justification AccountableSafety.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Now we begin making definitions used in the statement and proof of
   the plausible liveness theorem *)

(* The liveness theorem will assume that 2/3 of validators
   have not behaved badly. For liveness it is not sufficient to merely
   say they are unslashed.
   Votes with unjustified sources do not violate any slashing conditions
   themselves, but can prevent a validator from contributing to progress,
   because votes spanning over the unjustified vote would violate
   slashing condition II.
   No correct validator should ever make such a vote.
   We also simplify the problem by forbidding good validators from
   having votes with sources higher than the start of the current epoch
   but not descended from the current epoch.
   In the older casper design with Prepare/Commit messages this was
   prevented by slashing conditions.
 *)
 
(* [Modified: no longer includes the now vacuous conclusion that genesis 
   is an ancestor of s] *)
Definition sources_justified st v :=
  forall s t s_h t_h,
    vote_msg st v s t s_h t_h -> justified st s s_h.

(* This assumption says 2/3 of the validators have behaved well *)
Definition two_thirds_good (st : State) :=
  exists q2, q2 \in quorum_2 /\
  forall v, v \in q2 -> (~ slashed st v /\ sources_justified st v).

(* We also need to assume block proposals continue.
   In particular, our proof requires that blocks exist
   sufficiently high over the highest justified block *)
Definition blocks_exist_high_over (base : Hash) : Prop :=
  forall n, exists block, nth_ancestor n base block /\ n > 1.

(* We also define the property of being the highest justified block *)
Definition highest_justified st b b_h : Prop :=
  forall b' b_h', b_h' >= b_h
  -> justified st b' b_h'
  -> b' = b /\ b_h' = b_h.

(* We assume a highest justified block exists.
   This is left as an unproved assumption for now,
   becasue proving there is only one justified block
   of maximum height would require depending on
   the accountable safety theorem and assumptions of
   good behavior. *)
(* This should be provable in the merged version *)
Lemma highest_exists: forall st,
    exists b b_h,
      justified st b b_h /\
      highest_justified st b b_h.
Admitted.

(** Now we have some defintions used to state the conclusion of the theorem **)
(* First, the solution only calls for votes from unslashed validators. *)
Definition unslashed_can_extend st st' : Prop :=
  forall v s t s_h t_h,
    vote_msg st' v s t s_h t_h = true ->
    vote_msg st v s t s_h t_h = true \/ ~ slashed st v.
(* Second, making the new votes does not cause any previously unslashed
   validator to be slashed *)
Definition no_new_slashed st st' :=
  forall v, slashed st' v -> slashed st v.

(** Now a few minor lemmas and definitions used in the proof **)
Definition highest (A : {fset nat}) : nat :=
  \max_(i : A) (val i).


Lemma highest_ub:
  forall (A : {fset nat}) (x:nat), x \in A -> x <= highest A.
Proof.
move => A x Hx.
case (insubP [subType of A] x) => /=; last by move: Hx =>->.
move => k Hk =><-.
exact: leq_bigmax_cond.
Qed.

Lemma ltSnn: forall n, (n.+1 < n) = false.
Proof.
by move => n; apply/negP/negP; rewrite leqNgt; apply/negP; case/negP.
Qed.

Definition vote_target_height (v:Vote) : nat :=
  match v with
    (_,_,_,_,t_h) => t_h
  end.

(** And finally, the overall plausible liveness theorem **)
Theorem plausible_liveness :
  forall st, two_thirds_good st ->
  (forall b b_h, highest_justified st b b_h -> blocks_exist_high_over b) ->
  exists st', unslashed_can_extend st st'
   /\ no_new_slashed st st'
   /\ exists (new_finalized new_final_child:Hash) new_height,
        justified st' new_finalized new_height
         (* /\ epoch_height < new_height *)
         /\ new_finalized <~ new_final_child
         /\ supermajority_link st' new_finalized new_final_child
                                   new_height new_height.+1.
Proof.
  intros st Hgood Hheight.
  destruct (highest_exists st) as (just_max & just_max_h & [Hjust_max_just Hjust_max_max]).
  specialize (Hheight _ _ Hjust_max_max).

  destruct Hgood as (good_quorum & Hgood_is_quorum & Hgood).

  pose targets := (0 |` [ fset vote_target_height vote | vote in st])%fset;
                    change {fset nat} in (type of targets).
  
  (* perhaps *)
  (* pose targets := ([ fset vote_target_height vote | vote in st])%fset;
                    change {fset nat} in (type of targets). *)

  pose highest_target := highest targets.
  destruct (Hheight ((highest_target.+1 - just_max_h)).+1) as [new_final_child [Hpath Hdist]].
  inversion Hpath;subst. rename h2 into new_finalized.

  pose new_votes1 := [fset (v,just_max,new_finalized,just_max_h,highest_target.+1)
                     | v in good_quorum]%fset; change {fset Vote} in (type of new_votes1).
  pose new_votes2 := [fset (v,new_finalized,new_final_child,highest_target.+1,highest_target.+2)
                     | v in good_quorum]%fset; change {fset Vote} in (type of new_votes2).

  exists (st `|` new_votes1 `|` new_votes2)%fset.
  split;[|split].

  *
  unfold unslashed_can_extend.
  clear -Hgood.
  unfold vote_msg.
  intros v s t s_h t_h.
  rewrite in_fsetU. rewrite in_fsetU.
  rewrite !Bool.orb_true_iff.
  move => [[H|H] | H];[tauto|right;apply Hgood..].
  case/imfsetP: H => x Hx Heq. replace v with x. assumption. congruence.
  case/imfsetP: H => x Hx Heq. replace v with x. assumption. congruence.

  pose proof (@highest_ub targets).
  assert (forall v s t s_h t_h, (v,s,t,s_h,t_h) \in st -> t_h <= highest_target)
    as H_st_highest by
   (clear;intros;apply highest_ub;
    apply/fsetUP;right;revert H;apply in_imfset).

  *
  Local Ltac new_vote_mem_tac Hvote :=
    let x := fresh "x" in
    let x_good := fresh "x_good" in
    let Heq := fresh "Heq" in
    case/imfsetP: Hvote => x x_good Heq;injection Heq;clear Heq;intros;subst x;subst.

  assert (forall n n_h, justified st n n_h -> n_h <= highest_target)
    as Hjust_le_target by
     (clear;intros n n_h H;
     apply highest_ub;destruct H;[by apply fset1U1|];
     destruct (quorum_2_nonempty H2) as [t_supporter Ht];
     rewrite in_set in Ht; apply/fsetUP; right;
     revert Ht; apply in_imfset).

  unfold no_new_slashed.
  intros badV [Hdbl|Hnest];[left|right].
  (* slashed for double vote *)
  unfold slashed_dbl_vote, vote_msg in Hdbl |- *.
  destruct Hdbl as (t1 & t2 & Hneq_t & Hdouble_votes).
  exists t1. exists t2. split;[exact Hneq_t|].
  destruct Hdouble_votes as (s1 & s1_h & s2 & s2_h & t_h & Hvote1 & Hvote2).
  exists s1; exists s1_h; exists s2; exists s2_h; exists t_h.

  rewrite in_fsetU in Hvote1;case/orP: Hvote1 => Hvote1.
  rewrite in_fsetU in Hvote1;case/orP: Hvote1 => Hvote1.
  split;[assumption|].
  apply H_st_highest in Hvote1.

  rewrite in_fsetU in Hvote2;case/orP: Hvote2 => Hvote2.
  rewrite in_fsetU in Hvote2;case/orP: Hvote2 => Hvote2.
  assumption.
  new_vote_mem_tac Hvote2.
  contradict Hvote1;clear. rewrite ltnn. trivial.
  new_vote_mem_tac Hvote2.
  contradict Hvote1;clear. rewrite ltSnn. trivial.

  rewrite in_fsetU in Hvote2;case/orP: Hvote2 => Hvote2.
  rewrite in_fsetU in Hvote2;case/orP: Hvote2 => Hvote2.
  split;[|assumption].
  apply H_st_highest in Hvote2.
  new_vote_mem_tac Hvote1.
  rewrite ltnn in Hvote2. solve[auto].

  new_vote_mem_tac Hvote1.
  new_vote_mem_tac Hvote2.
  contradict Hneq_t. reflexivity.

  new_vote_mem_tac Hvote1.
  new_vote_mem_tac Hvote2.
  contradict H2. solve[apply n_Sn].

  rewrite in_fsetU in Hvote2;case/orP: Hvote2 => Hvote2.
  rewrite in_fsetU in Hvote2;case/orP: Hvote2 => Hvote2.
  split;[|assumption].
  apply H_st_highest in Hvote2.
  new_vote_mem_tac Hvote1.
  contradict Hvote2;clear. rewrite ltSnn. trivial.

  new_vote_mem_tac Hvote1.
  new_vote_mem_tac Hvote2.
  symmetry in H2. solve[case/n_Sn: H2].

  new_vote_mem_tac Hvote1.
  new_vote_mem_tac Hvote2.
  clear -Hneq_t. congruence.

  (* slashed surround case *)
  unfold slashed_surround in Hnest |- *.
  destruct Hnest as (s1 & t1 & s1_h & t1_h & s2 & t2 & s2_h & t2_h & Hnest).
  exists s1;exists t1;exists s1_h;exists t1_h;exists s2;exists t2;exists s2_h;exists t2_h.
  destruct Hnest as (Houter & Hinner & Hstarts & Hends).
  rewrite <- and_assoc. split;[|split;assumption].

  unfold vote_msg in * |- *.
  rewrite in_fsetU in Houter;case/orP: Houter => Houter.
  rewrite in_fsetU in Houter;case/orP: Houter => Houter.
  split;[assumption|].
  apply H_st_highest in Houter.

  rewrite in_fsetU in Hinner;case/orP: Hinner => Hinner.
  rewrite in_fsetU in Hinner;case/orP: Hinner => Hinner.
  assumption.

  new_vote_mem_tac Hinner.
  clear -Hends Houter.
  assert (t1_h < t1_h) by (apply ltn_trans with (highest_target.+1);assumption).
  rewrite ltnn in H. contradict H. solve[trivial].

  new_vote_mem_tac Hinner.
  clear -Hends Houter.
  assert (t1_h < t1_h).
  apply ltn_trans with (highest_target.+1).
  assumption. apply ltn_trans with (highest_target.+2). apply ltnSn. assumption.
  contradict H. rewrite ltnn. solve[trivial].

  rewrite in_fsetU in Hinner;case/orP: Hinner => Hinner.
  rewrite in_fsetU in Hinner;case/orP: Hinner => Hinner.
  split;[|assumption].

  new_vote_mem_tac Houter.
  change (is_true (badV \in good_quorum)) in x_good.

  apply Hgood in x_good. destruct x_good as [Hnot_slashed Hsources_justified].
  apply Hsources_justified in Hinner as Hst2_justified. 
  clear -Hjust_max_max Hst2_justified Hstarts.
  apply Hjust_max_max in Hst2_justified;[|apply ltnW;assumption].
  destruct Hst2_justified.
  contradict Hstarts.
  rewrite -H0. rewrite ltnn. trivial.

  new_vote_mem_tac Houter.
  new_vote_mem_tac Hinner.
  contradict Hstarts. clear. rewrite ltnn. trivial.

  new_vote_mem_tac Houter.
  new_vote_mem_tac Hinner.
  contradict Hends. clear. rewrite ltSnn. trivial.

  rewrite in_fsetU in Hinner;case/orP: Hinner => Hinner.
  rewrite in_fsetU in Hinner;case/orP: Hinner => Hinner.
  split;[|assumption].

  new_vote_mem_tac Houter.
  apply Hgood in x_good. destruct x_good as [_ x_good].
  apply x_good in Hinner as Hs2_justified.
  apply Hjust_le_target in Hs2_justified.
  clear -Hstarts Hs2_justified.
  rewrite <- ltnS in Hs2_justified.
  assert (s2_h < s2_h). apply ltn_trans with highest_target.+1;assumption.
  contradict H. rewrite ltnn. trivial.

  new_vote_mem_tac Houter.
  new_vote_mem_tac Hinner.
  exfalso.
  apply Hjust_le_target in Hjust_max_just.
  clear -Hjust_max_just Hstarts.
  rewrite <- ltnS in Hjust_max_just.
  assert (just_max_h < just_max_h).
  eapply ltn_trans;eassumption.
  contradict H. rewrite ltnn. trivial.

  new_vote_mem_tac Houter.
  new_vote_mem_tac Hinner.
  contradict Hstarts. clear.
  rewrite ltnn. trivial.

  * exists new_finalized. exists new_final_child. exists (highest_target.+1).
    split.

    apply (@justified_link _ just_max just_max_h).
      revert Hjust_max_just. apply justified_weaken.
      apply/fsubsetP. by eapply fsubset_trans;apply fsubsetUl.
    
    rewrite <- addn1 with (highest_target.+1 - just_max_h) in Hdist.
    replace 1 with (0 + 1) in Hdist at 1 by trivial.
    rewrite -> ltn_add2r with 1 0 (highest_target.+1 - just_max_h) in Hdist.
    revert Hdist.
    rewrite subn_gt0. trivial.
    
    assumption.

    unfold supermajority_link, link_supporters, vote_msg.
    apply quorum_2_upclosed with good_quorum;[|assumption].
    apply /subsetP.
    intros v Hv_good.
    rewrite in_set. rewrite in_fsetU.
    apply/orP. left. rewrite in_fsetU.
    apply/orP. right. unfold new_votes1.
    apply/imfsetP. exists v.
      assumption. reflexivity.

    split.
    assert (0 <= highest_target).
    apply highest_ub.
    rewrite in_fsetU. apply/orP. left. apply fset11. by auto with arith.

    (* split. assumption. *)

    unfold supermajority_link, link_supporters, vote_msg.
    apply quorum_2_upclosed with good_quorum;[|assumption].
    apply /subsetP.
    intros v Hv_good.
    rewrite in_set. rewrite in_fsetU.
    apply/orP. right. unfold new_votes2.
    apply/imfsetP. exists v.
      assumption. reflexivity.
Qed.

