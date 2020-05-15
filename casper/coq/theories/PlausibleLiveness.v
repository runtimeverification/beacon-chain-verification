Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

Require Import Classical.

From Casper
Require Import NatExt StrongInductionLtn.

From Casper
Require Import Validator Weight HashTree State Slashing Quorums Justification AccountableSafety.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* The plausible liveness theorem                                             *)
(*                                                                            *)
(* The liveness theorem will assume that 2/3 of validators have not behaved   *)
(* badly. For liveness it is not sufficient to merely say that a 1/3 quorum   *)
(* is unslashed. Votes with unjustified sources or ones that do not represent *)
(* proper forward links in the checkpoint tree do not violate any slashing    *)
(* conditions themselves, but can prevent a validator from contributing to    *)
(* progress, because votes spanning over such bad votes would violate         *)
(* slashing condition II. No correct validator should ever make such votes.   *)
(******************************************************************************)

(* A few minor lemmas and definitions used in the proof *)

(* Votes have justified sources *)
Definition justified_source_votes st v :=
  forall s t s_h t_h,
    vote_msg st v s t s_h t_h -> justified st s s_h.

(* Votes constitute valid forward links *)
Definition forward_link_votes st v :=
  forall s t s_h t_h,
    vote_msg st v s t s_h t_h ->
    t_h > s_h /\ nth_ancestor (t_h - s_h) s t.

(* Votes made by 2/3-quorum validators are all good
   (holds globally for all blocks) *)
Definition good_votes (st : State) :=
  forall b q2, quorum_2 q2 b ->
    forall v, v \in q2 ->
    justified_source_votes st v /\ forward_link_votes st v.

(* There exists a 2/3-quorum that have behaved well
   (for every block!) *)
Definition two_thirds_good (st : State) :=
  forall b, exists q2, quorum_2 q2 b /\
    forall v, v \in q2 -> ~ slashed st v.

(* Blocks exist sufficiently high over the given block *)
Definition blocks_exist_high_over (base : Hash) : Prop :=
  forall n, exists block, nth_ancestor n base block /\ n > 1.

(* The property of being the highest justified block *)
Definition highest_justified st b b_h : Prop :=
  forall b' b_h', b_h' >= b_h
  -> justified st b' b_h'
  -> b' = b /\ b_h' = b_h.

(* There exists a justification link with a justified source *)
Definition has_justification_link (st : State) : Prop :=
  exists s t s_h t_h, justified st s s_h /\ justification_link st s t s_h t_h.

(* The property of being a maximal justification link *)
Definition maximal_justification_link st s t s_h t_h : Prop :=
  justification_link st s t s_h t_h /\
  forall s' t' s_h' t_h', justification_link st s' t' s_h' t_h' -> t_h' <= t_h.

(* When votes are assumed good, the source of a justifiction link is
   always justified *)
Lemma good_votes_mean_source_justified : forall st s t s_h t_h,
  good_votes st ->
  justification_link st s t s_h t_h ->
  justified st s s_h.
Proof.
  intros st s t s_h t_h Hgood Hjlink.
  unfold good_votes in Hgood.
  destruct Hjlink as [Hh [Hnth Hsm]].
  unfold supermajority_link in Hsm.
  specialize Hgood with (q2 := link_supporters st s t s_h t_h).
  have Hstgood := (Hgood t Hsm). clear Hgood.
  destruct (quorum_2_nonempty Hsm) as [v Hv].
  have [H _] := (Hstgood v Hv). clear Hstgood.
  rewrite in_set in Hv.
  by apply H in Hv.
Qed.

(* A maximal justification link always exists if we assume good votes
   that make up at least one justification link. *)
Lemma maximal_link_exists: forall st,
  good_votes st ->
  has_justification_link st ->
  exists s t s_h t_h, maximal_justification_link st s t s_h t_h.
Proof.
  intros st Hgood Hjust.
  pose sm_votes : {fset Vote} :=
    [ fset vote:Vote in st |
      supermajority_link st (vote_source vote)
                            (vote_target vote)
                            (vote_source_height vote)
                            (vote_target_height vote) ]%fset.
  pose sm_votes_targets := [ fset vote_target_height vote | vote in sm_votes]%fset.
  pose highest_sm_target := highest sm_votes_targets.
  pose maximal_sm_votes : {fset Vote} :=
    [ fset vote:Vote in sm_votes | (vote_target_height vote) >= highest_sm_target]%fset.
  (* sm_votes is non-empty. *)
  move:(Hjust) =>[s [t [s_h [t_h [_]]]]]>[_ [_ Hlink]].
  move:(Hlink) => /quorum_2_nonempty [v].
  rewrite inE => Hvote.
  assert ((v,s,t,s_h,t_h) \in sm_votes) as H_sm_votes_ne.
    by rewrite inE /= inE /= unfold_in;apply/andP.
  (* sm_votes_targets is non-empty *)
  assert (vote_target_height (v,s,t,s_h,t_h) \in sm_votes_targets) as H_sm_votes_targets_ne.
    by apply in_imfset.
  (* highest_sm_target \in sm_votes_targets *)
  lapply (eq_bigmax (val: sm_votes_targets -> nat));
    [|by rewrite -cardfE cardfs_gt0;apply /fset0Pn;exists (vote_target_height (v, s, t, s_h, t_h)) ].
  move => [i Hmax].
  match type of Hmax with (?L = _) => assert (L = highest_sm_target) by reflexivity end.
  assert (highest_sm_target \in sm_votes_targets).
    rewrite -H Hmax. apply fsvalP.
  (* maximal_sm_votes is non-empty *)
  move:(H0) => /imfsetP /= [maximal_vote Hin Hval].
  assert (maximal_vote \in maximal_sm_votes).
    by rewrite inE /= inE Hval leqnn Bool.andb_true_r.
  (* a maximal supermajority link exists *)
  move:H1;rewrite inE /= inE /=. move/andP=>[Hmax_sm Hmax_h].
  move:Hmax_sm; rewrite inE /= inE /=. move/andP=>[Hmax_vote Hmax_sm].
  exists (vote_source maximal_vote),
         (vote_target maximal_vote),
         (vote_source_height maximal_vote),
         (vote_target_height maximal_vote).
  rewrite /maximal_justification_link. split.
    (* the link is a proper justification link *)
    rewrite /good_votes in Hgood. rewrite /supermajority_link in Hmax_sm.
    specialize (Hgood (vote_target maximal_vote)
                      (link_supporters st (vote_source maximal_vote)
                                          (vote_target maximal_vote)
                                          (vote_source_height maximal_vote)
                                          (vote_target_height maximal_vote))).
    have Hvgood := (Hgood Hmax_sm).
    specialize Hvgood with (v := (vote_val maximal_vote)).
    unfold link_supporters, vote_msg in Hvgood.
    rewrite inE in Hvgood.
    rewrite (vote_unfold maximal_vote) in Hmax_vote.
    have Hvgood_votes:= (Hvgood Hmax_vote).
    move:Hvgood_votes=>[_ Hf].
    rewrite /forward_link_votes in Hf.
    have [Hh Hnth]:= (@Hf (vote_source maximal_vote) (vote_target maximal_vote) (vote_source_height maximal_vote) (vote_target_height maximal_vote) Hmax_vote).
    rewrite /justification_link. repeat (split; try assumption).
  (* the link is maximal *)
  move=> s' t' s_h' t_h' [Hh' [Hsj' Hsm']].
  move:(Hsm') => /quorum_2_nonempty [v'].
  rewrite inE => Hvote'.
  assert ((v',s',t',s_h',t_h') \in sm_votes).
    by rewrite inE /= inE /= unfold_in;apply/andP.
  assert (vote_target_height (v',s',t',s_h',t_h') \in sm_votes_targets).
    by apply in_imfset.
  simpl in H2.
  rewrite -Hval. rewrite /highest_sm_target. apply (highest_ub H2).
Qed.

(* Assuming good behavior, the target of a maximal justification link
   is a maximal-hight justified block. *)
Lemma maximal_link_highest_block: forall st s t s_h t_h b b_h,
  ~ q_intersection_slashed st ->
  good_votes st ->
  maximal_justification_link st s t s_h t_h ->
  justified st b b_h ->
  b_h >= t_h ->
  b = t /\ b_h = t_h.
Proof.
  intros st s t s_h t_h b b_h Hunslashed Hgood Hmaxjl Hbj Hbh.
  destruct Hmaxjl as [Hjl Hmaxjl].
  have Hsj := (good_votes_mean_source_justified Hgood Hjl).
  have Htj := (justified_link Hsj Hjl).
  case Heqh: (b_h == t_h).
    move/eqP: Heqh => Heqh.
    subst.
    split;[|reflexivity].
    have Hsafe := (no_two_justified_same_height Hbj Htj Hunslashed).
    have Ho: b = t \/ ~ b = t by apply classic.
    case: Ho => // Ho;first last.
    apply Hsafe in Ho.
    by contradiction.
  move/eqP: Heqh => Heqh.
  destruct Hbj.
    rewrite leqn0 in Hbh.
    move/eqP: Hbh => Hbh. subst.
    contradict Heqh. reflexivity.
  apply Hmaxjl in H.
  contradict Heqh.
  have Heq: (t_h0 <= t_h) /\ (t_h <= t_h0) by auto.
  move/andP: Heq => Heq.
  rewrite <- eqn_leq in Heq.
  move/eqP: Heq => Heq. assumption.
Qed.

(* Assuming good behavior, the highest justified block exists. *)
Lemma highest_exists: forall st,
  ~ q_intersection_slashed st ->
  good_votes st ->
  exists b b_h,
    justified st b b_h /\
    highest_justified st b b_h.
Proof.
  intros st Hq Hgood.
  have Hj: has_justification_link st \/ ~ has_justification_link st by apply classic.
  case: Hj => // Hj;first last.
    exists genesis, 0.
    split;[apply justified_genesis|].
    unfold highest_justified.
    intros b' b_h' Hb_h' Hb'justified.
    unfold not, has_justification_link in Hj.
    inversion Hb'justified;auto. subst.
    contradict Hj.
    exists s, b', s_h, b_h'. split;[assumption|assumption].
  have Hmax_exists := (maximal_link_exists Hgood Hj).
  destruct Hmax_exists as [max_s [max_t [max_s_h [max_t_h Hmax_jlink]]]].
  exists max_t, max_t_h.
  destruct (Hmax_jlink) as [Hmaxj Hmaximal_link].
  split.
    apply (@justified_link st max_s max_s_h max_t max_t_h).
      apply (good_votes_mean_source_justified Hgood Hmaxj).
    assumption.
  unfold highest_justified.
  intros b b_h Hbmax Hbj.
  by apply (maximal_link_highest_block Hq Hgood Hmax_jlink Hbj Hbmax).
Qed.

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

(** And finally, the overall plausible liveness theorem                           **)
(* In addition to gloabal axioms, the theorem requires the following               *)
(*   assumptions:                                                                  *)
(*   (1) There exists a well behaving 2/3 quorum (for every block)                 *)
(*   (2) 2/3-quorum validators' votes are valid votes (with respect to all blocks) *)
(*   (2) The conditions of slashing have not been met                              *)
(*   (3) Blocks exist sufficiently high over the highest justified block           *)
Theorem plausible_liveness : forall st,
  two_thirds_good st ->
  ~ q_intersection_slashed st ->
  good_votes st ->
  (forall b b_h, highest_justified st b b_h -> blocks_exist_high_over b) ->
  exists st', unslashed_can_extend st st'
    /\ no_new_slashed st st'
    /\ exists (new_finalized new_final_child:Hash) new_height,
         justified st' new_finalized new_height
         /\ new_finalized <~ new_final_child
         /\ supermajority_link st' new_finalized new_final_child
                                   new_height new_height.+1.
Proof.
  intros st Hgood Hunslashed Hgood_votes Hheight.
  destruct (highest_exists Hunslashed Hgood_votes) as (just_max & just_max_h & [Hjust_max_just Hjust_max_max]).
  specialize (Hheight _ _ Hjust_max_max).

  pose targets := (0 |` [ fset vote_target_height vote | vote in st])%fset;
                    change {fset nat} in (type of targets).

  pose highest_target := highest targets.
  destruct (Hheight ((highest_target.+1 - just_max_h)).+1) as [new_final_child [Hpath Hdist]].
  inversion Hpath;subst. rename h2 into new_finalized.

  destruct (Hgood new_finalized) as (good_quorum_f & Hgood_is_quorum_f & Hgood_f).
  destruct (Hgood new_final_child) as (good_quorum_c & Hgood_is_quorum_c & Hgood_c).
    
  pose new_votes1 := [fset (v,just_max,new_finalized,just_max_h,highest_target.+1)
                     | v in good_quorum_f]%fset; change {fset Vote} in (type of new_votes1).
  pose new_votes2 := [fset (v,new_finalized,new_final_child,highest_target.+1,highest_target.+2)
                     | v in good_quorum_c]%fset; change {fset Vote} in (type of new_votes2).

  exists (st `|` new_votes1 `|` new_votes2)%fset.
  split;[|split].

  *
  unfold unslashed_can_extend.
  clear -Hgood Hgood_f Hgood_c.
  unfold vote_msg.
  intros v s t s_h t_h.
  rewrite in_fsetU. rewrite in_fsetU.
  rewrite !Bool.orb_true_iff.
  move => [[H|H] | H];[tauto|right;apply (Hgood_f)|right;apply Hgood_c].
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
     destruct H0 as [_ [_ Hsm]];
     destruct (quorum_2_nonempty Hsm) as [t_supporter Ht];
     rewrite in_set in Ht; apply/fsetUP; right;
     revert Ht; apply in_imfset).

  unfold no_new_slashed.
  intros badV [Hdbl|Hnest];[left|right].
  (* slashed for double vote *)
  unfold slashed_double_vote, vote_msg in Hdbl |- *.
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
  unfold slashed_surround_vote in Hnest |- *.
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
  change (is_true (badV \in good_quorum_f)) in x_good.

  have Hnot_slashed := (Hgood_f badV x_good).
  apply (Hgood_votes new_finalized good_quorum_f) in x_good as HgoodbadV;try (repeat assumption).
  destruct HgoodbadV as [Hst2_justifiedvotes Hforward_links].
  apply Hst2_justifiedvotes in Hinner as Hst2_justified.
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
  apply (Hgood_votes new_final_child good_quorum_c) in x_good as [Hst2_justifiedvotes Hforward_links]; last by assumption.
  apply Hst2_justifiedvotes in Hinner as Hs2_justified.
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

    unfold justification_link. split.
    rewrite <- addn1 with (highest_target.+1 - just_max_h) in Hdist.
    replace 1 with (0 + 1) in Hdist at 1 by trivial.
    rewrite -> ltn_add2r with 1 0 (highest_target.+1 - just_max_h) in Hdist.
    revert Hdist.
    rewrite subn_gt0. trivial.

    split. assumption.

    unfold supermajority_link, link_supporters, vote_msg.
    apply quorum_2_upclosed with good_quorum_f.
    apply /subsetP.
    intros v Hv_good.
    rewrite in_set. rewrite in_fsetU.
    apply/orP. left. rewrite in_fsetU.
    apply/orP. right. unfold new_votes1.
    apply/imfsetP. exists v.
      assumption. reflexivity.
    apply /subsetP.
    intros v Hv_good.
    apply (votes_from_target_vset Hv_good).
    assumption.

    split.
    assert (0 <= highest_target).
    apply highest_ub.
    rewrite in_fsetU. apply/orP. left. apply fset11. by auto with arith.

    unfold supermajority_link, link_supporters, vote_msg.
    apply quorum_2_upclosed with good_quorum_c.
    apply /subsetP.
    intros v Hv_good.
    rewrite in_set. rewrite in_fsetU.
    apply/orP. right. unfold new_votes2.
    apply/imfsetP. exists v.
      assumption. reflexivity.
    apply /subsetP.
    intros v Hv_good.
    apply (votes_from_target_vset Hv_good).
    assumption.

Qed.

