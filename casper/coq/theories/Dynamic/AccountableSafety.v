Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

From Hammer
Require Reconstr. 

Require Import Classical.

From Dynamic
Require Import StrongInductionLtn.

From Dynamic
Require Import Validator HashTree State Slashing Quorums Justification.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* The accountable safety theorem *)

(* A state has a fork when two conflicting blocks are both finalized *)
Definition finalization_fork st :=
  exists b1 b1_h b2 b2_h,
    finalized st b1 b1_h /\
    finalized st b2 b2_h /\
    b2 </~* b1 /\ b1 </~* b2.

Definition k_finalization_fork st k1 k2 :=
  exists b1 b1_h b2 b2_h,
    k_finalized st b1 b1_h k1 /\
    k_finalized st b2 b2_h k2 /\
    b2 </~* b1 /\ b1 </~* b2.

Definition same_k_finalization_fork st k :=
  k_finalization_fork st k k.

Lemma finalization_fork_means_same_finalization_fork_one :
  forall st,
    finalization_fork st <-> same_k_finalization_fork st 1. 
Proof. 
  intros st; split; intro Hfin;
  destruct Hfin as [b1 [b1_h [b2 [b2_h [Hfin1 [Hfin2 [Hnot1 Hnot2]]]]]]];
  exists b1, b1_h, b2, b2_h; split.
  now apply finalized_means_one_finalized.
  split. now apply finalized_means_one_finalized.
  eauto. 
  now apply finalized_means_one_finalized. 
  split. now apply finalized_means_one_finalized.
  eauto.
Qed.

(* No two different blocks can be justified at the same height without a quorum being slashed *)
Lemma no_two_justified_same_height: forall st b1 b1_h b2 b2_h,
  justified st b1 b1_h ->
  justified st b2 b2_h ->
  ~ q_intersection_slashed st ->
  b1 <> b2 ->
  b1_h <> b2_h.
Proof.
move => st b1 b1_h b2 b2_h Hj1 Hj2 Hs Hneq.
destruct Hj1 as [| sb1 sb1_h b1 b1_h Hjs1 [Hh1 [Ha1 Hsm1]]] eqn:E1.
- destruct Hj2 eqn:E2; first by contradiction.
  by Reconstr.scrush.
- destruct Hj2 as [| sb2 sb2_h b2 b2_h Hjs2 [Hh2 [Ha2 Hsm2]]] eqn:E2; first by Reconstr.scrush.
  unfold supermajority_link, link_supporters, vote_msg in Hsm1.
  unfold supermajority_link, link_supporters, vote_msg in Hsm2.
  contradict Hs.
  subst b1_h.
  unfold q_intersection_slashed.
  exists b1, b2.
  exists [set v | (v, sb1, b1, sb1_h, b2_h) \in st],
         [set v | (v, sb2, b2, sb2_h, b2_h) \in st].

  clear E1 E2.
  repeat (split; try assumption).
  unfold quorum_2 in Hsm1, Hsm2.
      by move/andP: Hsm1 => [Hsub1 _].
    by move/andP: Hsm2 => [Hsub2 _].
  
  intros v Hvinq1 Hvinq2. unfold slashed. left.
  unfold slashed_dbl_vote.
  exists b1, b2. split;[assumption|].
  exists sb1, sb1_h, sb2, sb2_h, b2_h.
  unfold vote_msg.
  rewrite in_set in Hvinq1.
  rewrite in_set in Hvinq2.
  easy.
Qed.

(* No block can be finalized at a height at which some other block is
   justified without a quorum being slashed *)
Lemma no_k_finalized_justified_same_height : forall st bf bf_h bj bj_h k,
  k_finalized st bf bf_h k ->
  justified st bj bj_h ->
  ~ q_intersection_slashed st ->
  bj <> bf ->
  bj_h <> bf_h.
Proof.
  intros.
  eapply no_two_justified_same_height.
  apply H0.
  apply k_finalized_means_justified with k.
  apply H.
  assumption. assumption.
Qed. 

(* Slash-surround case of the inductive step of the safety proof *)
(* The specific case of proper link containment *)
Lemma k_slash_surround_case_general : forall st s t final s_h t_h final_h k,
  justified st s s_h ->
  justification_link st s t s_h t_h ->
  k_finalized st final final_h k ->
  final_h < t_h ->
  final </~* t ->
  s_h < final_h ->
  q_intersection_slashed st.
Proof.
  move => st s t final s_h t_h final_h k Hsj [Htgts [Hnth Hsm]] Hfinal Hft Hnoans Hsf.
  destruct Hfinal as [H_k [ls [H_size [H_hd [H_rel H_link]]]]].
  assert (final_h + k < t_h \/ final_h + k = t_h \/ final_h + k > t_h)%coq_nat by apply PeanoNat.Nat.lt_total.
  destruct H as [H_lt | H_ge].
  (* Full containment *) 
  unfold supermajority_link, link_supporters, vote_msg in Hsm.
  unfold supermajority_link, link_supporters, vote_msg in H_link.
  unfold q_intersection_slashed.
  exists t, (last final ls).
  exists [set v | (v, s, t, s_h, t_h) \in st],
         [set v | (v, final, last final ls, final_h, (final_h + k)%coq_nat) \in st].
  repeat (split; try assumption).
  unfold quorum_2 in Hsm, H_link.
      by move/andP: Hsm => [Hsub1 _].
    by move/andP: H_link => [Hsub2 _].  
  intros v Hvinq1 Hvinq2.
  rewrite in_set in Hvinq1. rewrite in_set in Hvinq2.
  unfold slashed. right.
  unfold slashed_surround.
  exists s, t, s_h, t_h. exists final, (last final ls), final_h, (final_h + k).
  repeat (split;try assumption).
  by apply/ltP.
  (* Partial containment *)
  destruct (classic (t = last final ls)). 
  (** In the case that they overlap, we find a contradiction to non-ancestry **)
  assert (final <~* last final ls).
  { eapply (nth_ancestor_ancestor).
    subst. spec H_rel k. spec H_rel; intuition.
    rewrite <- nth_last. rewrite H_size.
    simpl. exact H0. rewrite <- nth_last.
    rewrite H_size. simpl. exact H0. } 
  subst; contradiction. 
  (** In the case that they do not overlap, we find a contradiction via two non-equal blocks justified at the same height *)
  destruct H_ge as [H_eq | H_gt]. 
  destruct (classic (q_intersection_slashed st)).
  (* In the yes case, we're done *)
  assumption.
  (* In the no case, we find another contradiction *)
  assert (Hjj : justified st t t_h). 
  { eapply justified_link. exact Hsj.
    unfold supermajority_link, link_supporters, vote_msg in Hsm.
    unfold justification_link; split; by intuition. }
  assert (Hjlast : justified st (nth final ls k) (final_h + k)).
  { eapply H_rel. auto. }
  assert (H_useful := no_two_justified_same_height Hjj Hjlast).
  spec H_useful H0.
  spec H_useful.
  replace k with ((k.+1).-1) by easy.
  rewrite <- H_size. rewrite nth_last.
  assumption.
  have: (final_h + k)%coq_nat <> t_h. 
  apply/eqP. auto. intro. contradiction.
  spec H_rel (t_h - final_h). 
  spec H_rel. apply ltnW.
  rewrite ltn_psubLR. 
  apply/ltP. assumption. assumption.
  destruct H_rel as [H_just H_ancestor].
  assert (Htj : justified st t t_h). 
  { eapply justified_link. exact Hsj.
    unfold supermajority_link, link_supporters, vote_msg in Hsm.
    unfold justification_link; split; by intuition. }
  destruct (classic (t = nth final ls (t_h - final_h))). 
  (* In the case that t is on the justification chain of final *)
  subst. 
  assert (final <~* nth final ls (t_h - final_h)).
  eapply nth_ancestor_ancestor. apply H_ancestor.
  contradiction.
  (* In the case that t is outside of the justification chain *)
  assert (H_useful := no_two_justified_same_height Htj H_just). 
  destruct (classic (q_intersection_slashed st)).
  assumption. spec H_useful H1.
  spec H_useful H0.
  assert (final_h <= t_h). intuition.
  erewrite subnKC in H_useful. 
  contradiction. assumption. 
Qed.

(* Slash-surround case of the inductive step of the safety proof *)
(* The general case *)
(* The inductive reasoning step for the safety proof case of non-equal
   heights*)
Lemma k_non_equal_height_case_ind : forall st b1 b1_h b2 b2_h k,
  justified st b1 b1_h ->
  k_finalized st b2 b2_h k ->
  b2 </~* b1 ->
  b1_h > b2_h ->
  q_intersection_slashed st.
Proof.
move => st b1 b1_h b2 b2_h k Hb1j Hb2f Hconfl Hh.
pose P (h1_h : nat) (h1 : Hash) :=
  justified st h1 h1_h ->
  k_finalized st b2 b2_h k ->
  b2 </~* h1 ->
  b2_h < h1_h ->
  q_intersection_slashed st. 
suff Hsuff: forall h1_h h1, P h1_h h1 by apply: Hsuff; eauto.
apply (@strong_induction_sub b2_h).
clear b1 b1_h Hb1j Hconfl Hh Hb2f.
move => b1_h b1 IH Hb1j Hb2f Hconfl Hh.
have Hor: (b1 = genesis /\ b1_h = 0) \/
          (exists s s_h,
             justified st s s_h /\
             justification_link st s b1 s_h b1_h).
  inversion Hb1j; first by left.
  right.
  by exists s, s_h.
case: Hor => Hor; first by move: Hor => [H1 H2]; rewrite H2 in Hh.
have Ho: q_intersection_slashed st \/ ~ q_intersection_slashed st by apply classic.
case: Ho => // Ho.
move: Hor => [s [s_h [Hsj [Hsh [Hsa Hsm]]]]].
have IH' := IH s_h s _ _ Hsj Hb2f.
have Hp: b2 </~* s.
  have Hm := nth_ancestor_ancestor Hsa.
  by apply: hash_ancestor_conflict; eauto.
have Hpneq: b2 <> s by apply hash_nonancestor_nonequal.
have Hpneq': s <> b2 by eauto.
have Hplt: s_h - b2_h < b1_h - b2_h.
  by apply ltn_sub2r.
  case Hlt: (b2_h < s_h); last first.
  rewrite ltn_neqAle /= in Hlt.
  move/negP/negP: Hlt.
  rewrite negb_and.
  move/orP; case.
  * move/negP/eqP => Hvv. 
    case Hv2p: (b2_h == s_h); last by rewrite Hv2p /= in Hvv.
    move/eqP: Hv2p => Hv2p {Hvv}.
    have Hl5 := no_k_finalized_justified_same_height Hb2f Hsj Ho Hpneq'.
    by have H : b2_h <> s_h by eauto.
  * rewrite leq_eqVlt.
    rewrite negb_or.
    rewrite -leqNgt leq_eqVlt.
    move/andP => [Hnq Hpp].
    move/eqP: Hnq => Hnq.
    case/orP: Hpp.
      move/eqP => Hpp.
      by apply sym_eq in Hpp.
    move => Hlt.
    have Hjl : justification_link st s b1 s_h b1_h by trivial.
    by have Hslash_surround := k_slash_surround_case_general Hsj Hjl Hb2f Hh Hconfl Hlt.
    intuition.
Qed. 

(* Safety proof case: two conflicting blocks are finalized at different
   heights *)
Lemma k_non_equal_height_case : forall st b1 b1_h b2 b2_h k1 k2,
  k_finalized st b1 b1_h k1 ->
  k_finalized st b2 b2_h k2 ->
  b2 </~* b1 ->
  b1_h > b2_h ->
  q_intersection_slashed st.
Proof.
intros st b1 b1_h b2 b2_h k1 k2 Hb1f Hb2f Hx Hh.
apply k_finalized_means_justified in Hb1f. 
by apply k_non_equal_height_case_ind with b1 b1_h b2 b2_h k2.
Qed.

(* Safety proof case: two conflicting blocks are finalized at the same
   height *)
Lemma k_equal_height_case : forall st b1 b2 h k1 k2,
  k_finalized st b1 h k1 ->
  k_finalized st b2 h k2 ->
  b1 <> b2 ->
  q_intersection_slashed st.
Proof.
move => st b1 b2 h k1 k2 Hf1 Hf2 Hh.
unfold k_finalized, supermajority_link, link_supporters, vote_msg in Hf1, Hf2.
apply k_finalized_means_justified in Hf1. 
apply k_finalized_means_justified in Hf2.
have Hconf := no_two_justified_same_height Hf1 Hf2.
have Ho: q_intersection_slashed st \/ ~ q_intersection_slashed st by apply classic.
case: Ho => // Ho.
apply Hconf in Ho;[contradiction|assumption].
Qed.

(* A quorum is slashed if two conflicting blocks are finalized *)
Lemma k_safety' : forall st b1 b1_h b2 b2_h k1 k2,
  k_finalized st b1 b1_h k1 ->
  k_finalized st b2 b2_h k2 ->
  b2 </~* b1 ->
  b1 </~* b2 ->
  q_intersection_slashed st.
Proof.
  move => st b1 b1_h b2 b2_h k1 k2 Hf1 Hf2 Hh1 Hh2.
  have Hn:= hash_nonancestor_nonequal Hh2.
  case Hbh: (b1_h == b2_h).
  move/eqP: Hbh => Hbh.
  subst.
  move: Hf1 Hf2 Hn.
  exact: k_equal_height_case.
  move/eqP: Hbh => Hbh.
  case H1: (b1_h > b2_h).
  move: Hf1 Hf2 Hh1 H1. 
    by apply: k_non_equal_height_case; eauto.
    have Hgt: b2_h > b1_h.
    apply/ltP.
    move/ltP: H1.
    move => Hnn.
      by intuition.
      move: Hgt.
        by apply: k_non_equal_height_case; eauto.
Qed.

(* The main accountable safety theorem *)
Theorem k_accountable_safety : forall st k1 k2, 
  k_finalization_fork st k1 k2 -> q_intersection_slashed st.
Proof.
by Reconstr.hobvious Reconstr.Empty
		(@k_safety')
		(@k_finalization_fork).
Qed.

Theorem accountable_safety : forall st, 
  finalization_fork st -> q_intersection_slashed st.
Proof.
  intros st Hfin.
  apply finalization_fork_means_same_finalization_fork_one in Hfin.
  eapply k_accountable_safety with 1 1.
  assumption. 
Qed.
