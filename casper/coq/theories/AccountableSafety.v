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
Require Import Quorums HashTree State Slashing Justification.

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

(* No two different blocks can be justified at the same height without
   a quorum being slashed *)
Lemma no_two_justified_same_height: forall st b1 b1_h b2 b2_h,
  justified st b1 b1_h ->
  justified st b2 b2_h ->
  ~ quorum_slashed st ->
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
  have [q1 [Hq1 Hq1dblvote]]: exists q1, q1 \in quorum_1 /\
    forall v, v \in q1 ->
      v \in [set v | (v, sb1, b1, sb1_h, b1_h) \in st] /\
      v \in [set v | (v, sb2, b2, sb2_h, b2_h) \in st]
    by Reconstr.reasy (@quorums_property) Reconstr.Empty.
  contradict Hs.
  subst b1_h.
  unfold quorum_slashed.
  exists q1. split;[assumption|].
  intros v Hvinq. unfold slashed. left.
  unfold slashed_dbl_vote.
  exists b1, b2. split;[assumption|].
  exists sb1, sb1_h, sb2, sb2_h, b2_h.
  unfold vote_msg.
  have H:= @Hq1dblvote v Hvinq.
  repeat rewrite in_set in H.
  assumption.
Qed.

(* No block can be finalized at a height at which some other block is
   justified without a quorum being slashed *)
Lemma no_finalized_justified_same_height : forall st bf bf_h bj bj_h,
  finalized st bf bf_h ->
  justified st bj bj_h ->
  ~ quorum_slashed st ->
  bj <> bf ->
  bj_h <> bf_h.
Proof.
by Reconstr.hcrush Reconstr.Empty
		(@no_two_justified_same_height)
		(@finalized).
Qed.

(* Slash-surround case of the inductive step of the safety proof *)
(* The specific case of proper link containment *)
Lemma slash_surround_case_strict : forall st s t final s_h t_h final_h,
  justified st s s_h ->
  justification_link st s t s_h t_h ->
  finalized st final final_h ->
  final_h.+1 < t_h ->
  final </~* t ->
  s_h < final_h ->
  quorum_slashed st.
Proof.
  move => st s t final s_h t_h final_h Hsj [Htgts [Hnth Hsm]] Hfinal Hft Hnoans Hsf.
  destruct Hfinal as [Hfj [c [Hcp Hcsm]]].
  unfold supermajority_link, link_supporters, vote_msg in Hsm.
  unfold supermajority_link, link_supporters, vote_msg in Hcsm.
  have [q1 [Hq1 Hq1slashed]]: exists q1, q1 \in quorum_1 /\
    forall v, v \in q1 ->
      v \in [set v | (v, s, t, s_h, t_h) \in st] /\
      v \in [set v | (v, final, c, final_h, final_h.+1) \in st]
    by Reconstr.reasy (@quorums_property) Reconstr.Empty.
  unfold quorum_slashed.
  exists q1. split;[assumption|].
  intros v Hvinq.
  apply Hq1slashed in Hvinq as [H1 H2].
  rewrite in_set in H1. rewrite in_set in H2.
  unfold slashed. right.
  unfold slashed_surround.
  exists s, t, s_h, t_h. exists final, c, final_h, final_h.+1.
  repeat (split;try assumption).
Qed.

(* Slash-surround case of the inductive step of the safety proof *)
(* The general case *)
Lemma slash_surround_case_general : forall st s t final s_h t_h final_h,
  justified st s s_h ->
  justification_link st s t s_h t_h ->
  finalized st final final_h ->
  final_h < t_h ->
  final </~* t ->
  s_h < final_h ->
  quorum_slashed st.
Proof.
move => st s t final s_h t_h final_h Hsj [Htgts [Hnth Hsm]] Hfinal Hft Hnoans Hsf.
case Hn: (t_h == final_h.+1).
  move/eqP: Hn => Hn.
  have Htjl : justification_link st s t s_h t_h by trivial.
  have Htj : justified st t t_h by apply (justified_link Hsj Htjl).
  subst t_h.
  destruct Hfinal as [Hfj [c [Hcp Hcsm]]].
  have Hfh : final_h.+1 > final_h by trivial.
  have Hca : final <~* c by apply (hash_parent_ancestor Hcp).
  apply parent_ancestor in Hcp.
  replace 1 with (final_h.+1 - final_h) in Hcp by apply subSnn.
  have Hcjl : justification_link st final c final_h final_h.+1 by trivial.
  have Hcj : justified st c final_h.+1 by apply (justified_link Hfj Hcjl).
  have Hfcconf: t <> c by (contradict Hnoans;subst c;assumption).
  have Hconf := no_two_justified_same_height Htj Hcj.
  have Ho: quorum_slashed st \/ ~ quorum_slashed st by apply classic.
  case: Ho => // Ho.
  apply Hconf in Ho;[contradiction|assumption].
move/negP/negP/eqP: Hn => Hn.
have Hgt: final_h.+1 < t_h.
  apply/ltP.
  move/ltP: Hft => Hft.
  by intuition.
have Hjl : justification_link st s t s_h t_h by trivial.
by Reconstr.hobvious (@Hfinal, @Hnoans, @Hsf, @Hgt, @Hsj, @Hjl)
		(@slash_surround_case_strict)
		(@hash_ancestor).
Qed.

(* The inductive reasoning step for the safety proof case of non-equal
   heights*)
Lemma non_equal_height_case_ind : forall st b1 b1_h b2 b2_h,
  justified st b1 b1_h ->
  finalized st b2 b2_h ->
  b2 </~* b1 ->
  b1_h > b2_h ->
  quorum_slashed st.
Proof.
move => st b1 b1_h b2 b2_h Hb1j Hb2f Hconfl Hh.
pose P (h1_h : nat) (h1 : Hash) :=
  justified st h1 h1_h ->
  finalized st b2 b2_h ->
  b2 </~* h1 ->
  b2_h < h1_h ->
  quorum_slashed st.
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
have Ho: quorum_slashed st \/ ~ quorum_slashed st by apply classic.
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
    have Hl5 := no_finalized_justified_same_height Hb2f Hsj Ho Hpneq'.
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
    by have Hslash_surround := slash_surround_case_general Hsj Hjl Hb2f Hh Hconfl Hlt.
by apply: IH'.
Qed.

(* Safety proof case: two conflicting blocks are finalized at different
   heights *)
Lemma non_equal_height_case : forall st b1 b1_h b2 b2_h,
  finalized st b1 b1_h ->
  finalized st b2 b2_h ->
  b2 </~* b1 ->
  b1_h > b2_h ->
  quorum_slashed st.
Proof.
intros st b1 b1_h b2 b2_h Hb1f Hb2f Hx Hh.
destruct Hb1f as [Hb1j _].
by apply non_equal_height_case_ind with b1 b1_h b2 b2_h.
Qed.

(* Safety proof case: two conflicting blocks are finalized at the same
   height *)
Lemma equal_height_case : forall st b1 b2 h,
  finalized st b1 h ->
  finalized st b2 h ->
  b1 <> b2 ->
  quorum_slashed st.
Proof.
move => st b1 b2 h Hf1 Hf2 Hh.
unfold finalized, supermajority_link, link_supporters, vote_msg in Hf1, Hf2.
destruct Hf1 as [Hj1 [c1 [Hp1 Hq1]]].
destruct Hf2 as [Hj2 [c2 [Hp2 Hq2]]].

  have Hconf := no_two_justified_same_height Hj1 Hj2.
  have Ho: quorum_slashed st \/ ~ quorum_slashed st by apply classic.
  case: Ho => // Ho.
  apply Hconf in Ho;[contradiction|assumption].
Qed.

(* A quorum is slashed if two conflicting blocks are finalized *)
Lemma safety' : forall st b1 b1_h b2 b2_h,
  finalized st b1 b1_h ->
  finalized st b2 b2_h ->
  b2 </~* b1 ->
  b1 </~* b2 ->
  quorum_slashed st.
Proof.
move => st b1 b1_h b2 b2_h Hf1 Hf2 Hh1 Hh2.
have Hn:= hash_nonancestor_nonequal Hh2.
  case Hbh: (b1_h == b2_h).
  move/eqP: Hbh => Hbh.
  subst.
  move: Hf1 Hf2 Hn.
  exact: equal_height_case.
move/eqP: Hbh => Hbh.
case H1: (b1_h > b2_h).
  move: Hf1 Hf2 Hh1 H1.
  by apply: non_equal_height_case; eauto.
have Hgt: b2_h > b1_h.
  apply/ltP.
  move/ltP: H1.
  move => Hnn.
  by intuition.
move: Hgt.
by apply: non_equal_height_case; eauto.
Qed.

(* The main accountable safety theorem *)
Theorem accountable_safety : forall st, finalization_fork st -> quorum_slashed st.
Proof.
by Reconstr.hobvious Reconstr.Empty
		(@safety')
		(@finalization_fork).
Qed.
