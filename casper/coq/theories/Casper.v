Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

From Hammer
Require Reconstr.

Require Import Classical. 

Require Import Coq.micromega.Lia.

From Casper
Require Import StrongInductionLtn.

From Casper
Require Import Quorums.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CasperProperties.

(* We consider the checkpoint tree of blocks, and so a "block" refers to a 
   "checkpoint block" throughout the specs below. *)

Variable Hash : finType.


(* Each vote names source and target nodes by giving hash and height,
   and is signed by a particular validator.
   This definition is different from votes in AccountableSafety.v,
   this is taken directly from the way votes are expressed in the
   Casper paper.supermajority
 *)
Definition Vote := (Validator * Hash * Hash * nat * nat)%type.
(* A State is described by the set of votes case in the current epoch.
   For liveness we insist that this be a finite set of votes.
 *)

Definition State := {fset Vote}.

(* This relation links blocks (b,b') if b is an ancestor of b' and
   b' is at the next checkpoint level above b *)
Variable hash_parent : rel Hash.

Notation "h1 <~ h2" := (hash_parent h1 h2) (at level 50).

Hypothesis hash_parent_irreflexive: 
  forall h1 h2, h1 <~ h2 -> h1 <> h2.

Definition hash_ancestor h1 h2 :=
 connect hash_parent h1 h2.

Notation "h1 <~* h2" := (hash_ancestor h1 h2) (at level 50).

Notation "h1 </~* h2" := (~ hash_ancestor h1 h2) (at level 50).

(* a hash can have one parent *)
Hypothesis hash_at_most_one_parent :
  forall h1 h2 h3, h2 <~ h1 -> h3 <~ h1 -> h2 = h3.

(* The genesis block. *)
Variable genesis : Hash.

(* [ADDED] *)
Hypothesis genesis_ancestor :
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

(* A boolean vote_msg predicate is then a definition rather than
   a field of State as in AccountableSafety.v 
   Further constraints on what constitutes a valid vote message have
   been added *)
Definition vote_msg (st:State) v s t (s_h t_h:nat) : bool
  := ((v,s,t,s_h,t_h) \in st) .

(* Definitions of the slashing conditions *)
(* A validator may not make two votes with different target hashes at the same
  target height (whatever the source blocks)
 *)
Definition slashed_dbl_vote st v :=
  exists t1 t2, t1 <> t2 /\ exists s1 s1_h s2 s2_h t_h,
      vote_msg st v s1 t1 s1_h t_h /\ vote_msg st v s2 t2 s2_h t_h.

(* A validator may not make two votes with the source and target of one vote
   both strictly between the source and target of the other
 *)
Definition slashed_surround st v :=
  exists s1 t1 s1_h t1_h,
  exists s2 t2 s2_h t2_h,
    vote_msg st v s1 t1 s1_h t1_h /\
     vote_msg st v s2 t2 s2_h t2_h /\
     s2_h > s1_h /\ t2_h < t1_h.


Definition slashed st v : Prop :=
 slashed_dbl_vote st v \/ slashed_surround st v.

(* The finalized node at which the current epoch started. *)
(* Variable epoch_start : Hash.
Variable epoch_height : nat.
Hypothesis epoch_ancestry : nth_ancestor epoch_height genesis epoch_start.*)

(* Now we define justification *)
(* First a definition of supermajority links *)
Definition link_supporters st s t s_h t_h : {set Validator} :=
  [set v | vote_msg st v s t s_h t_h ].

Definition supermajority_link (st:State) (s t : Hash) (s_h t_h : nat) : Prop :=
  link_supporters st s t s_h t_h \in quorum_2.
  
(* [Modified: now requires the link to be based on proper votes, where proper means
    that votes must link a source being an ancestor of the target]
   [It's a Prop now]
   [this now matches the version in A.S.] *)
(* 
Definition justified_link (st:State) (s t : Hash) (s_h t_h : nat) : Prop :=
  supermajority_link st s t s_h t_h 
  /\ t_h > s_h 
  /\ nth_ancestor (t_h - s_h) s t .
  *)

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

(* This is trivial now and add nothing new. We are not referring to epochs anymore! 
   [From P.L.] *)
Lemma justified_is_descendant st n n_h:
  justified st n n_h -> genesis <~* n.
Proof.
induction 1. 
  eapply connect0.
apply nth_ancestor_ancestor in H1.
have Hg := hash_ancestor_concat IHjustified H1.
eassumption.
Defined.

(* From A.S. *)
(* The nth_ancestor, with n positive, is an ancestor 
   [Now subsumed by nth_ancestor_ancestor] 
 *)
Lemma ancestor_means :
  forall n parent new,
  nth_ancestor n parent new -> n > 0 -> parent <~* new.
Proof.
elim => //=.
move => n IH parent new Hn.
inversion Hn; subst.
case Hn0: (n == 0).
  move/eqP: Hn0 H0 -> => Hnt Hlt.
  inversion Hnt; subst.
  by apply/connect1.
move/negP/negP: Hn0 => Hn0 Hltn.
have Hnn: 0 < n.
  apply: neq0_lt0n.
  by apply/negP/negP.
move: (IH _ _ H0 Hnn) => Hp.
apply: connect_trans; eauto.
by apply/connect1.
Qed.

(*  From A.S. *)
(*    
*)
Lemma justified_means:
  forall st t t_h,
  t <> genesis -> 
  justified st t t_h -> 
  exists s s_h, 
    justified st s s_h /\
    t_h > s_h /\
    nth_ancestor (t_h - s_h) s t /\ 
    supermajority_link st s t s_h t_h.
Proof.
intros st t t_h Ht Ht_justified.
destruct Ht_justified. contradict Ht. trivial.
exists s. exists s_h. 
by repeat(try(split;assumption)).
Qed.

(* A s.m. link from s to t means that t_h > s_h 
   [Corresponds to L01 from A.S.] 
   subsumed roughly by justified_means above *)
(*
Lemma justified_means_forwardlink :
  forall st s t s_h t_h,
  justified_link st s t s_h t_h -> t_h > s_h .
Proof.
move => st s t s_h t_h.
unfold supermajority_link.
move => smH .
destruct smH as [supp stH]. destruct stH as [stH staH].
assumption. 
Qed.
*)

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

(* a state has a fork when blocks in different branches are both finalized *)
Definition finalization_fork st :=
  exists b1 b1_h b2 b2_h,
    finalized st b1 b1_h /\
    finalized st b2 b2_h /\
    b2 </~* b1 /\ b1 </~* b2.

(* In a vote message, the source must be an ancestor of the target 
   and the source must be justified 
  [from P.L.] 
  [Replaced epoch_start <~* s (and later s <~* t) with the stronger conclusion that 
   the source must be the kth ancestor of the target, with k the distance] 

  But this is no longer needed as it is already assumed in the defition of a supermajority link *)

(*
 Definition sources_justified st v :=
  forall s t s_h t_h,
    vote_msg st v s t s_h t_h ->
    nth_ancestor (t_h - s_h) s t /\ justified st s s_h.
*)

(* "1/3" or more of validators are slashed *)
Definition quorum_slashed st :=
  exists q, q \in quorum_1 /\ forall v, v \in q -> slashed st v.

(* slash surround: the case of proper containment of justified links *)
Lemma l03 : forall st s t final s_h t_h final_h,
  justified st s s_h ->
  t_h > s_h ->
  nth_ancestor (t_h - s_h) s t ->
  supermajority_link st s t s_h t_h -> (* may not be enough *)
  finalized st final final_h ->
  final_h.+1 < t_h ->
  final </~* t -> 
  s_h < final_h ->
  quorum_slashed st.
Proof.
  move => st s t final s_h t_h final_h Hsj Htgts Hnth Hsm Hfinal Hft Hnoans Hsf.
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

Lemma no_two_justified_same_height: forall st b1 b1_h b2 b2_h,
  justified st b1 b1_h ->
  justified st b2 b2_h ->
  ~ quorum_slashed st ->
  b1 <> b2 ->
  b1_h <> b2_h.
Proof.
move => st b1 b1_h b2 b2_h Hj1 Hj2 Hs Hneq.
destruct Hj1 as [| sb1 sb1_h b1 b1_h Hjs1 Hh1 Ha1 Hsm1] eqn:E1.
- destruct Hj2 eqn:E2; first by contradiction.
  by Reconstr.scrush.
- destruct Hj2 as [| sb2 sb2_h b2 b2_h Hjs2 Hh2 Ha2 Hsm2] eqn:E2; first by Reconstr.scrush.
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

(* slash surround - general *)
Lemma l00 : forall st s t final s_h t_h final_h,
  justified st s s_h ->
  t_h > s_h ->
  nth_ancestor (t_h - s_h) s t ->
  supermajority_link st s t s_h t_h -> (* may not be enough alone *)
  finalized st final final_h ->
  final_h < t_h ->
  final </~* t -> 
  s_h < final_h ->
  quorum_slashed st.
Proof.
move => st s t final s_h t_h final_h Hsj Htgts Hnth Hsm Hfinal Hft Hnoans Hsf.
case Hn: (t_h == final_h.+1).
  move/eqP: Hn => Hn.
  have Htj : justified st t t_h by apply (justified_link Hsj Htgts Hnth Hsm).
  subst t_h.  
  destruct Hfinal as [Hfj [c [Hcp Hcsm]]].
  have Hfh : final_h.+1 > final_h by trivial.
  have Hca : final <~* c by apply (hash_parent_ancestor Hcp).
  apply parent_ancestor in Hcp.
  replace 1 with (final_h.+1 - final_h) in Hcp by apply subSnn.
  have Hcj : justified st c final_h.+1 by apply (justified_link Hfj Hfh Hcp Hcsm).
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
by Reconstr.hobvious (@Hfinal, @Hnoans, @Hsf, @Hgt, @Hsj, @Htgts, @Hnth, @Hsm)
		(@l03)
		(@hash_ancestor).
Qed.

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
             b1_h > s_h /\
             nth_ancestor (b1_h - s_h) s b1 /\
             supermajority_link st s b1 s_h b1_h).
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
    by have Hl00 := l00 Hsj Hsh Hsa Hsm Hb2f Hh Hconfl Hlt.
by apply: IH'.
Qed.

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
have [q [Hq_qourum Hq_dblvote]]: exists q, 
  q \in quorum_1 /\ 
  forall v, v \in q -> 
    v \in [set v | (v, b1, c1, h, h.+1) \in st] /\ v \in [set v | (v, b2, c2, h, h.+1) \in st]
  by Reconstr.rsimple (@quorums_property) Reconstr.Empty.
have Hx: c1 <> c2.
  move => Hx.
  rewrite Hx in Hp1.
  by have Hp := hash_at_most_one_parent Hp1 Hp2.
unfold quorum_slashed.
exists q. split;[assumption|].
intros v Hvinq. unfold slashed. left.
unfold slashed_dbl_vote.
exists c1, c2. split;[assumption|].
exists b1, h, b2, h, (h.+1).
unfold vote_msg.
have H:= @Hq_dblvote v Hvinq.
repeat rewrite in_set in H.
assumption.
Qed.

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

Theorem accountable_safety : forall st, finalization_fork st -> quorum_slashed st.
Proof.
by Reconstr.hobvious Reconstr.Empty
		(@safety')
		(@finalization_fork).
Qed.


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

End CasperProperties.
