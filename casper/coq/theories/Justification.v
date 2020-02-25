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

(* The voter set for a link constitute a supermajority *)
Definition supermajority_link (st:State) (s t : Hash) (s_h t_h : nat) : Prop :=
  link_supporters st s t s_h t_h \in quorum_2.

(* Adding more votes (from the same validators) to a state preserves supermajority links *)
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

(* Justification is preserved when the state is expanded with new votes *)
Lemma justified_weaken: forall (st st':State)
    (HSub:forall (v: Vote), v \in st -> v \in st'),
  forall t t_h, justified st t t_h -> justified st' t t_h.
Proof.
  move=> st st' Hsub t t_h.
  induction 1. constructor.
  destruct H0 as [Hh [Ha Hsm]].
  apply (justified_link IHjustified).
  unfold justification_link;repeat (split; try assumption).
  revert Hsm.
  apply supermajority_weaken.
  assumption.
Qed.

(* A finalized block is a justified block that has a child who is also
   justified by a supermajority link to the block *)
Definition finalized st b b_h :=
  justified st b b_h /\
  exists c, (b <~ c /\ supermajority_link st b c b_h b_h.+1).

(* I think k-finalized safety can be shown without unique tree paths and indeed, without any ancestry relationship between the blocks *) 

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

(* A block is 1-finalized if it is finalized *)
Lemma finalized_means_k_finalized : forall st b b_h,
    finalized st b b_h <->
    k_finalized st b b_h 1. 
Proof.     
  intros st b B_h; split.
  (* Left direction *) 
  { intro H_fin.
    destruct H_fin as [H_just [c [H_rel H_link]]]. 
    split. easy.
    exists [::b; c]; repeat split.
    assert (n = 0 \/ n = 1)%coq_nat by admit.
    destruct H0 as [H_zero | H_one]; subst.
    (* Proving justified *) 
    { (* n = 0 *)
      simpl. replace (B_h + 0) with B_h. 
      assumption. 
      admit. } 
    { (* n = 1 *)
      assert (justification_link st b c B_h B_h.+1).
        { unfold justification_link; split.
          easy. split. rewrite subSnn.
          now apply parent_ancestor.
          assumption. }
        simpl.
        replace (B_h + 1) with (B_h.+1). 
        apply (justified_link H_just H0).
        admit. }
    (* Proving ancestor *)
    assert (n = 0 \/ n = 1) by admit.
    destruct H0 as [H_zero | H_one]; subst.
    simpl. apply nth_ancestor_0. 
    simpl. apply parent_ancestor. assumption.
    simpl.
    replace (B_h + 1) with (B_h.+1) by admit.
    assumption. }
  (* Right direction *) 
  intros [H_k [ls [H_size [H_hd [H_rel H_link]]]]].
  split.
  (* Proving justified *)
  { spec H_rel 0. spec H_rel.
    easy. destruct H_rel.
    rewrite <- nth0 in H_hd.
    rewrite H_hd in H. 
    replace (B_h + 0) with B_h in H by admit.
    assumption. } 
  (* Proving existential *)
  { exists (last b ls). split.
    spec H_rel 1. spec H_rel; try easy.
    destruct H_rel.
    admit.
    replace (B_h.+1) with (B_h + 1) by admit.
    assumption.
Admitted.

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
  admit.
Admitted.

(* A finalized block has a child who is justified *)
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
have Hjl : justification_link st p c p_h p_h.+1 by trivial.
apply (justified_link Hjustified_p Hjl).
Qed.
