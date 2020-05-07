Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

From Dynamic
Require Import NatExt SetTheoryProps Validator Weight HashTree State Slashing Quorums Justification AccountableSafety.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fmap_scope.

(******************************************************************************)
(* The slash-able bound theorem                                               *)
(******************************************************************************)

(** Activation and Exit Sets **)
(* The set of validators who activated from s1 to s2 *)
Definition activated (s1 s2: {set Validator}): {set Validator} :=
  s2 :\: s1.

(* The set of validators who exited from s1 to s2 *)
Definition exited (s1 s2: {set Validator}): {set Validator} :=
  s1 :\: s2.

(* The weight of new activations from s1 to s2 *)
Definition actwt (s1 s2: {set Validator}): nat :=
  wt (activated s1 s2).

(* The weight of validators who exited from s1 to s2 *)
Definition extwt (s1 s2: {set Validator}): nat :=
  wt (exited s1 s2).

(* Some additional lemmas about wt *)
Lemma wt_meet_bound : forall (s1 s2 s1' s2':{set Validator}),
  s1 \subset s1' -> 
  s2 \subset s2' ->
  let s12' := (s1' :&: s2') in 
    wt (s1 :&: s2) + wt s12' >= wt (s1 :&: s12') + wt (s2 :&: s12').
Proof.
  move=> s1 s2 s1' s2' Hs1sub Hs2sub /=.
  have Hs1 : (s1 :&: s1' = s1) by move/setIidPl: Hs1sub.
  have Hs2 : (s2 :&: s2' = s2) by move/setIidPl: Hs2sub. 
  rewrite setIA Hs1.
  rewrite {1}[(s1' :&: s2')]setIC setIA Hs2.
  
  rewrite -(setID (s1 :&: s2') s2).
  rewrite wt_join_disjoint; last by apply setID_disjoint.
  rewrite -(setID (s2 :&: s1') s1).
  rewrite wt_join_disjoint; last by apply setID_disjoint.
  rewrite -setIA [s2' :&: s2]setIC Hs2.
  rewrite -setIA [s1' :&: s1]setIC Hs1.
  rewrite addnACA -addnA leq_add2l.
  rewrite setIC addnA.
  
  rewrite -(wt_join_disjoint); last by apply setIID_disjoint.
  rewrite -(wt_join_disjoint); last by apply setIIDD_disjoint.
  apply: wt_inc_leq.
  by apply: setIIDD_subset.
Qed.

Lemma wt_meet_subbound : forall (s1 s1' s2':{set Validator}),
  s1 \subset s1' -> 
  wt (s1 :&: (s1' :&: s2')) + wt (s1' :\: s2') >= wt s1.
Proof.
  move=> s1 s1' s2' Hs1sub.
  have Hs1 : (s1 :&: s1' = s1) by move/setIidPl: Hs1sub.
  rewrite setIA Hs1.
  rewrite -wt_join_disjoint; last by apply setID2_disjoint.  
  apply: wt_inc_leq.
  by apply setID2_subset.
Qed.

Lemma wt_meet_tri_bound : forall s0 s1 s2,
  wt (s1 :\: s2) <= wt (s0 :\: s2) + wt (s1 :\: s0).
Proof.
  move=> s0 s1 s2.
  rewrite -wt_join_disjoint;last by apply set3D_disjoint. 
  apply: wt_inc_leq. apply: set3D_subset.
Qed.

(* The main slashable bound theorem *)
Theorem slashable_bound : forall st b0 b1 b2 b1_h b2_h k1 k2,
  k_finalized st b1 b1_h k1 ->
  k_finalized st b2 b2_h k2 ->
  b1 </~* b2 -> b2 </~* b1 ->
  exists (bL bR:Hash) (qL qR:{set Validator}),
    let v0 := vset.[vs_fun b0] in
    let vL := vset.[vs_fun bL] in
    let vR := vset.[vs_fun bR] in
    let aL := actwt v0 vL in
    let eL := extwt v0 vL in
    let aR := actwt v0 vR in
    let eR := extwt v0 vR in
    let xM := maxn (wt vL - aL - eR)  (wt vR - aR - eL) in
      qL \subset vL /\
      qR \subset vR /\
      wt (qL :&: qR) >= xM - one_third (wt vL) - one_third (wt vR).
Proof. 
intros st b0 b1 b2 b1_h b2_h k1 k2 Hb1f Hb2f Hconf1 Hconf2. 
have [bL [bR [qL [qR [HqLsubset [HqRsubset [HqLq2 [HqRq2 Hqslashed]]]]]]]] := 
   (k_safety' Hb1f Hb2f Hconf2 Hconf1).
clear Hb1f Hb2f Hconf2 Hconf1.
exists bL, bR, qL, qR. repeat (split;[assumption|]).
set v0 := vset.[vs_fun b0].
set vL := vset.[vs_fun bL].
set vR := vset.[vs_fun bR].
set aL := actwt v0 vL.
set eR := extwt v0 vR.
set aR := actwt v0 vR.
set eL := extwt v0 vL.
have Hbound := (wt_meet_bound HqLsubset HqRsubset). simpl in Hbound.
set vLR :=  vset.[vs_fun bL] :&: vset.[vs_fun bR].

have HsubL := (wt_meet_subbound vR HqLsubset).
replace (vset.[vs_fun bL] :&: vR) with vLR in HsubL by trivial.
replace vset.[vs_fun bL] with vL in HsubL by trivial.
have HsubR := (wt_meet_subbound vL HqRsubset).
replace (vset.[vs_fun bR] :&: vL) with vLR in HsubR; last by rewrite setIC.
replace vset.[vs_fun bR] with vR in HsubR by trivial.

rewrite -(leq_add2l (wt (vL :\: vR))) addnA [_ + wt (qL :&: vLR)]addnC in Hbound.
rewrite -(leq_add2r (wt (vR :\: vL))) -[(_ + _) + wt (vR :\: vL)]addnA in Hbound.
have HsubLR := (leq_add HsubL HsubR).
have Hbound' := (leq_trans HsubLR Hbound). clear HsubL HsubR HsubLR Hbound.
rewrite addnA [_ + wt (qL :&: qR)]addnC -addnA [wt vLR +_]addnC -addnA in Hbound'.
rewrite [wt (vL :\: vR) + (_+_)]addnA in Hbound'.
rewrite -wt_join_partition wt_join in Hbound'.
rewrite /quorum_2 in HqLq2. rewrite /quorum_2 in HqRq2.
move/andP: HqLq2 => [_ HqLwt].
move/andP: HqRq2 => [_ HqRwt].
replace vset.[vs_fun bL] with vL in HqLwt by trivial.
replace vset.[vs_fun bR] with vR in HqRwt by trivial.
have HqLR := (leq_add HqLwt HqRwt). clear HqLwt HqRwt.
have Hbound := (leq_trans HqLR Hbound'). clear HqLR Hbound'.

rewrite addnBA in Hbound; last by apply wt_meet_leq.
rewrite [wt vL + wt vR]addnC -leq_subCr in Hbound; last first.
  * by rewrite [wt vR +_]addnC;
    apply (leq_add (wt_nonneg (qL :&: qR)) (wt_meet_leq vL vR)).
  * by rewrite [wt vR +_]addnC;
    apply (leq_add (wt_nonneg (qL :&: qR)) (wt_two_thirds_sum (wt vL) (wt vR))).
  
rewrite subnDA addnA in Hbound.
rewrite addnDAr in Hbound; last by (apply leq_two_thrids).
rewrite thirds_def in Hbound.
rewrite -addnA [wt vR + _]addnC addnA addnDAr in Hbound; last by (apply leq_two_thrids).
rewrite thirds_def in Hbound.

rewrite !leq_subLR addnC [one_third _ + _]addnC -addnA [one_third _ + _]addnC addnA.

have HxL := (wt_diff vL vR).
move/eqP: HxL.
rewrite -(eqn_add2l (wt (vL :&: vR)) (wt (vL :\: vR)) _).
rewrite addnABC;[| by [] |by apply wt_meet_leq1]. 
rewrite sub_eq add0n.
move/eqP => HxL.
have HxLbound := (wt_meet_tri_bound v0 vL vR).
rewrite -(leq_add2l (wt (vL :&: vR))) HxL in HxLbound. clear HxL.
replace (wt (v0 :\: vR)) with eR in HxLbound by trivial.
replace (wt (vL :\: v0)) with aL in HxLbound by trivial.
rewrite addnC -leq_subLR addnC subnDA in HxLbound.

have HxR := (wt_diff vR vL).
move/eqP: HxR.
rewrite -(eqn_add2l (wt (vR :&: vL)) (wt (vR :\: vL)) _).
rewrite addnABC;[| by [] |by apply wt_meet_leq1]. 
rewrite sub_eq add0n.
move/eqP => HxR.
have HxRbound := (wt_meet_tri_bound v0 vR vL).
rewrite -(leq_add2l (wt (vR :&: vL))) HxR in HxRbound. clear HxR.
replace (wt (v0 :\: vL)) with eL in HxRbound by trivial.
replace (wt (vR :\: v0)) with aR in HxRbound by trivial.
rewrite addnC -leq_subLR addnC subnDA wt_meetC in HxRbound.

have HxM : (wt (vL :&: vR) >= maxn (wt vL - aL - eR) (wt vR - aR - eL)) by
  rewrite geq_max;
  have H := (conj HxLbound HxRbound);
  by move/andP: H.
clear HxLbound HxRbound.
apply (leq_trans HxM Hbound).
Qed.


