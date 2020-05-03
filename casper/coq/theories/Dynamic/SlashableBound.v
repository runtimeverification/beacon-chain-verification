Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

From Dynamic
Require Import NatExt Validator Weight HashTree State Slashing Quorums Justification AccountableSafety.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fmap_scope.

(** Activation and Exit Sets **)
(* The set of validators who activated from vs1 to vs2 *)
Definition activated (vs1 vs2: {set Validator}): {set Validator} :=
  vs2 :\: vs1.

(* The set of validators who exited from vs1 to vs2 *)
Definition exited (vs1 vs2: {set Validator}): {set Validator} :=
  vs1 :\: vs2.

(* The weight of new activations from vs1 to vs2 *)
Definition actwt (vs1 vs2: {set Validator}): nat :=
  wt (activated vs1 vs2).

(* The weight of validators who exited from vs1 to vs2 *)
Definition extwt (vs1 vs2: {set Validator}): nat :=
  wt (exited vs1 vs2).

Lemma wt_meetC : forall vs1 vs2,
  wt (vs1 :&: vs2) = wt (vs2 :&: vs1).
Proof. by [rewrite /wt => vs1 vs2;rewrite setIC]. Qed.

Lemma wt_meet_bound : forall (s1 s2 s1' s2':{set Validator}),
  s1 \subset s1' -> 
  s2 \subset s2' ->
  let s12' := (s1' :&: s2') in 
    wt (s1 :&: s2) + wt s12' >= wt (s1 :&: s12') + wt (s2 :&: s12').
Proof. Admitted.

Lemma wt_meet_subbound : forall (s1 s1' s2':{set Validator}),
  s1 \subset s1' -> 
  wt (s1 :&: (s1' :&: s2')) + wt (s1' :\: s2') >= wt s1.
Proof. Admitted.

Lemma set3DD_disjoint : forall (vs0 vs1 vs2:{set Validator}),
  [disjoint vs0 :\: vs2 & vs1 :\: vs0].
Proof.
  move=> vs0 vs1 vs2.
  rewrite -setI_eq0 eqEsubset.
  apply/andP;split;apply/subsetP => x;last by rewrite in_set0.
  move/setIP=> [H1 H2].
  move/setDP: H1 => [H1a H1b].
  move/setDP: H2 => [H2a H2b].
  move/negP: H2b => H2b.
  by contradiction.
Qed.

Lemma set3D_subset : forall (vs0 vs1 vs2:{set Validator}),
  vs1 :\: vs2 \subset vs0 :\: vs2 :|: vs1 :\: vs0.
Proof. 
  move=> vs0 vs1 vs2.
  apply/subsetP => x.
  move/setDP=> [H1 H2].  
  apply/setUP.
  have : (x \in vs0) || ~~(x \in vs0) by apply orbN.
  case/orP=> H.
  - left. by apply/setDP;split.
  - right. by apply/setDP;split.  
Qed.

Lemma wt_meet_tri_bound : forall vs0 vs1 vs2,
  wt (vs1 :\: vs2) <= wt (vs0 :\: vs2) + wt (vs1 :\: vs0).
Proof.
  move=> vs0 vs1 vs2.
  rewrite -wt_join_disjoint;last by apply set3DD_disjoint. 
  apply: wt_inc_leq. apply: set3D_subset.
Qed.

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


