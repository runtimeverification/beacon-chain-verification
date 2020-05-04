Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

From Dynamic
Require Import NatExt Validator.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fmap_scope.

(* A finite map defining the weight of a given set of validators 
 *)
Definition wt (vs:{set Validator}) : nat := 
  (\sum_(v in vs) stake.[st_fun v]).

Lemma wt_nonneg : forall vs, wt vs >= 0.
Proof. by []. Qed.

Lemma wt_set0 : wt set0 = 0.
Proof.
by rewrite /wt big_set0.
Qed.

Lemma wt_inc_leq : forall (vs1 vs2:{set Validator}),
  vs1 \subset vs2 -> wt vs1 <= wt vs2.
Proof. 
  move=> vs1 vs2.
  rewrite /wt.
  rewrite [\sum_(v in vs2) _](big_setID vs1) //=.
  move/setIidPr => ->.
  apply: leq_addr.
Qed.

Lemma wt_eq : forall (vs1 vs2:{set Validator}),
  vs1 = vs2 -> wt vs1 = wt vs2.
Proof.
  move=> vs1 vs2 Heq.
  by rewrite /wt Heq.
Qed.

Lemma wt_aidem : forall v (vs:{set Validator}), 
  v \in vs -> wt (v |: vs) = wt vs.
Proof. Admitted. 

Lemma wt_ext : forall v (vs:{set Validator}), 
  v \notin vs -> wt (v |: vs) = (stake.[st_fun v] + wt vs).
Proof. Admitted. 

(* In this case, wt (vs :\ v) >= 0 should also be provable *)
Lemma wt_drop : forall v (vs:{set Validator}), 
  v \in vs -> wt (vs :\ v) = wt vs - stake.[st_fun v].
Proof. Admitted.

Lemma wt_didem : forall v (vs:{set Validator}), 
  v \notin vs -> wt (vs :\ v) = wt vs.
Proof. Admitted.

Lemma wt_ext_monotonic : forall v vs, wt vs <= wt (v |: vs).
Proof. Admitted.

Lemma wt_drop_monotonic : forall v vs, wt (vs :\ v) <= wt vs.
Proof. Admitted.

(* wt (vs :&: v) >= 0 should also be provable *)
Lemma wt_meet : forall s1 s2,
  wt (s1 :&: s2) = wt s1 + wt s2 - wt (s1 :|: s2).
Proof. Admitted.

(* wt (~: vs) >= 0 should also be provable *)
Lemma wt_comp : forall vs,
  wt (~: vs) = wt [set: Validator] - wt vs.
Proof. Admitted.
  
Lemma wt_join_disjoint : forall (vs1 vs2:{set Validator}),
  [disjoint vs1 & vs2] -> wt (vs1 :|: vs2) = wt vs1 + wt vs2.
Proof.
  move=> vs1 vs2 Hdis.
  rewrite /wt.
  rewrite (eq_bigl [predU vs1 & vs2]); last by move=> i; rewrite !inE.
  rewrite bigU //=.  
(*
  rewrite -setI_eq0.
  move/eqP=> H.
  by rewrite wt_join H wt_set0 subn0.
*)
Qed.

Lemma setID_disjoint : forall (vs1 vs2:{set Validator}),
  [disjoint (vs1 :&: vs2) & (vs1 :\: vs2)].
Proof.
  move=> vs1 vs2.
  rewrite -setI_eq0 eqEsubset.
  apply/andP;split;apply/subsetP => x;last by rewrite in_set0.
  move/setIP=> [H1 H2].
  move/setIP: H1 => [_ H1].
  move/setDP: H2 => [_ H2].
  move/negP: H2 => H2.
  by contradiction.
Qed.

Lemma setDD_disjoint : forall (vs1 vs2:{set Validator}),
  [disjoint (vs1 :\: vs2) & (vs2 :\: vs1)].
Proof.
  move=> vs1 vs2.
  rewrite -setI_eq0 eqEsubset.
  apply/andP;split;apply/subsetP => x;last by rewrite in_set0.
  move/setIP=> [H1 H2].
  move/setDP: H1 => [H1a H1b].
  move/setDP: H2 => [H2a H2b].
  move/negP: H2b => H2b.
  by contradiction.
Qed.

Lemma setDDI_disjoint : forall (vs1 vs2:{set Validator}),
  [disjoint vs1 :\: vs2 :|: vs2 :\: vs1 & vs1 :&: vs2].
Proof. 
  move=> vs1 vs2.
  rewrite -setI_eq0 eqEsubset.
  apply/andP;split;apply/subsetP => x;last by rewrite in_set0.
  move/setIP=> [H1 H2].
  move/setIP: H2 => [Hin1 Hin2].
  case/setUP: H1 => H;move/setDP: H => [_ Hnotin2];
    move/negP: Hnotin2 => Hnotin2;contradiction.
Qed.

(* wt (vs1 :\: vs2) >= 0 should also be provable *)
Lemma wt_diff : forall vs1 vs2,
  wt (vs1 :\: vs2) = wt vs1 - wt (vs1 :&: vs2).
Proof.
  move=> vs1 vs2.
  rewrite -{2}(setID vs1 vs2).
  rewrite (wt_join_disjoint).
    rewrite addnC -addnBA; last by [].
    by rewrite sub_eq addn0.
  by apply: setID_disjoint.
Qed.

Lemma setU_par : forall (vs1 vs2:{set Validator}),
  vs1 :|: vs2 = (vs1 :\: vs2) :|: (vs2 :\: vs1) :|: (vs1 :&: vs2).
Proof.
  move=> vs1 vs2.
  apply/eqP.
  rewrite eqEsubset.
  apply/andP;split;apply/subsetP => x.
  case/setUP=> H.
  - rewrite -setUA setUC -setUA.
    apply/setUP;right. 
    by rewrite setUC -setDDr setDv setD0.
  - rewrite -setUA.
    apply/setUP;right.
    by rewrite setIC -setDDr setDv setD0.
  case/setUP=> H.
  - case/setUP: H => H.
    * move/setDP: H => [H _].
      by apply/setUP;left.
    * move/setDP: H => [H _].
      by apply/setUP;right.
  - move/setIP: H => [H _].
    by apply/setUP;left.
Qed.

Lemma wt_join_partition : forall vs1 vs2,
  wt (vs1 :|: vs2) = wt (vs1 :\: vs2) + wt (vs2 :\: vs1) + wt (vs1 :&: vs2).
Proof.
  move=> vs1 vs2.
  rewrite -!wt_join_disjoint. 
  apply: wt_eq. apply: setU_par.
  apply: setDDI_disjoint.
  apply: setDD_disjoint.
Qed.

(* wt (vs :|: v) >= 0 should also be provable *)
Lemma wt_join : forall vs1 vs2,
  wt (vs1 :|: vs2) = wt vs1 + wt vs2 - wt (vs1 :&: vs2).
Proof.
  move=> vs1 vs2.
  rewrite -{2}(setID vs1 vs2).
  rewrite -{4}(setID vs2 vs1).
  rewrite [wt (vs1 :&: vs2 :|: _)]wt_join_disjoint; last by apply setID_disjoint.
  rewrite [wt (vs2 :&: vs1 :|: _)]wt_join_disjoint; last by apply setID_disjoint.
  rewrite [vs2 :&: vs1]setIC.
  rewrite -addnA [_ + wt (vs2 :\: vs1)]addnC.  
  rewrite [wt (vs1 :\: vs2) + (_+_)]addnA.
  rewrite -wt_join_partition. 
  rewrite -addnBAC; last by [].
  by rewrite sub_eq add0n.
Qed.

Lemma wt_meet_leq1 : forall vs1 vs2,
  wt (vs1 :&: vs2) <= wt vs1.
Proof. 
  move=> vs1 vs2; apply: wt_inc_leq; apply: subsetIl.
Qed.

Lemma wt_meet_leq2 : forall vs1 vs2,
  wt (vs1 :&: vs2) <= wt vs2.
Proof. 
  move=> vs1 vs2; apply: wt_inc_leq; apply: subsetIr.
Qed.

Lemma wt_meet_leq : forall vs1 vs2,
  wt (vs1 :&: vs2) <= wt vs1 + wt vs2.
Proof.
  move=> vs1 vs2.
  have H1:= (wt_meet_leq1 vs1 vs2).
  have H2:= (leq_addr (wt vs2) (wt vs1)).
  apply: (leq_trans H1 H2).
Qed.

