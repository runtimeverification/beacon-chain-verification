Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

From Dynamic
Require Import NatExt Validator SetTheoryProps.

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

Lemma wt_meetC : forall vs1 vs2,
  wt (vs1 :&: vs2) = wt (vs2 :&: vs1).
Proof. by [rewrite /wt => vs1 vs2;rewrite setIC]. Qed.

Lemma wt_join_disjoint : forall (vs1 vs2:{set Validator}),
  [disjoint vs1 & vs2] -> wt (vs1 :|: vs2) = wt vs1 + wt vs2.
Proof.
  move=> vs1 vs2 Hdis.
  rewrite /wt.
  rewrite (eq_bigl [predU vs1 & vs2]); last by move=> i; rewrite !inE.
  rewrite bigU //=.  
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

