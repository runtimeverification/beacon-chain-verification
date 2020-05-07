Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

From Dynamic
Require Import NatExt SetTheoryProps Validator.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fmap_scope.

(******************************************************************************)
(* Definitions and properties of the function `wt' mapping validator sets to  *)
(* values corresponding to their weights. Many of these results follow from   *)
(* properties of \sum and set-theoretic properties of set operations.         *)
(******************************************************************************)

(* A finite map defining the weight of a given set of validators as the sum of
 * stake values of its validators
 *)
Definition wt (s:{set Validator}) : nat := 
  (\sum_(v in s) stake.[st_fun v]).

(* wt is always non-negative *)
Lemma wt_nonneg s: wt s >= 0.
Proof. by []. Qed.

(* wt of the empty set is always 0 *)
Lemma wt_set0 : wt set0 = 0.
Proof.
by rewrite /wt big_set0.
Qed.

(* set inclusion induces an order on weights *)
Lemma wt_inc_leq (s1 s2:{set Validator}):
  s1 \subset s2 -> wt s1 <= wt s2.
Proof. 
  rewrite /wt.
  rewrite [\sum_(v in s2) _](big_setID s1) //=.
  move/setIidPr => ->.
  apply: leq_addr.
Qed.

(* equal sets have the same weight *)
Lemma wt_eq (s1 s2:{set Validator}):
  s1 = s2 -> wt s1 = wt s2.
Proof.
  move=> Heq.
  by rewrite /wt Heq.
Qed.

(* sets commute under wt *)
Lemma wt_meetC (s1 s2:{set Validator}):
  wt (s1 :&: s2) = wt (s2 :&: s1).
Proof. 
  by [rewrite /wt setIC].
Qed.

(* the weight of the union of two disjoint sets is exactly the sum of 
 * their weights 
 *)
Lemma wt_join_disjoint (s1 s2:{set Validator}):
  [disjoint s1 & s2] -> wt (s1 :|: s2) = wt s1 + wt s2.
Proof.
  move=> Hdis.
  rewrite /wt.
  rewrite (eq_bigl [predU s1 & s2]); last by move=> i; rewrite !inE.
  rewrite bigU //=.
Qed.

(* The weight of the difference of two sets *)
Lemma wt_diff (s1 s2:{set Validator}):
  wt (s1 :\: s2) = wt s1 - wt (s1 :&: s2).
Proof.
  rewrite -{2}(setID s1 s2).
  rewrite (wt_join_disjoint).
    rewrite addnC -addnBA; last by [].
    by rewrite sub_eq addn0.
  by apply: setID_disjoint.
Qed.

(* The weight of the union of two sets as the sum of weights of its partitions *)
Lemma wt_join_partition (s1 s2:{set Validator}):
  wt (s1 :|: s2) = wt (s1 :\: s2) + wt (s2 :\: s1) + wt (s1 :&: s2).
Proof.
  rewrite -!wt_join_disjoint. 
  apply: wt_eq. apply: setU_par.
  apply: setDDI_disjoint.
  apply: setDD_disjoint.
Qed.

(* The weight of the union of two sets in terms of the weights of the sets *)
Lemma wt_join (s1 s2:{set Validator}):
  wt (s1 :|: s2) = wt s1 + wt s2 - wt (s1 :&: s2).
Proof.
  rewrite -{2}(setID s1 s2).
  rewrite -{4}(setID s2 s1).
  rewrite [wt (s1 :&: s2 :|: _)]wt_join_disjoint; last by apply setID_disjoint.
  rewrite [wt (s2 :&: s1 :|: _)]wt_join_disjoint; last by apply setID_disjoint.
  rewrite [s2 :&: s1]setIC.
  rewrite -addnA [_ + wt (s2 :\: s1)]addnC.  
  rewrite [wt (s1 :\: s2) + (_+_)]addnA.
  rewrite -wt_join_partition. 
  rewrite -addnBAC; last by [].
  by rewrite sub_eq add0n.
Qed.

(* Properties of the weight of the intersection of two sets *)
Lemma wt_meet_leq1 (s1 s2:{set Validator}):
  wt (s1 :&: s2) <= wt s1.
Proof. 
  apply: wt_inc_leq; apply: subsetIl.
Qed.

Lemma wt_meet_leq2 (s1 s2:{set Validator}):
  wt (s1 :&: s2) <= wt s2.
Proof. 
  apply: wt_inc_leq; apply: subsetIr.
Qed.

Lemma wt_meet_leq (s1 s2:{set Validator}):
  wt (s1 :&: s2) <= wt s1 + wt s2.
Proof.
  have H1:= (wt_meet_leq1 s1 s2).
  have H2:= (leq_addr (wt s2) (wt s1)).
  apply: (leq_trans H1 H2).
Qed.

