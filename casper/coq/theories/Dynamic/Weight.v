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

Lemma wt_mt_zero : wt set0 = 0.
Proof.
Admitted.

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

(* wt (vs :|: v) >= 0 should also be provable *)
Lemma wt_join : forall vs1 vs2,
  wt (vs1 :|: vs2) = wt vs1 + wt vs2 - wt (vs1 :&: vs2).
Proof. Admitted.

(* wt (~: vs) >= 0 should also be provable *)
Lemma wt_comp : forall vs,
  wt (~: vs) = wt [set: Validator] - wt vs.
Proof. Admitted.
  
(* wt (vs1 :\: vs2) >= 0 should also be provable *)
Lemma wt_diff : forall vs1 vs2,
  wt (vs1 :\: vs2) = wt vs1 - wt (vs1 :&: vs2).
Proof. Admitted.
  
Lemma wt_inc_leq : forall (vs1 vs2:{set Validator}),
  vs1 \subset vs2 -> wt vs1 <= wt vs2.
Proof. Admitted.

Lemma wt_meet_leq : forall vs1 vs2,
  wt (vs1 :&: vs2) <= wt vs1 + wt vs2.
Proof. Admitted.

Lemma wt_meet_leq1 : forall vs1 vs2,
  wt (vs1 :&: vs2) <= wt vs1.
Proof. Admitted.

