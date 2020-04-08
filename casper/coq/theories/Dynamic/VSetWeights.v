Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

From Dynamic
Require Import Validator HashTree State Slashing Quorums.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fmap_scope.

Lemma wt_nonneg : forall vs, wt vs >= 0.
Proof. by []. Qed.

Lemma wt_mt_zero : wt set0 = 0.
Proof. 

Admitted.

Lemma wt_ext : forall v vs, wt (v |: vs) = wt [set v] + wt vs. 
Proof. Admitted. 

Lemma wt_drop : forall v vs, wt (vs :\ v) = wt vs - wt [set v].
Proof. Admitted.

Lemma wt_ext_monotonic : forall v vs, wt vs <= wt (v |: vs).
Proof. Admitted.

Lemma wt_drop_monotonic : forall v vs, wt (vs :\ v) <= wt vs.
Proof. Admitted.

Lemma wt_meet : forall s1 s2,
  wt (s1 :&: s2) = wt s1 + wt s2 - wt (s1 :|: s2).
Proof. Admitted.

Lemma wt_join : forall s1 s2,
  wt (s1 :|: s2) = wt s1 + wt s2 - wt (s1 :&: s2).
Proof. Admitted.

Lemma wt_comp : forall s,
  wt (~: s) = wt [set: Validator] - wt s.
Proof. Admitted.
  
Lemma wt_diff : forall s1 s2,
  wt (s1 :\: s2) = wt s1 - wt (s1 :&: s2).
Proof. Admitted.
  



(** Activation and Exit Sets **)
(* The set of validators who activated from vs1 to vs2 *)
Definition activated (vs1 vs2: {set Validator}): {set Validator} :=
  vs2 :\: vs1.

(* The set of validators who exited from vs1 to vs2 *)
Definition exited (vs1 vs2: {set Validator}): {set Validator} :=
  vs1 :\: vs2.

(* The weight of new activations from vs1 to vs2 *)
Definition activated_weight (vs1 vs2: {set Validator}): nat :=
  wt.[wt_fun (activated vs1 vs2)].

(* The weight of validators who exited from vs1 to vs2 *)
Definition exited_weight (vs1 vs2: {set Validator}): nat :=
  wt.[wt_fun (exited vs1 vs2)].

