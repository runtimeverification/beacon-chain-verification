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

Lemma wt_join_partition : forall vs1 vs2,
  wt (vs1 :|: vs2) = wt (vs1 :\: vs2) + wt (vs2 :\: vs1) + wt (vs1 :&: vs2).
Proof. Admitted.
  
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

Lemma wt_meet_tri_bound : forall vs0 vs1 vs2,
  wt (vs1 :\: vs2) <= wt (vs0 :\: vs2) + wt (vs1 :\: vs0).
Proof. Admitted.

Theorem slashable_bound : forall st b0 b1 b2 b0_h b1_h b2_h k0 k1 k2,
  k_finalized st b0 b0_h k0 ->
  k_finalized st b1 b1_h k1 ->
  k_finalized st b2 b2_h k2 ->
  b0 <~* b1 -> b0 <> b1 ->
  b0 <~* b2 -> b0 <> b2 ->
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
Admitted.


