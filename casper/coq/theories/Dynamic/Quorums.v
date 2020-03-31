Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

From Dynamic
Require Import Validator HashTree State Slashing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fmap_scope.

(* A finite map vSet defining the set of validators for a given block *)
Parameter vSet : {fmap Hash -> {set Validator}}.

(* We assume the map vSet is total *)
Axiom vs_fun : forall h : Hash, h \in vSet.

(** Activation and Exit Sets **)
(* The set of validators who activated from vs1 to vs2 *)
Definition activated (vs1 vs2: {set Validator}): {set Validator} :=
  vs2 :\: vs1.

(* The set of validators who exited from vs1 to vs2 *)
Definition exited (vs1 vs2: {set Validator}): {set Validator} :=
  vs1 :\: vs2.

(* A finite map defining the weight of a given set of validators 
   Note: weight is currently nat (will probably use real in the future)
 *)
Parameter weight : {fmap {set Validator} -> nat}.

(* We assume the map weight is both total and zero at the empty set *)
Axiom wt_fun  : forall s : {set Validator}, s \in weight.
Axiom wt_zero : forall s : {set Validator}, weight.[wt_fun s] == 0 <-> s == set0.

(* The weight of new activations from vs1 to vs2 *)
Definition activated_weight (vs1 vs2: {set Validator}): nat :=
  weight.[wt_fun (activated vs1 vs2)].

(* The weight of validators who exited from vs1 to vs2 *)
Definition exited_weight (vs1 vs2: {set Validator}): nat :=
  weight.[wt_fun (exited vs1 vs2)].

(** Quorums **)
(* A predicate for an "at least 1/3 weight" set of validators *)
Definition quorum_1 (vs : {set Validator}) (b : Hash) : bool :=
  (vs \subset vSet.[vs_fun b]) && 
  (weight.[wt_fun vs] >= (weight.[wt_fun vSet.[vs_fun b]] %/ 3)).

(* A predicate for an "at least 2/3 weight" set of validators *)
Definition quorum_2 (vs : {set Validator}) (b : Hash) : bool :=
  (vs \subset vSet.[vs_fun b]) && 
  (weight.[wt_fun vs] >= (2 * weight.[wt_fun vSet.[vs_fun b]] %/ 3)).

(* Meaning of a validator set being slashed in thr context of dynamic validator sets *)
Definition q_intersection_slashed st :=
  exists (bL bR: Hash) (vL vR: {set Validator}),
    vL \subset vSet.[vs_fun bL] /\ 
    vR \subset vSet.[vs_fun bR] /\
    quorum_2 vL bL /\ 
    quorum_2 vR bR /\
    forall v, v \in vL -> v \in vR -> slashed st v.

(* The assumption on quorums that a supermajority quorum with respect to
   a block is nonempty (Needed for liveness) *)
Axiom quorum_2_nonempty:
  forall (b:Hash) (q :{set Validator}), 
    quorum_2 q b -> exists v, v \in q.


(* The assumption that, with respect to a block b, adding more b-validators
   to a supermajority with respect to b leaves a supermajority (Needed for 
   liveness) *)
Axiom quorum_2_upclosed:
  forall (b:Hash) (q q':{set Validator}), 
    q \subset q' -> q' \subset vSet.[vs_fun b] -> quorum_2 q b -> 
    quorum_2 q' b.

