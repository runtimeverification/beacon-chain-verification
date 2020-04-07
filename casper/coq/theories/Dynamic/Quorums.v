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

(* A finite map vset defining the set of validators for a given block *)
Parameter vset : {fmap Hash -> {set Validator}}.

(* We assume the map vset is total *)
Axiom vs_fun : forall h : Hash, h \in vset.

(* A finite map defining the stake (weight) of a validator *)
(* Note: weight is currently nat (will probably use reals in the future) *)
Parameter stake : {fmap Validator -> nat}.

(* We assume the map stake is total *)
Axiom st_fun : forall v : Validator, v \in stake.

(* A finite map defining the weight of a given set of validators 
 *)
Definition wt (vs:{set Validator}) : nat := \sum_(v in vs) stake.[st_fun v].

(* We assume the map weight is both total and zero at the empty set *)
(* Axiom wt_fun  : forall s : {set Validator}, s \in wt.
Axiom wt_zero : forall s : {set Validator}, wt.[wt_fun s] == 0 <-> s == set0.
*)

(** Quorum Predicates **)
(* A predicate for an "at least 1/3 weight" set of validators *)
Definition quorum_1 (vs : {set Validator}) (b : Hash) : bool :=
  (vs \subset vset.[vs_fun b]) && 
  (wt vs >= (wt vset.[vs_fun b] %/ 3)).

(* A predicate for an "at least 2/3 weight" set of validators *)
Definition quorum_2 (vs : {set Validator}) (b : Hash) : bool :=
  (vs \subset vset.[vs_fun b]) && 
  (wt vs >= (2 * wt vset.[vs_fun b] %/ 3)).

(* Meaning of a validator set being slashed in thr context of dynamic validator sets *)
Definition q_intersection_slashed st :=
  exists (bL bR: Hash) (vL vR: {set Validator}),
    vL \subset vset.[vs_fun bL] /\ 
    vR \subset vset.[vs_fun bR] /\
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
    q \subset q' -> q' \subset vset.[vs_fun b] -> quorum_2 q b -> 
    quorum_2 q' b.

