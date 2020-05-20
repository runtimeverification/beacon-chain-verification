Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

From Casper
Require Import NatExt.

From Casper
Require Import Validator Weight HashTree State Slashing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fmap_scope.
Open Scope big_scope.

(******************************************************************************)
(* Validator sets, quorums and quorum properties                              *)
(******************************************************************************)


(* A finite map vset defining the set of validators for a given block       *)
Parameter vset : {fmap Hash -> {set Validator}}.

(* We assume the map vset is total                                          *)
Axiom vs_fun : forall h : Hash, h \in vset.

(** Quorum Predicates **)
(* A predicate for an "at least 1/3 weight" set of validators               *)
Definition quorum_1 (vs : {set Validator}) (b : Hash) : bool :=
  (vs \subset vset.[vs_fun b]) && 
  (wt vs >= one_third (wt vset.[vs_fun b])).

(* A predicate for an "at least 2/3 weight" set of validators               *)
Definition quorum_2 (vs : {set Validator}) (b : Hash) : bool :=
  (vs \subset vset.[vs_fun b]) && 
  (wt vs >= two_third (wt vset.[vs_fun b])).

(* Meaning of a validator set being slashed in the general context of       *)
(* dynamic validator sets                                                   *)
Definition q_intersection_slashed st :=
  exists (bL bR: Hash) (vL vR: {set Validator}),
    vL \subset vset.[vs_fun bL] /\ 
    vR \subset vset.[vs_fun bR] /\
    quorum_2 vL bL /\ 
    quorum_2 vR bR /\
    forall v, v \in vL -> v \in vR -> slashed st v.

(* The assumption on quorums that a supermajority quorum with respect to a  *)
(* block is nonempty (Needed for liveness)                                  *)
Axiom quorum_2_nonempty:
  forall (b:Hash) (q :{set Validator}), 
    quorum_2 q b -> exists v, v \in q.

(* The property that, with respect to a block b, adding more b-validators *)
(* to a supermajority leaves a supermajority (Needed for liveness)        *)
Lemma quorum_2_upclosed:
  forall (b:Hash) (q q':{set Validator}), 
    q \subset q' -> q' \subset vset.[vs_fun b] -> quorum_2 q b -> 
    quorum_2 q' b.
Proof.
  move=> b q q' Hqsubq' Hq'.
  rewrite /quorum_2.
  move/andP=> [Hq Hqwt].
  apply/andP;split. exact Hq'.
  apply wt_inc_leq in Hqsubq'.
  by apply (leq_trans Hqwt Hqsubq').  
Qed.


