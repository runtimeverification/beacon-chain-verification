Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Validator is a type of finite sets *)
Parameter Validator : finType.

(* The sets of "at least 1/3 weight" validators *)
Parameter quorum_1 : {set {set Validator}}.

(* The sets of "at least 2/3 weight" validators *)
Parameter quorum_2 : {set {set Validator}}.

(* The essential intersection property that comes from the
   numeric choices 2/3 and 1/3 - any two sets from quorum_2
   have an intersection containing a quorum_1 set. *)
Axiom quorums_intersection_property :
  forall (q2 q2': {set Validator}), q2 \in quorum_2 -> q2' \in quorum_2 ->
  exists q1, q1 \in quorum_1 /\ q1 \subset q2 /\ q1 \subset q2'.

(* The quorums property is a re-statement of the property above *)
Lemma quorums_property :
 forall (q2 q2': {set Validator}), q2 \in quorum_2 -> q2' \in quorum_2 ->
 exists q1, q1 \in quorum_1 /\ forall n, n \in q1 -> n \in q2 /\ n \in q2'.
Proof.
move => q1 q2 Hq1 Hq2.
have [q3 [Hq3 [Hq13 Hq23]]] := (quorums_intersection_property Hq1 Hq2).
exists q3.
split => //.
move => n Hn.
split.
- by apply/(subsetP Hq13).
- by apply/(subsetP Hq23).
Qed.

(* For liveness proof we use additional assumptions on quorums that
   a supermajority quorum is nonempty *)
Axiom quorum_2_nonempty:
  forall (q :{set Validator}), q \in quorum_2 -> exists v, v \in q.

(* and that adding more validators to a supermajority leaves a 
   supermajority. *)
Axiom quorum_2_upclosed:
  forall (q q':{set Validator}), q \subset q' -> q \in quorum_2 -> q' \in quorum_2.
