Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

From Dynamic
Require Import Validator HashTree State.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* Definitions of the slashing conditions                                     *)
(******************************************************************************)

(* A validator may not make two votes with different target hashes at
   the same target height (whatever the source blocks)
 *)
Definition slashed_dbl_vote st v :=
  exists t1 t2, t1 <> t2 /\ exists s1 s1_h s2 s2_h t_h,
      vote_msg st v s1 t1 s1_h t_h /\ vote_msg st v s2 t2 s2_h t_h.

(* A validator may not make two votes with the source and target of
   one vote both strictly between the source and target of the other
 *)
Definition slashed_surround st v :=
  exists s1 t1 s1_h t1_h,
  exists s2 t2 s2_h t2_h,
    vote_msg st v s1 t1 s1_h t1_h /\
     vote_msg st v s2 t2 s2_h t2_h /\
     s2_h > s1_h /\ t2_h < t1_h.

(* A slashed validator is one that has double-voted or surround-voted *)
Definition slashed st v : Prop :=
 slashed_dbl_vote st v \/ slashed_surround st v.
