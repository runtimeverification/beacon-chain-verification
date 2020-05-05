Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fmap_scope.

(******************************************************************************)
(* Validators and validator stake                                             *)
(******************************************************************************)

(* We assume finite sets of validators *)
Parameter Validator : finType.

(* A finite map defining the stake (weight) of a validator *)
(* Note: weight is a nat *)
Parameter stake : {fmap Validator -> nat}.

(* We assume the map stake is total *)
Axiom st_fun : forall v : Validator, v \in stake.

