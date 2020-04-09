Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

From Dynamic
Require Import Validator HashTree State Slashing Quorums Weight Justification AccountableSafety.

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
Definition activated_weight (vs1 vs2: {set Validator}): nat :=
  wt (activated vs1 vs2).

(* The weight of validators who exited from vs1 to vs2 *)
Definition exited_weight (vs1 vs2: {set Validator}): nat :=
  wt (exited vs1 vs2).
