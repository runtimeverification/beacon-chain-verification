Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* We assume finite sets of validators *)
Parameter Validator : finType.
