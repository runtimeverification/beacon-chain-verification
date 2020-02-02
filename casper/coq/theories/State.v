Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

From Casper
Require Import Quorums HashTree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Each vote names source and target nodes by giving hash and height,
   and is signed by a particular validator.
   This definition is different from votes in AccountableSafety.v,
   this is taken directly from the way votes are expressed in the
   Casper paper.supermajority
 *)
Definition Vote := (Validator * Hash * Hash * nat * nat)%type.
(* A State is described by the set of votes case in the current epoch.
   For liveness we insist that this be a finite set of votes.
 *)

Definition State := {fset Vote}.

(* A boolean vote_msg predicate is then a definition rather than
   a field of State as in AccountableSafety.v 
   Further constraints on what constitutes a valid vote message have
   been added *)
Definition vote_msg (st:State) v s t (s_h t_h:nat) : bool
  := ((v,s,t,s_h,t_h) \in st) .

