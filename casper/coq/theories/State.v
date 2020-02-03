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
   and is signed by a particular validator. This is taken directly from
   the way votes are expressed in the Casper paper.
 *)
Definition Vote := (Validator * Hash * Hash * nat * nat)%type.

(* A State is described by the finite set of votes cast.
 *)
Definition State := {fset Vote}.

(* A boolean vote_msg predicate that tells us whether a vote belongs to
   the state
 *)
Definition vote_msg (st:State) v s t (s_h t_h:nat) : bool
  := (v,s,t,s_h,t_h) \in st .

