Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

From Casper
Require Import Validator HashTree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* A representation of state as a set of votes cast.                          *)
(*                                                                            *)
(* Each vote names source and target nodes by giving hash and height, and is  *)
(* signed by a particular validator. This is taken directly from the way      *)
(* votes are expressed in the Casper paper.                                   *)
(******************************************************************************)

(* A vote is a tuple: 
 *        (attestor, source, target, source height, target height) 
 *)
Definition Vote := (Validator * Hash * Hash * nat * nat)%type.

(* A State is described by the finite set of votes cast.
 *)
Definition State := {fset Vote}.

(* A boolean vote_msg predicate that tells us whether a vote belongs to
 * the state
 *)
Definition vote_msg (st:State) v s t (s_h t_h:nat) : bool
  := (v,s,t,s_h,t_h) \in st .

(* Vote projection operations *)
Definition vote_val (v:Vote) : Validator :=
  match v with
    (x,_,_,_,_) => x
  end.

Definition vote_source (v:Vote) : Hash :=
  match v with
    (_,s,_,_,_) => s
  end.

Definition vote_target (v:Vote) : Hash :=
  match v with
    (_,_,t,_,_) => t
  end.

Definition vote_source_height (v:Vote) : nat :=
  match v with
    (_,_,_,s_h,_) => s_h
  end.

Definition vote_target_height (v:Vote) : nat :=
  match v with
    (_,_,_,_,t_h) => t_h
  end.

(* Reconstructing a vote using its projections *)
Lemma vote_unfold (vote:Vote):
  vote = ((vote_val           vote),
          (vote_source        vote),
          (vote_target        vote),
          (vote_source_height vote),
          (vote_target_height vote)).
Proof.
  by move:vote=>[[[[v s] t] s_h] t_h].
Qed.