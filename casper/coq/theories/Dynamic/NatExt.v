Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From mathcomp.finmap
Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* Some basic extentions/properties of nats needed in the rest of the specs.  *)
(******************************************************************************)

(* The `highest' value in a finite set of nats *)
Definition highest (A : {fset nat}) : nat :=
  \max_(i : A) (val i).

(* The `highest' is the maximum value *)
Lemma highest_ub:
  forall (A : {fset nat}) (x:nat), x \in A -> x <= highest A.
Proof.
move => A x Hx.
case (insubP [subType of A] x) => /=; last by move: Hx =>->.
move => k Hk =><-.
exact: leq_bigmax_cond.
Qed.

(* The successor cannot be smaller *)
Lemma ltSnn n: (n.+1 < n) = false.
Proof.
by apply/negP/negP; rewrite leqNgt; apply/negP; case/negP.
Qed.

(* Basic subtraction fact *)
Lemma sub_eq n : n - n = 0. 
Proof. by elim: n => [|n IHn]. Qed.

(* Conditional associativity of add-sub *)
Lemma addnDAr n m p :
  m >= p -> (n + m) - p = n + (m - p).
Proof. 
  elim: n m => [|n IHn] [|m IHm];trivial.
  rewrite leqn0.
  by move/eqP => Hp;subst.
  apply IHn in IHm as IH.
  rewrite [in RHS]addSnnS -[in RHS]addn1  [in RHS]addnA.
  rewrite -IH.
  rewrite addSn. rewrite [in LHS]subSn. by rewrite [in RHS]addn1. 
  apply (leq_trans IHm). clear.
  elim: m => [|m IHm]. rewrite addn1. apply ltn0Sn.
  by rewrite -addn1 addnA leq_add2r.
Qed.

(* Two uninterpreted functions are introduced to represent quantities that will be *)
(* used in the statement of the slashsable bound theorem. These are not strictly   *)
(* necessary, but they enable using statements and proof arguments that are closer *)
(* to the paper. *)
Parameter one_third : nat -> nat.
Parameter two_third : nat -> nat.

(* Basic axioms assumed to hold for these function symbols *)
Axiom thirds_def : forall n, n - two_third n = one_third n.
Axiom leq_two_thrids : forall n, two_third n <= n.

(* This property follows from leq_two_thrids above *)
Lemma wt_two_thirds_sum : forall n m,
  two_third n + two_third m <= n + m.
Proof. 
by move => n m; apply: (leq_add (leq_two_thrids n) (leq_two_thrids m)).
Qed.

