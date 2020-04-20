Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma sub_eq n : n - n = 0. 
Proof. by elim: n => [|n IHn]. Qed.

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

Parameter one_third : nat -> nat.
Parameter two_third : nat -> nat.
Axiom thirds_def : forall n, n - two_third n = one_third n.
Axiom leq_two_thrids : forall n, two_third n <= n.

Lemma wt_two_thirds_sum : forall n m,
  two_third n + two_third m <= n + m.
Proof. 
by move => n m; apply: (leq_add (leq_two_thrids n) (leq_two_thrids m)).
Qed.

