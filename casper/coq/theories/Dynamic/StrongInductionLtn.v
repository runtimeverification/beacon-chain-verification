Set Warnings "-parsing".
From mathcomp
Require Import all_ssreflect.
Set Warnings "parsing".

(******************************************************************************)
(*  This utility module proves a few induction principles used in other       *)
(*  proofs.                                                                   *)
(******************************************************************************)

(* Two strong induction principles over natural numbers,
   as represented in the MathComp library.
   Adapted from work by Tej Chajed. *)

Section StrongInductionLtn.

  Variable P:nat -> Prop.

  (** The stronger inductive hypothesis given in strong induction. The standard
  [nat ] induction principle provides only n = pred m, with [P 0] required
  separately. *)
  Hypothesis IH : forall m, (forall n, n < m -> P n) -> P m.

  Lemma P0 : P 0.
  Proof.
    apply IH; intros.
    exfalso; inversion H.
  Qed.

  Hint Resolve P0 : core.

  Lemma pred_increasing : forall (n m : nat),
      n <= m ->
      n.-1 <= m.-1.
  Proof. by elim => //= n IH'; case. Qed.

  Local Lemma strong_induction_all : forall n,
      (forall m, m <= n -> P m).
  Proof.
    elim => //=; first by case.
    move => n IH' m Hm.
    apply: IH.
    move => n' Hn'.
    apply: IH'.
    have Hnn: n < n.+1 by apply ltnSn.
    move: Hm.
    rewrite leq_eqVlt.
    move/orP.
    case.
    - move/eqP => Hm.
      by move: Hm Hn' =>->.
    - move => Hm.
      have Hmn: m <= n by [].
      suff Hsuff: n' < n.
        rewrite leq_eqVlt.
        apply/orP.
        by right.
      by apply: leq_trans; eauto.
  Qed.

  Theorem strong_induction_ltn : forall n, P n.
  Proof.
    eauto using strong_induction_all.
  Qed.

End StrongInductionLtn.

Section StrongInductionSub.

  Variable k : nat.

  Variable T : Type.

  Variable P : nat -> T -> Prop.

  Hypothesis IH : forall (v1 : nat) (h1 : T), (forall (v1a : nat) (h1a : T), k < v1a -> v1a - k < v1 - k -> P v1a h1a) -> P v1 h1.

  Theorem strong_induction_sub : forall n t, P n t.
  Proof.
    elim/strong_induction_ltn.
    move => m IH' t.
    apply IH.
    move => v1a h1a Hlt Hlt'.
    apply: IH'.
    rewrite ltn_subRL in Hlt'.
    rewrite subnKC in Hlt' => //.
    rewrite leq_eqVlt.
    by apply/orP; right.
  Qed.

End StrongInductionSub.