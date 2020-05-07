Set Warnings "-parsing".
From mathcomp.ssreflect
Require Import all_ssreflect.
Set Warnings "parsing".

From Dynamic
Require Import NatExt Validator.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* Various set-theoretic properties that are used in the rest of the specs.   *)
(******************************************************************************)


Lemma setID_disjoint : forall (A B:{set Validator}),
  [disjoint (A :&: B) & (A :\: B)].
Proof.
  move=> A B.
  rewrite -setI_eq0 eqEsubset.
  apply/andP;split;apply/subsetP => x;last by rewrite in_set0.
  move/setIP=> [H1 H2].
  move/setIP: H1 => [_ H1].
  move/setDP: H2 => [_ H2].
  move/negP: H2 => H2.
  by contradiction.
Qed.

Lemma setDD_disjoint : forall (A B:{set Validator}),
  [disjoint (A :\: B) & (B :\: A)].
Proof.
  move=> A B.
  rewrite -setI_eq0 eqEsubset.
  apply/andP;split;apply/subsetP => x;last by rewrite in_set0.
  move/setIP=> [H1 H2].
  move/setDP: H1 => [H1a H1b].
  move/setDP: H2 => [H2a H2b].
  move/negP: H2b => H2b.
  by contradiction.
Qed.

Lemma setDDI_disjoint : forall (A B:{set Validator}),
  [disjoint A :\: B :|: B :\: A & A :&: B].
Proof. 
  move=> A B.
  rewrite -setI_eq0 eqEsubset.
  apply/andP;split;apply/subsetP => x;last by rewrite in_set0.
  move/setIP=> [H1 H2].
  move/setIP: H2 => [Hin1 Hin2].
  case/setUP: H1 => H;move/setDP: H => [_ Hnotin2];
    move/negP: Hnotin2 => Hnotin2;contradiction.
Qed.

Lemma setU_par : forall (A B:{set Validator}),
  A :|: B = (A :\: B) :|: (B :\: A) :|: (A :&: B).
Proof.
  move=> A B.
  apply/eqP.
  rewrite eqEsubset.
  apply/andP;split;apply/subsetP => x.
  case/setUP=> H.
  - rewrite -setUA setUC -setUA.
    apply/setUP;right. 
    by rewrite setUC -setDDr setDv setD0.
  - rewrite -setUA.
    apply/setUP;right.
    by rewrite setIC -setDDr setDv setD0.
  case/setUP=> H.
  - case/setUP: H => H.
    * move/setDP: H => [H _].
      by apply/setUP;left.
    * move/setDP: H => [H _].
      by apply/setUP;right.
  - move/setIP: H => [H _].
    by apply/setUP;left.
Qed.

Lemma setIs_disjoint : forall (A B C: {set Validator}),
  [disjoint A & B] -> [disjoint A & B :&: C].
Proof.
  move=> A B C.
  move/setDidPl=> <-.
  rewrite -setI_eq0 eqEsubset.
  apply/andP;split;apply/subsetP => x;last by rewrite in_set0.
  move/setIP=> [H1 H2].
  move/setDP: H1 => [_ H1].
  move/setIP: H2 => [H2 _].
  by move/negP: H1 => H1.
Qed.

Lemma setIID_disjoint : forall (A B C: {set Validator}),
  [disjoint (A :&: B) & (A :&: C :\: B)].
Proof.
  move=> A B C.
  rewrite setDIl.
  apply: setIs_disjoint.
  apply: setID_disjoint.
Qed.

Lemma setIIDD_disjoint : forall (A B C D: {set Validator}),
[disjoint A :&: B :|: A :&: C :\: B & B :&: D :\: A].
Proof.
  move=> A B C D.
  rewrite -setI_eq0 eqEsubset.
  apply/andP;split;apply/subsetP => x;last by rewrite in_set0.
  move/setIP=> [H1 H2].
  move/setUP: H1 => H1.
  move/setDP: H2 => [H2a H2b].
  case: H1.
  - move/setIP=> [H _]. by move/negP: H2b.
  - move/setDP=> [H _]. move/setIP: H => [H _]. by move/negP: H2b.
Qed.

Lemma setIIDD_subset : forall (A B C D: {set Validator}), 
  A \subset C ->
  B \subset D ->
  A :&: B :|: A :&: D :\: B :|: B :&: C :\: A \subset C :&: D.
Proof.
  move=> A B C D Ha Hb.
  move/subsetP:Ha => Ha.
  move/subsetP:Hb => Hb.
  apply/subsetP => x.
  case/setUP=> H.
  apply/setIP.
  - case/setUP: H => H.
    * move/setIP: H => [Hxa Hxb].
      by (apply Ha in Hxa;apply Hb in Hxb).
    * move/setDP: H => [Hxad _]. move/setIP: Hxad => [Hxa Hxd].
      by (apply Ha in Hxa).
  - move/setDP: H => [Hxbc _]. move/setIP: Hxbc => [Hxb Hxc].
    apply Hb in Hxb. by apply/setIP.
Qed.

Lemma setID2_disjoint : forall (A B C:{set Validator}),
  [disjoint (A :&: C) & (B :\: C)].
Proof.
  move=> A B C.
  rewrite -setI_eq0 eqEsubset.
  apply/andP;split;apply/subsetP => x;last by rewrite in_set0.
  move/setIP=> [H1 H2].
  move/setIP: H1 => [_ H1].  
  move/setDP: H2 => [_ H2].  
  by move/negP: H2 => H2.
Qed.

Lemma setID2_subset : forall (A B C:{set Validator}),
  A \subset B ->
  A \subset (A :&: C) :|: (B :\: C).
Proof.
  move=> A B C.
  move/subsetP => H.
  apply/subsetP => x.
  move=> Hs0.
  apply/setUP.
  have : (x \in C) || ~~(x \in C) by apply orbN.
  case/orP=> H'.
  - left. by apply/setIP.
  - right. apply H in Hs0. by apply/setDP.
Qed.

Lemma set3D_disjoint : forall (A B C:{set Validator}),
  [disjoint C :\: B & A :\: C].
Proof.
  move=> A B C.
  rewrite -setI_eq0 eqEsubset.
  apply/andP;split;apply/subsetP => x;last by rewrite in_set0.
  move/setIP=> [H1 H2].
  move/setDP: H1 => [H1a H1b].
  move/setDP: H2 => [H2a H2b].
  move/negP: H2b => H2b.
  by contradiction.
Qed.

Lemma set3D_subset : forall (A B C:{set Validator}),
  A :\: B \subset C :\: B :|: A :\: C.
Proof. 
  move=> A B C.
  apply/subsetP => x.
  move/setDP=> [H1 H2].  
  apply/setUP.
  have : (x \in C) || ~~(x \in C) by apply orbN.
  case/orP=> H.
  - left. by apply/setDP;split.
  - right. by apply/setDP;split.  
Qed.

