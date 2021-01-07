From Ordinal Require Import sflib Basics.
From Ordinal Require Export Ordinal.

Require Import PropExtensionality.

Set Implicit Arguments.
Set Primitive Projections.

Lemma from_acc_mon A (R0 R1: A -> A -> Prop) (INCL: forall a0 a1 (LE: R0 a0 a1), R1 a0 a1)
      a (ACC0: Acc R0 a) (ACC1: Acc R1 a)
  :
    Ord.le (Ord.from_acc ACC0) (Ord.from_acc ACC1).
Proof.
  dup ACC1. rename ACC2 into ACC. revert ACC0 ACC1. induction ACC.
  i. destruct ACC0, ACC1. ss. econs. i.
  destruct a1 as [a1 p1]. ss. exists (exist _ a1 (INCL _ _ p1)). ss.
  eapply H0; eauto.
Qed.

Lemma from_wf_mon A (R0 R1: A -> A -> Prop) (INCL: forall a0 a1 (LE: R0 a0 a1), R1 a0 a1)
      (WF0: well_founded R0) (WF1: well_founded R1) a
  :
    Ord.le (Ord.from_wf WF0 a) (Ord.from_wf WF1 a).
Proof.
  unfold Ord.from_wf. eapply from_acc_mon; eauto.
Qed.

Lemma from_wf_set_le A (R0 R1: A -> A -> Prop) (INCL: forall a0 a1 (LE: R0 a0 a1), R1 a0 a1)
      (WF0: well_founded R0) (WF1: well_founded R1)
  :
    Ord.le (Ord.from_wf_set WF0) (Ord.from_wf_set WF1).
Proof.
  econs. i. exists a0. eapply from_wf_mon; auto.
Qed.

Lemma from_wf_inj A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
      (WFA: well_founded RA) (WFB: well_founded RB)
      f
      (INJ: forall a0 a1 (LT: RA a0 a1), RB (f a0) (f a1))
  :
    forall a, Ord.le (Ord.from_wf WFA a) (Ord.from_wf WFB (f a)).
Proof.
  eapply (well_founded_induction WFA). i. eapply Ord.from_wf_supremum.
  i. dup LT. eapply H in LT. eapply Ord.le_lt_lt; eauto.
  eapply Ord.from_wf_lt; eauto.
Qed.

Lemma from_wf_set_inj A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
      (WFA: well_founded RA) (WFB: well_founded RB)
      f
      (INJ: forall a0 a1 (LT: RA a0 a1), RB (f a0) (f a1))
  :
    Ord.le (Ord.from_wf_set WFA) (Ord.from_wf_set WFB).
Proof.
  eapply Ord.build_supremum. i. eapply Ord.le_lt_lt.
  { eapply from_wf_inj; eauto. }
  eapply Ord.from_wf_set_upperbound.
Qed.

Definition projected_rel_rev A B (RB: B -> B -> Prop) (f: A -> B): A -> A -> Prop :=
  fun a0 a1 => RB (f a0) (f a1).

Lemma projected_rel_rev_well_founded A B (RB: B -> B -> Prop)
      (WFB: well_founded RB)
      (f: A -> B)
      (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
  :
    well_founded (projected_rel_rev RB f).
Proof.
  assert (forall b, forall a (LE: RB (f a) b), Acc (projected_rel_rev RB f) a).
  { eapply (well_founded_induction WFB (fun b => forall a (LE: RB (f a) b), Acc (projected_rel_rev RB f) a)).
    i. econs. i. unfold projected_rel_rev in H0. exploit H; eauto. }
  ii. econs. i. unfold projected_rel_rev in H0. eauto.
Qed.

Inductive projected_rel A B (RA: A -> A -> Prop) (f: A -> B): B -> B -> Prop :=
| projected_rel_intro
    a0 a1 (LT: RA a0 a1)
  :
    projected_rel RA f (f a0) (f a1)
.

Lemma inj_projected_rel_incl A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
      f
      (INJ: forall a0 a1 (LT: RA a0 a1), RB (f a0) (f a1))
  :
    forall b0 b1 (FLT: projected_rel RA f b0 b1), RB b0 b1.
Proof.
  i. inv FLT. eapply INJ; eauto.
Qed.

Lemma embed_projected_rel_well_founded A B (RA: A -> A -> Prop)
      (WFA: well_founded RA)
      (f: A -> B)
      (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
  :
    well_founded (projected_rel RA f).
Proof.
  assert (forall a, Acc (projected_rel RA f) (f a)).
  { eapply (well_founded_induction WFA). i.
    econs. i. inv H0. eapply INJ in H3. subst. eapply H; eauto. }
  ii. econs. i. inv H0. eapply H; eauto.
Qed.

Lemma inj_projected_rel_well_founded A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
      (WFA: well_founded RA) (WFB: well_founded RB)
      f
      (INJ: forall a0 a1 (LT: RA a0 a1), RB (f a0) (f a1))
  :
    well_founded (projected_rel RA f).
Proof.
  eapply wf_incl.
  { eapply inj_projected_rel_incl. eapply INJ. }
  { eauto. }
Qed.

Lemma from_wf_projected_rel_eq A B (RA: A -> A -> Prop)
      (WFA: well_founded RA)
      (f: A -> B)
      (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
  :
    forall a, Ord.eq (Ord.from_wf WFA a) (Ord.from_wf (embed_projected_rel_well_founded WFA f INJ) (f a)).
Proof.
  eapply (well_founded_induction WFA). i. split.
  - eapply Ord.from_wf_supremum. i. exploit H; eauto. i.
    eapply Ord.eq_lt_lt; eauto. eapply Ord.from_wf_lt.
    econs; eauto.
  - eapply Ord.from_wf_supremum. i. inv LT.
    eapply INJ in H2. subst. exploit H; eauto. i.
    symmetry in x0. eapply Ord.eq_lt_lt; eauto.
    eapply Ord.from_wf_lt; eauto.
Qed.

Lemma from_wf_set_projected_rel_le A B (RA: A -> A -> Prop)
      (WFA: well_founded RA)
      (f: A -> B)
      (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
  :
    Ord.le (Ord.from_wf_set WFA) (Ord.from_wf_set (embed_projected_rel_well_founded WFA f INJ)).
Proof.
  eapply Ord.build_supremum. i. eapply Ord.eq_lt_lt.
  { eapply from_wf_projected_rel_eq. }
  eapply Ord.build_upperbound.
Qed.

Definition to_projected_sig A B (f: A -> B) (a: A):
  @sig B (fun b => exists a, f a = b) :=
  (exist _ (f a) (ex_intro _ a eq_refl)).

Definition projected_rel_set A B (f: A -> B): Type :=
  @sig B (fun b => exists a, f a = b).

Inductive projected_rel_sig A B (RA: A -> A -> Prop) (f: A -> B):
  @sig B (fun b => exists a, f a = b) -> @sig B (fun b => exists a, f a = b) -> Prop :=
| projected_rel_sig_intro
    a0 a1 (LT: RA a0 a1)
  :
    projected_rel_sig RA f (to_projected_sig f a0) (to_projected_sig f a1)
.

Lemma projected_rel_sig_well_founded A B (RA: A -> A -> Prop)
      (WFA: well_founded RA)
      (f: A -> B)
      (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
  :
    well_founded (projected_rel_sig RA f).
Proof.
  assert (forall a, Acc (projected_rel_sig RA f) (to_projected_sig f a)).
  { eapply (well_founded_induction WFA). i.
    econs. i. inv H0. eapply INJ in H3. subst. eapply H; eauto. }
  ii. econs. i. inv H0. eapply H; eauto.
Qed.

Lemma from_wf_projected_rel_sig_eq A B (RA: A -> A -> Prop)
      (WFA: well_founded RA)
      (f: A -> B)
      (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
  :
    forall a, Ord.eq (Ord.from_wf WFA a) (Ord.from_wf (projected_rel_sig_well_founded WFA f INJ) (to_projected_sig f a)).
Proof.
  eapply (well_founded_induction WFA). i. split.
  - eapply Ord.from_wf_supremum. i. exploit H; eauto. i.
    eapply Ord.eq_lt_lt; eauto. eapply Ord.from_wf_lt.
    econs; eauto.
  - eapply Ord.from_wf_supremum. i. inv LT.
    eapply INJ in H2. subst. exploit H; eauto. i.
    symmetry in x0. eapply Ord.eq_lt_lt; eauto.
    eapply Ord.from_wf_lt; eauto.
Qed.

Lemma from_wf_set_projected_rel_sig_le A B (RA: A -> A -> Prop)
      (WFA: well_founded RA)
      (f: A -> B)
      (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
  :
    Ord.le (Ord.from_wf_set WFA) (Ord.from_wf_set (projected_rel_sig_well_founded WFA f INJ)).
Proof.
  eapply Ord.build_supremum. i. eapply Ord.eq_lt_lt.
  { eapply from_wf_projected_rel_sig_eq. }
  eapply Ord.build_upperbound.
Qed.

Lemma from_wf_set_projected_rel_sig_eq A B (RA: A -> A -> Prop)
      (WFA: well_founded RA)
      (f: A -> B)
      (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
  :
    Ord.eq (Ord.from_wf_set WFA) (Ord.from_wf_set (projected_rel_sig_well_founded WFA f INJ)).
Proof.
  split.
  - eapply from_wf_set_projected_rel_sig_le.
  - eapply Ord.build_supremum. i. destruct a. des. subst. eapply Ord.eq_lt_lt.
    { symmetry. eapply from_wf_projected_rel_sig_eq. }
    { eapply Ord.build_upperbound. }
Qed.

Definition cut_rel A (R: A -> A -> Prop) (a1: A):
  sig (fun a0 => R a0 a1) -> sig (fun a0 => R a0 a1) -> Prop :=
  fun a0 a1 => R (proj1_sig a0) (proj1_sig a1).

Lemma cut_rel_well_founded A (R: A -> A -> Prop)
      (WF: well_founded R)
      (a1: A)
  :
    well_founded (cut_rel R a1).
Proof.
  ii. destruct a as [a0 r]. revert a0 r.
  eapply (well_founded_induction
            WF
            (fun a0 => forall (r: R a0 a1), Acc (cut_rel R a1) (exist _ a0 r))).
  i. econs. i. destruct y as [a0 r0].
  unfold cut_rel in H0. ss. eapply H; auto.
Qed.

Lemma from_wf_cut A (R: A -> A -> Prop) (WF: well_founded R)
      (TOTAL: forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0)
      (a1: A):
  forall a0 (LT: R a0 a1),
    Ord.eq (Ord.from_wf WF a0) (Ord.from_wf (cut_rel_well_founded WF a1) (exist _ a0 LT)).
Proof.
  eapply (well_founded_induction
            WF
            (fun a0 => forall (LT: R a0 a1), Ord.eq (Ord.from_wf WF a0) (Ord.from_wf (cut_rel_well_founded WF a1) (exist _ a0 LT)))).
  intros a0 IH. i. split.
  { eapply Ord.from_wf_supremum. i.
    assert (LT1: R a2 a1).
    { destruct (TOTAL a2 a1) as [|[]]; auto.
      - subst. exfalso.
        eapply well_founded_irreflexive.
        { eapply clos_trans_well_founded; eauto. }
        { econs 2; eauto. econs 1; auto. }
      - exfalso.
        eapply well_founded_irreflexive.
        { eapply clos_trans_well_founded; eauto. }
        { econs 2; eauto. econs 2; eauto. econs 1; auto. }
    }
    eapply (@Ord.le_lt_lt (Ord.from_wf (cut_rel_well_founded WF a1)
                                       (exist _ a2 LT1))).
    { eapply IH; auto. }
    { eapply Ord.from_wf_lt. ss. }
  }
  { eapply Ord.from_wf_supremum. i. destruct a2 as [a2 LT1].
    unfold cut_rel in LT0. ss.
    eapply (@Ord.le_lt_lt (Ord.from_wf WF a2)).
    { eapply IH; auto. }
    { eapply Ord.from_wf_lt. ss. }
  }
Qed.


Lemma from_wf_set_cut A (R: A -> A -> Prop) (WF: well_founded R)
      (TOTAL: forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0)
      (a1: A):
  Ord.eq (Ord.from_wf WF a1) (Ord.from_wf_set (cut_rel_well_founded WF a1)).
Proof.
  split.
  { eapply Ord.from_wf_supremum. i.
    eapply Ord.lt_intro with (a:=exist _ a0 LT).
    eapply from_wf_cut; eauto. }
  { eapply Ord.build_supremum. intros [a0 r].
    eapply (@Ord.le_lt_lt (Ord.from_wf WF a0)).
    { eapply from_wf_cut; eauto. }
    { eapply Ord.from_wf_lt; eauto. }
  }
Qed.

Lemma cut_rel_total A (R: A -> A -> Prop)
      (TOTAL: forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0)
      (a: A)
  :
    forall a0 a1, cut_rel R a a0 a1 \/ a0 = a1 \/ cut_rel R a a1 a0.
Proof.
  ii. destruct a0, a1. unfold cut_rel. ss.
  destruct (TOTAL x x0)as [|[]]; auto. subst.
  right. left. f_equal. eapply proof_irrelevance.
Qed.
