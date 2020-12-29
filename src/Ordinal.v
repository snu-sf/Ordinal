From Ordinal Require Import sflib Basics.

Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms. (* TODO: Use Morphisms *)

Set Implicit Arguments.
Set Primitive Projections.

Module Ord.
  Section TYPE.
  Let MyT := Type.
  Inductive t: Type :=
  | build (A: MyT) (os: A -> t)
  .

  Definition proj1 (o: t): MyT :=
    match o with
    | @build A _ => A
    end.

  Definition proj2 (o: t): proj1 o -> t :=
    match o with
    | @build _ os => os
    end.

  Inductive le: t -> t -> Prop :=
  | le_intro
      A0 A1 os0 os1
      (LE: forall (a0: A0), exists (a1: A1), le (os0 a0) (os1 a1))
    :
      le (build os0) (build os1)
  .

  Lemma le_induction (P: t -> t -> Prop)
        (IND: forall
            A0 A1 os0 os1
            (LE: forall (a0: A0), exists (a1: A1), le (os0 a0) (os1 a1) /\ P (os0 a0) (os1 a1)),
            P (build os0) (build os1)):
    forall o0 o1 (LE: le o0 o1), P o0 o1.
  Proof.
    fix IH 3. i. inv LE. eapply IND. i.
    hexploit (LE0 a0). i. des. specialize (IH _ _ H). eauto.
  Qed.

  Lemma le_proj (o0 o1: t) (a0: proj1 o0) (LE: le o0 o1):
    exists (a1: proj1 o1),
        le (proj2 o0 a0) (proj2 o1 a1).
  Proof.
    inv LE. eauto.
  Qed.

  Lemma le_proj_rev (o0 o1: t)
        (LE: forall (a0: proj1 o0), exists (a1: proj1 o1),
              le (proj2 o0 a0) (proj2 o1 a1)):
    le o0 o1.
  Proof.
    destruct o0, o1. econs; eauto.
  Qed.

  Lemma le_inv A0 A1 os0 os1 (a0: A0) (LE: le (@build A0 os0) (@build A1 os1)):
    exists (a1: A1), le (os0 a0) (os1 a1).
  Proof.
    eapply le_proj in LE. eauto.
  Qed.

  Lemma le_equivalent A0 A1 os0 os1:
    le (@build A0 os0) (@build A1 os1) <->
    (forall (a0: A0), exists (a1: A1), le (os0 a0) (os1 a1)).
  Proof.
    split.
    { i. eapply le_inv. auto. }
    { i. econs; eauto. }
  Qed.

  Variant lt: t -> t -> Prop :=
  | lt_intro
      o A os (a: A)
      (LE: le o (os a))
    :
      lt o (build os)
  .

  Lemma lt_proj (o0 o1: t) (LT: lt o0 o1):
    exists (a: proj1 o1), le o0 (proj2 o1 a).
  Proof.
    inv LT. eauto.
  Qed.

  Lemma lt_proj_rev (o0 o1: t)
        (LT: exists (a: proj1 o1), le o0 (proj2 o1 a)):
    lt o0 o1.
  Proof.
    destruct o1. des. econs; eauto.
  Qed.

  Lemma lt_inv o0 A1 os1 (LT: lt o0 (@build A1 os1)):
    exists (a: A1), le o0 (os1 a).
  Proof.
    eapply lt_proj in LT. eauto.
  Qed.

  Lemma lt_equivalent o0 A1 os1:
    lt o0 (@build A1 os1) <->
    exists (a: A1), le o0 (os1 a).
  Proof.
    split.
    { i. eapply lt_inv. auto. }
    { i. des. econs; eauto. }
  Qed.


  Section PLUMP.
    Lemma le_refl o: le o o.
    Proof.
      induction o. econs; eauto.
    Qed.

    Lemma le_trans o1 o0 o2 (LE0: le o0 o1) (LE1: le o1 o2): le o0 o2.
    Proof.
      revert o0 o1 LE0 LE1.
      induction o2. i. destruct o0, o1.
      rewrite le_equivalent in LE0. rewrite le_equivalent in LE1.
      econs. i. hexploit (LE0 a0); eauto. i. des.
      hexploit (LE1 a1); eauto. i. des. eauto.
    Qed.

    Global Program Instance le_PreOrder: PreOrder le.
    Next Obligation.
    Proof.
      ii. eapply le_refl.
    Qed.
    Next Obligation.
    Proof.
      ii. eapply (@le_trans y); eauto.
    Qed.

    Lemma lt_le o0 o1 (LT: lt o0 o1): le o0 o1.
    Proof.
      ginduction o1. i.
      eapply lt_inv in LT. des.
      destruct o0. destruct (os a) eqn:EQ.
      econs. i. eapply le_inv in LT. des.
      hexploit (H a (os0 a0)); eauto.
      rewrite EQ. econs; eauto.
    Qed.

    Lemma le_lt_lt o1 o0 o2 (LE: le o0 o1) (LT: lt o1 o2): lt o0 o2.
    Proof.
      inv LT. econs. etransitivity; eauto.
    Qed.

    Lemma lt_le_lt o1 o0 o2 (LT: lt o0 o1) (LE: le o1 o2): lt o0 o2.
    Proof.
      ginduction o2. i. inv LT.
      eapply (le_inv a) in LE. des. econs.
      etransitivity; eauto.
    Qed.

    Lemma lt_well_founded: well_founded lt.
    Proof.
      ii. cut (forall b (LE: le b a), Acc lt b).
      { i. eapply H. reflexivity. }
      induction a. i. econs. i. inv H0.
      eapply le_inv in LE. des.
      eapply H; eauto. etransitivity; eauto.
    Qed.

    Lemma lt_irreflexive o: ~ lt o o.
    Proof.
      ii. eapply (well_founded_induction lt_well_founded (fun o => ~ lt o o)); eauto.
    Qed.

    Lemma lt_trans o1 o0 o2 (LT0: lt o0 o1) (LT1: lt o1 o2): lt o0 o2.
    Proof.
      ii. eapply le_lt_lt; eauto. eapply lt_le; eauto.
    Qed.

    Global Program Instance lt_StrictOrder: StrictOrder lt.
    Next Obligation.
    Proof.
      ii. eapply lt_irreflexive. eauto.
    Qed.
    Next Obligation.
    Proof.
      ii. eapply lt_trans; eauto.
    Qed.

    Definition eq (o0 o1: t): Prop := le o0 o1 /\ le o1 o0.

    Lemma eq_refl o: eq o o.
    Proof.
      split; reflexivity.
    Qed.

    Lemma eq_sym o0 o1 (EQ: eq o0 o1): eq o1 o0.
    Proof.
      destruct EQ. split; auto.
    Qed.

    Lemma eq_trans o1 o0 o2 (EQ0: eq o0 o1) (EQ1: eq o1 o2): eq o0 o2.
    Proof.
      destruct EQ0, EQ1. split; etransitivity; eauto.
    Qed.

    Global Program Instance eq_Equivalence: Equivalence eq.
    Next Obligation.
    Proof.
      ii. eapply eq_refl.
    Qed.
    Next Obligation.
    Proof.
      ii. eapply eq_sym. auto.
    Qed.
    Next Obligation.
    Proof.
      ii. eapply (@eq_trans y); eauto.
    Qed.

    Global Program Instance le_PartialOrder: PartialOrder eq le.
    Next Obligation.
    Proof. ss. Qed.

    Lemma lt_not_le o0 o1 (LT: lt o0 o1) (LE: le o1 o0): False.
    Proof.
      eapply lt_StrictOrder. eapply le_lt_lt; eauto.
    Qed.

    Lemma lt_eq_lt o o0 o1 (EQ: eq o0 o1):
      lt o o0 <-> lt o o1.
    Proof.
      split; i.
      - destruct EQ. eapply lt_le_lt; eauto.
      - destruct EQ. eapply lt_le_lt; eauto.
    Qed.

    Lemma eq_lt_lt o o0 o1 (EQ: eq o0 o1):
      lt o0 o <-> lt o1 o.
    Proof.
      split; i.
      - destruct EQ. eapply le_lt_lt; eauto.
      - destruct EQ. eapply le_lt_lt; eauto.
    Qed.

    Lemma le_eq_le o o0 o1 (EQ: eq o0 o1):
      le o o0 <-> le o o1.
    Proof.
      split; i.
      - destruct EQ. etransitivity; eauto.
      - destruct EQ. etransitivity; eauto.
    Qed.

    Lemma eq_le_le o o0 o1 (EQ: eq o0 o1):
      le o0 o <-> le o1 o.
    Proof.
      split; i.
      - destruct EQ. etransitivity; eauto.
      - destruct EQ. etransitivity; eauto.
    Qed.
  End PLUMP.


  Section OPERATOR.
    Lemma build_upperbound A (os: A -> t): forall a, lt (os a) (build os).
    Proof.
      i. econs; eauto. reflexivity.
    Qed.

    Lemma build_spec A (os: A -> t) o (UB: forall a, lt (os a) o):
      le (build os) o.
    Proof.
      destruct o. econs. i.
      specialize (UB a0). eapply lt_inv in UB. des. eauto.
    Qed.

    Definition is_O (o0: t): Prop := forall o1, le o0 o1.

    Record is_S (o0 o1: t): Prop :=
      is_S_mk {
          is_S_lt: lt o0 o1;
          is_S_spec: forall o (LT: lt o0 o), le o1 o;
        }.

    Record is_join A (os: A -> t) o1: Prop :=
      is_join_mk {
          is_join_upperbound: forall a, le (os a) o1;
          is_join_supremum: forall o (LE: forall a, le (os a) o), le o1 o;
        }.

    Definition open A (os: A -> t): Prop :=
      forall a0, exists a1, lt (os a0) (os a1).

    Lemma eq_is_O o0 o1 (ZERO0: is_O o0) (EQ: eq o0 o1):
      is_O o1.
    Proof.
      ii. symmetry in EQ. eapply eq_le_le; eauto.
    Qed.

    Lemma is_O_unique o0 o1 (ZERO0: is_O o0) (ZERO1: is_O o1): eq o0 o1.
    Proof.
      split.
      - eapply ZERO0.
      - eapply ZERO1.
    Qed.

    Lemma eq_is_S o s0 s1 (SUCC: is_S o s0) (EQ: eq s0 s1):
      is_S o s1.
    Proof.
      econs.
      - eapply (@lt_le_lt s0).
        + eapply SUCC.
        + eapply EQ.
      - i. transitivity s0.
        + eapply EQ.
        + eapply SUCC; auto.
    Qed.

    Lemma is_S_unique o s0 s1 (SUCC0: is_S o s0) (SUCC1: is_S o s1):
      eq s0 s1.
    Proof.
      split.
      - eapply SUCC0. eapply SUCC1.
      - eapply SUCC1. eapply SUCC0.
    Qed.

    Lemma eq_is_join A (os: A -> t) o0 o1 (JOIN: is_join os o0) (EQ: eq o0 o1):
      is_join os o1.
    Proof.
      econs.
      - i. transitivity o0.
        + eapply JOIN.
        + eapply EQ.
      - i. transitivity o0.
        + eapply EQ.
        + eapply JOIN. auto.
    Qed.

    Lemma is_join_unique A (os: A -> t) o0 o1 (JOIN0: is_join os o0) (JOIN1: is_join os o1):
      eq o0 o1.
    Proof.
      split.
      - eapply JOIN0. eapply JOIN1.
      - eapply JOIN1. eapply JOIN0.
    Qed.

    Definition O: t := build (False_rect _).

    Lemma O_bot o: le O o.
    Proof.
      destruct o. econs. i. ss.
    Qed.

    Lemma O_is_O: is_O O.
    Proof.
      ii. eapply O_bot.
    Qed.

    Definition S (o: t): t := build (unit_rect _ o).

    Lemma S_lt o: lt o (S o).
    Proof.
      eapply (build_upperbound (unit_rect _ o) tt).
    Qed.

    Lemma S_le o:
      le o (S o).
    Proof.
      eapply lt_le. eapply S_lt.
    Qed.

    Lemma S_spec o0 o1 (LT: lt o0 o1):
      le (S o0) o1.
    Proof.
      eapply build_spec. ii. destruct a. ss.
    Qed.

    Lemma S_is_S o: is_S o (S o).
    Proof.
      econs.
      - eapply S_lt.
      - eapply S_spec.
    Qed.

    Lemma le_S o0 o1 (LE: le o0 o1):
      le (S o0) (S o1).
    Proof.
      eapply S_spec. eapply le_lt_lt; eauto. eapply S_lt.
    Qed.

    Lemma le_S_rev o0 o1 (LE: le (S o0) (S o1)):
      le o0 o1.
    Proof.
      eapply (le_inv tt) in LE. des. destruct a1. ss.
    Qed.

    Lemma lt_S o0 o1 (LT: lt o0 o1):
      lt (S o0) (S o1).
    Proof.
      eapply lt_intro with (a:=tt). ss. destruct o1. econs.
      i. destruct a0. ss. eapply lt_inv in LT. auto.
    Qed.

    Lemma lt_S_rev o0 o1 (LT: lt (S o0) (S o1)):
      lt o0 o1.
    Proof.
      eapply lt_inv in LT. des. destruct a. ss.
      destruct o1. eapply (le_inv tt) in LT. des.
      eapply lt_intro with (a:=a1). ss.
    Qed.

    Lemma eq_S o0 o1 (EQ: eq o0 o1):
      eq (S o0) (S o1).
    Proof.
      split.
      - eapply le_S. apply EQ.
      - eapply le_S. apply EQ.
    Qed.

    Lemma eq_S_rev o0 o1 (EQ: eq (S o0) (S o1)):
      eq o0 o1.
    Proof.
      split.
      - apply le_S_rev. apply EQ.
      - apply le_S_rev. apply EQ.
    Qed.

    Lemma S_pos o: lt O (S o).
    Proof.
      eapply le_lt_lt.
      { eapply O_bot. }
      { eapply S_lt. }
    Qed.

    Definition join (A: MyT) (os: A -> t): t :=
      @build
        (@sigT _ (fun a => proj1 (os a)))
        (fun aT => proj2 (os (projT1 aT)) (projT2 aT)).

    Lemma join_upperbound (A: MyT) (os: A -> t):
      forall a, le (os a) (join os).
    Proof.
      ii. eapply le_proj_rev. i.
      exists (existT _ a a0). reflexivity.
    Qed.

    Lemma join_supremum (A: MyT) (os: A -> t)
          o (LE: forall a, le (os a) o):
      le (join os) o.
    Proof.
      destruct o. econs. i. specialize (LE (projT1 a0)).
      eapply (le_proj (projT2 a0)) in LE. eauto.
    Qed.

    Lemma le_join A0 A1 (os0: A0 -> t) (os1: A1 -> t)
          (LE: forall a0, exists a1, le (os0 a0) (os1 a1))
      :
        le (join os0) (join os1).
    Proof.
      eapply join_supremum. i. specialize (LE a). des.
      etransitivity; eauto. eapply join_upperbound.
    Qed.

    Lemma le_join_same A (os0 os1: A -> t) (LE: forall a, le (os0 a) (os1 a)):
      le (join os0) (join os1).
    Proof.
      eapply le_join. i. exists a0. auto.
    Qed.

    Lemma eq_join A (os0 os1: A -> t) (LE: forall a, eq (os0 a) (os1 a)):
      eq (join os0) (join os1).
    Proof.
      split; apply le_join_same; i; eapply LE.
    Qed.

    Lemma join_is_join A (os: A -> t):
      is_join os (join os).
    Proof.
      econs.
      - eapply join_upperbound.
      - eapply join_supremum.
    Qed.

    Lemma build_is_join A (os: A -> t) (OPEN: open os): is_join os (build os).
    Proof.
      econs.
      - i. eapply lt_le. eapply build_upperbound.
      - i. eapply build_spec. i. specialize (OPEN a). des.
        eapply lt_le_lt; eauto.
    Qed.

    Lemma build_join A (os: A -> t) (OPEN: open os): eq (build os) (join os).
    Proof.
      eapply is_join_unique.
      { eapply build_is_join. auto. }
      { eapply join_is_join. }
    Qed.

    Lemma build_is_join_S A (os: A -> t):
      is_join (fun a => S (os a)) (build os).
    Proof.
      econs.
      { i. eapply S_spec. eapply build_upperbound. }
      { i. eapply build_spec. i. eapply (@lt_le_lt (S (os a))); auto. eapply S_lt. }
    Qed.

    Lemma build_join_S A (os: A -> t):
      eq (build os) (join (fun a => S (os a))).
    Proof.
      eapply is_join_unique.
      { eapply build_is_join_S. }
      { eapply join_is_join. }
    Qed.

    Definition union (o0 o1: t): t := @join bool (fun b: bool => if b then o0 else o1).

    Lemma union_l o0 o1: le o0 (union o0 o1).
    Proof.
      eapply (@join_upperbound _ (fun b: bool => if b then o0 else o1) true).
    Qed.

    Lemma union_r o0 o1: le o1 (union o0 o1).
    Proof.
      eapply (@join_upperbound _ (fun b: bool => if b then o0 else o1) false).
    Qed.

    Lemma union_spec o0 o1 o (LE0: le o0 o) (LE1: le o1 o):
      le (union o0 o1) o.
    Proof.
      eapply join_supremum. i. destruct a; ss.
    Qed.

    Lemma union_comm o0 o1: eq (union o0 o1) (union o1 o0).
    Proof.
      split.
      - eapply union_spec.
        + eapply union_r.
        + eapply union_l.
      - eapply union_spec.
        + eapply union_r.
        + eapply union_l.
    Qed.

    Lemma union_max o0 o1 (LE: le o0 o1): eq (union o0 o1) o1.
    Proof.
      split.
      - eapply union_spec.
        + auto.
        + reflexivity.
      - eapply union_r.
    Qed.

    Lemma le_union o0 o1 o2 o3 (LE0: le o0 o1) (LE1: le o2 o3):
      le (union o0 o2) (union o1 o3).
    Proof.
      eapply union_spec.
      - transitivity o1; auto. eapply union_l.
      - transitivity o3; auto. eapply union_r.
    Qed.

    Lemma eq_union o0 o1 o2 o3 (EQ0: eq o0 o1) (EQ1: eq o2 o3):
      eq (union o0 o2) (union o1 o3).
    Proof.
      split.
      - eapply le_union.
        + eapply EQ0.
        + eapply EQ1.
      - eapply le_union.
        + eapply EQ0.
        + eapply EQ1.
    Qed.

    Lemma union_assoc o0 o1 o2:
      eq (union o0 (union o1 o2)) (union (union o0 o1) o2).
    Proof.
      split.
      - eapply union_spec.
        + transitivity (union o0 o1).
          * eapply union_l.
          * eapply union_l.
        + eapply union_spec.
          * transitivity (union o0 o1).
            { eapply union_r. }
            { eapply union_l. }
          * eapply union_r.
      - eapply union_spec.
        + eapply union_spec.
          * eapply union_l.
          * transitivity (union o1 o2).
            { eapply union_l. }
            { eapply union_r. }
        + transitivity (union o1 o2).
          { eapply union_r. }
          { eapply union_r. }
    Qed.

    Lemma limit_S_disjoint o o0 A (os: A -> t)
          (SUCC: is_S o0 o)
          (JOIN: is_join os o)
          (OPEN: open os)
      :
        False.
    Proof.
      hexploit (JOIN.(is_join_supremum)).
      { instantiate (1:=o0).
        i. specialize (OPEN a). des.
        hexploit lt_le_lt.
        { eapply OPEN. }
        { eapply JOIN. }
        i. eapply le_S_rev.
        transitivity (os a1).
        { eapply S_spec. auto. }
        eapply le_eq_le.
        { eapply is_S_unique; eauto. eapply S_is_S. }
        eapply JOIN.
      }
      i. eapply (@lt_not_le o0 o); auto. eapply SUCC.(is_S_lt).
    Qed.
  End OPERATOR.


  Section FROMWF.
    Program Fixpoint from_acc A (R: A -> A -> Prop) (a1: A) (ACC: Acc R a1): t :=
      @build (sig (fun a0 => R a0 a1)) (fun a0p =>
                                          @from_acc _ R (proj1_sig a0p) _).
    Next Obligation.
      inv ACC. eapply H0; eauto.
    Defined.
    Arguments from_acc [A R] a1 ACC.

    Lemma same_acc_le A (R: A -> A -> Prop) (a: A) (ACC0 ACC1: Acc R a):
      le (from_acc a ACC0) (from_acc a ACC1).
    Proof.
      generalize ACC0. i. revert ACC1 ACC2. induction ACC0.
      i. destruct ACC1, ACC2. ss. econs. i.
      exists a1. eapply H0. eapply (proj2_sig a1).
    Qed.

    Lemma same_acc_eq A (R: A -> A -> Prop) (a: A) (ACC0 ACC1: Acc R a):
      eq (from_acc a ACC0) (from_acc a ACC1).
    Proof.
      split.
      - eapply same_acc_le.
      - eapply same_acc_le.
    Qed.

    Lemma from_acc_lt A (R: A -> A -> Prop) (a0 a1: A) (LT: R a0 a1)
          (ACC1: Acc R a1) (ACC0: Acc R a0)
      :
        lt (from_acc a0 ACC0) (from_acc a1 ACC1).
    Proof.
      destruct ACC1. ss.
      set (exist (fun a0 => R a0 a1) a0 LT).
      eapply le_lt_lt.
      2: { eapply (build_upperbound (fun a0p => from_acc (proj1_sig a0p) (from_acc_obligation_1 (Acc_intro a1 a) a0p)) s). }
      eapply same_acc_eq.
    Qed.

    Definition from_wf A (R: A -> A -> Prop) (WF: well_founded R) (a1: A): t :=
      from_acc a1 (WF a1).

    Lemma from_wf_lt A (R: A -> A -> Prop) (WF: well_founded R) (a0 a1: A) (LT: R a0 a1)
      :
        lt (from_wf WF a0) (from_wf WF a1).
    Proof.
      eapply from_acc_lt; eauto.
    Qed.

    Lemma same_wf_le A (R: A -> A -> Prop) (a: A) (WF0 WF1: well_founded R):
      le (from_wf WF0 a) (from_wf WF1 a).
    Proof.
      eapply same_acc_le.
    Qed.

    Lemma same_wf_eq A (R: A -> A -> Prop) (a: A) (WF0 WF1: well_founded R):
      eq (from_wf WF0 a) (from_wf WF1 a).
    Proof.
      eapply same_acc_eq.
    Qed.

    Lemma from_wf_supremum A (R: A -> A -> Prop) (WF: well_founded R) o a1
          (LE: forall a0 (LT: R a0 a1), lt (from_wf WF a0) o)
      :
        le (from_wf WF a1) o.
    Proof.
      unfold from_wf. destruct (WF a1). ss.
      eapply build_spec. i. destruct a0 as [a0 r]. ss.
      specialize (LE a0 r). unfold from_wf in LE.
      eapply le_lt_lt; [|eapply LE].
      eapply same_acc_le.
    Qed.

    Definition from_wf_set A (R: A -> A -> Prop) (WF: well_founded R): t :=
      @build A (from_wf WF).

    Lemma from_wf_set_upperbound A (R: A -> A -> Prop) (WF: well_founded R) a:
      lt (from_wf WF a) (from_wf_set WF).
    Proof.
      eapply build_upperbound.
    Qed.

    Lemma same_wf_set_le A (R: A -> A -> Prop) (WF0 WF1: well_founded R):
      le (from_wf_set WF0) (from_wf_set WF1).
    Proof.
      econs. i. exists a0. eapply same_wf_le.
    Qed.

    Lemma same_wf_set_eq A (R: A -> A -> Prop) (WF0 WF1: well_founded R):
      eq (from_wf_set WF0) (from_wf_set WF1).
    Proof.
      split; eapply same_wf_set_le.
    Qed.
  End FROMWF.


  Section REC.
    Variable D: Type.
    Variable base: D.
    Variable next: D -> D.
    Variable djoin: forall (A: MyT) (ds: A -> D), D.

    Let dunion (d0 d1: D): D := djoin (fun b: bool => if b then d0 else d1).

    Fixpoint rec (o: t): D :=
      match o with
      | @build X os =>
        dunion base (djoin (fun x => next (rec (os x))))
      end.

    Variable dle: D -> D -> Prop.
    Variable wf: D -> Prop.

    Let deq: D -> D -> Prop :=
      fun d0 d1 => dle d0 d1 /\ dle d1 d0.

    Hypothesis dle_reflexive: forall d (WF: wf d), dle d d.
    Hypothesis dle_transitive: forall d1 d0 d2 (WF0: wf d0) (WF1: wf d1) (WF2: wf d2) (LE0: dle d0 d1) (LE1: dle d1 d2),
        dle d0 d2.

    Hypothesis djoin_upperbound: forall A (ds: A -> D) (a: A) (WF: forall a, wf (ds a)), dle (ds a) (djoin ds).
    Hypothesis djoin_supremum: forall A (ds: A -> D) (d: D) (WF: forall a, wf (ds a)) (WFD: wf d) (LE: forall a, dle (ds a) d), dle (djoin ds) d.
    Hypothesis djoin_wf: forall A (ds: A -> D) (WF: forall a, wf (ds a)), wf (djoin ds).

    Hypothesis base_wf: wf base.
    Hypothesis next_wf: forall d (WF: wf d), wf (next d).

    Hypothesis next_le: forall d (WF: wf d), dle d (next d).
    Hypothesis next_mon: forall d0 d1 (WF0: wf d0) (WF1: wf d1) (LE: dle d0 d1), dle (next d0) (next d1).

    Let rec_all (o1: t):
      (forall o0 (LE: le o0 o1), dle (rec o0) (rec o1)) /\
      (forall o0 (LT: lt o0 o1), dle (next (rec o0)) (rec o1)) /\
      (wf (rec o1)) /\
      (dle base (rec o1))
    .
    Proof.
      revert o1.
      eapply (well_founded_induction lt_well_founded); auto.
      intros o1 IH. destruct o1. ss.

      assert (IHS0:
                forall
                  A0 (os0: A0 -> t)
                  (LE: forall a0, exists a, le (os0 a0) (os a))
                  a0,
                  (forall o0 (LE: le o0 (os0 a0)), dle (rec o0) (rec (os0 a0))) /\
                  (forall o0 (LT: lt o0 (os0 a0)), dle (next (rec o0)) (rec (os0 a0))) /\
                  wf (rec (os0 a0)) /\ dle base (rec (os0 a0))).
      { i. eapply IH. hexploit (LE a0); eauto. i. des. econs; eauto. }
      assert (WF0:
                forall
                  A0 (os0: A0 -> t)
                  (LE: forall a0, exists a, le (os0 a0) (os a))
                  a,
                  wf (next (rec (os0 a)))).
      { i. eapply next_wf. eapply IHS0; eauto. }
      assert (WFU0:
                forall
                  A0 (os0: A0 -> t)
                  (LE: forall a0, exists a, le (os0 a0) (os a))
                  (b: bool),
                  wf (if b then base else djoin (fun x => next (rec (os0 x))))).
      { i. destruct b; auto. }
      assert (REFL: forall a0, exists a1, le (os a0) (os a1)).
      { i. exists a0. reflexivity. }

      assert ((forall o0 (LE: le o0 (build os)), dle (rec o0) (dunion base (djoin (fun x => next (rec (os x)))))) /\
              wf (dunion base (djoin (fun x => next (rec (os x))))) /\ dle base (dunion base (djoin (fun x => next (rec (os x)))))).
      { splits.
        - i. destruct o0. erewrite le_equivalent in LE. ss.
          eapply djoin_supremum; eauto.
          i. destruct a.
          + unfold dunion.
            eapply (@djoin_upperbound _ (fun b: bool => if b then base else djoin (fun x => next (rec (os x)))) true); auto.
          + eapply (@dle_transitive (djoin (fun x => next (rec (os x))))); eauto.
            * eapply djoin_supremum; eauto. i. hexploit (LE a); eauto. i. des.
              eapply IHS0 in H; eauto.
              eapply (@dle_transitive (next (rec (os a1)))); eauto.
              { eapply next_mon; eauto.
                { eapply IHS0; eauto. }
                { eapply IHS0; eauto. }
              }
              { eapply (@djoin_upperbound _ (fun x => next (rec (os x))) a1); eauto. }
            * eapply (@djoin_upperbound _  (fun b: bool => if b then base else djoin (fun x => next (rec (os x)))) false); auto.
        - eapply djoin_wf; eauto.
        - eapply (@djoin_upperbound _  (fun b: bool => if b then base else djoin (fun x => next (rec (os x)))) true); auto.
      }

      destruct H as [RECLE [WF BASE]]. splits; auto. i.
      { dup LT. eapply lt_inv in LT. des.
        eapply (@dle_transitive (next (rec (os a)))); eauto.
        { eapply next_wf. eapply IH; eauto. }
        { eapply next_mon; eauto.
          { eapply IH; eauto. }
          { eapply IH; eauto. eapply build_upperbound. }
          { eapply IH; eauto. eapply build_upperbound. }
        }
        eapply (@dle_transitive (djoin (fun x => next (rec (os x))))); eauto.
        { eapply (djoin_upperbound (fun x => next (rec (os x)))); eauto. }
        { eapply (djoin_upperbound (fun b: bool => if b then base else djoin (fun x => next (rec (os x)))) false); eauto. }
      }
    Qed.

    Lemma le_rec (o0 o1: t) (LE: le o0 o1): dle (rec o0) (rec o1).
    Proof.
      eapply rec_all; auto.
    Qed.

    Lemma eq_rec (o0 o1: t) (EQ: eq o0 o1): deq (rec o0) (rec o1).
    Proof.
      split.
      - eapply le_rec. eapply EQ.
      - eapply le_rec. eapply EQ.
    Qed.

    Lemma lt_rec (o0 o1: t) (LT: lt o0 o1): dle (next (rec o0)) (rec o1).
    Proof.
      eapply rec_all; auto.
    Qed.

    Lemma rec_le_base o: dle base (rec o).
    Proof.
      eapply rec_all.
    Qed.

    Lemma rec_wf o: wf (rec o).
    Proof.
      eapply rec_all.
    Qed.

    Let RECWF:= rec_wf.

    Lemma rec_next_le (o0 o1: t) (LE: le o0 o1): dle (next (rec o0)) (next (rec o1)).
    Proof.
      eapply next_mon; eauto. eapply le_rec; auto.
    Qed.

    Let wf_helper X (xs: X -> t)
      :
        forall x, wf (next (rec (xs x))).
    Proof.
      i. auto.
    Qed.

    Let wfu_helper X (xs: X -> t)
      :
        forall (b: bool),
          wf (if b then base else djoin (fun x => next (rec (xs x)))).
    Proof.
      i. destruct b; auto.
    Qed.

    Lemma rec_O: deq (rec O) base.
    Proof.
      ss. split.
      - eapply djoin_supremum; auto. i. destruct a; auto.
        eapply djoin_supremum; auto. ss.
      - eapply (@djoin_upperbound _ (fun b: bool => if b then base else djoin (fun x => next (rec (@False_rect _ _)))) true); auto.
    Qed.

    Lemma rec_is_O o (ZERO: is_O o): deq (rec o) base.
    Proof.
      hexploit (@eq_rec O o).
      { eapply is_O_unique; auto. eapply O_is_O. }
      i. inv H. split.
      - eapply (@dle_transitive (rec O)); auto. eapply rec_O.
      - eapply (@dle_transitive (rec O)); auto. eapply rec_O.
    Qed.

    Lemma rec_S o: deq (rec (S o)) (next (rec o)).
    Proof.
      ss. split.
      - eapply djoin_supremum; auto. i. destruct a.
        + eapply (@dle_transitive (rec o)); auto. eapply rec_le_base.
        + eapply djoin_supremum; auto. i. destruct a. ss.
          eapply rec_next_le. reflexivity.
      - eapply (@dle_transitive (djoin (fun x => next (rec (unit_rect (fun _ : unit => t) o x))))); auto.
        { eapply djoin_wf; auto. }
        + eapply (djoin_upperbound (fun x : unit => next (rec (unit_rect (fun _ : unit => t) o x))) tt); auto.
        + eapply (@djoin_upperbound _ (fun b: bool => if b then base else djoin (fun x => next (rec (unit_rect (fun _ : unit => t) o x)))) false); auto.
    Qed.

    Lemma rec_is_S o s (SUCC: is_S o s): deq (rec s) (next (rec o)).
    Proof.
      hexploit (@eq_rec (S o) s).
      { eapply is_S_unique; eauto. eapply S_is_S. }
      i. inv H. split.
      - eapply (@dle_transitive (rec (S o))); auto. eapply rec_S.
      - eapply (@dle_transitive (rec (S o))); auto. eapply rec_S.
    Qed.

    Lemma rec_build A (os: A -> t)
          (INHABITED: inhabited A) (OPEN: open os)
      : deq (rec (build os)) (djoin (fun a => rec (os a))).
    Proof.
      destruct INHABITED as [a'].
      split; ss.
      - eapply djoin_supremum; auto. i. destruct a; auto.
        + eapply (@dle_transitive (rec (os a'))); auto.
          * eapply rec_le_base.
          * eapply (@djoin_upperbound _ (fun a : A => rec (os a)) a'); auto.
        + eapply djoin_supremum; auto. i.
          hexploit (OPEN a). i. des.
          eapply lt_rec in H; auto.
          eapply (@dle_transitive (rec (os a1))); auto.
          eapply (@djoin_upperbound _ (fun a0 : A => rec (os a0)) a1); auto.
      - eapply djoin_supremum; auto.
        { eapply djoin_wf; eauto. } i.
        eapply (@dle_transitive (djoin (fun x : A => next (rec (os x))))); auto.
        { eapply djoin_wf; auto. }
        eapply (@dle_transitive (next (rec (os a)))); auto.
        + eapply (@djoin_upperbound _ (fun a : A => next (rec (os a))) a); auto.
        + eapply (@djoin_upperbound _ (fun b: bool => if b then base else (djoin (fun a : A => next (rec (os a))))) false); auto.
    Qed.

    Lemma rec_red A (os: A -> t):
      rec (build os) = dunion base (djoin (fun a => next (rec (os a)))).
    Proof.
      ss.
    Qed.

    Lemma rec_join A (os: A -> t)
      : deq (rec (join os)) (dunion base (djoin (fun a => rec (os a)))).
    Proof.
      split.
      - ss. eapply djoin_supremum.
        { i. destruct a; auto. }
        { eapply djoin_wf; auto. destruct a; auto. }
        { i. destruct a; auto.
          { eapply (@djoin_upperbound _ (fun b: bool => if b then base else (djoin (fun a : A => rec (os a)))) true).
            i. destruct a; auto. }
          { eapply (@dle_transitive (djoin (fun a : A => rec (os a)))); auto.
            { eapply djoin_wf; auto. i. destruct a; auto. }
            { eapply djoin_supremum; auto. i.
              destruct a; ss. destruct (os x) eqn:EQ; auto.
              eapply (@dle_transitive (rec (build os0))); auto.
              { eapply (@dle_transitive (rec (S (os0 p)))); auto.
                { eapply rec_S. }
                { eapply le_rec. eapply S_spec. eapply build_upperbound. }
              }
              { rewrite <- EQ.
                eapply (@djoin_upperbound _ (fun a => rec (os a))); auto. }
            }
            { eapply (@djoin_upperbound _ (fun b: bool => if b then base else (djoin (fun a : A => rec (os a)))) false).
              i. destruct a; auto. }
          }
        }
      - eapply djoin_supremum; auto.
        { i. destruct a; auto. }
        { i. destruct a; auto.
          { eapply rec_le_base. }
          { eapply djoin_supremum; auto.
            i. eapply le_rec. eapply join_upperbound. }
        }
    Qed.

    Lemma rec_join_inhabited A (os: A -> t) (INHABITED: inhabited A)
      : deq (rec (join os)) (djoin (fun a => rec (os a))).
    Proof.
      split.
      { eapply (@dle_transitive (dunion base (djoin (fun a => rec (os a))))); auto.
        { eapply djoin_wf; auto. i. destruct a; auto. }
        { eapply rec_join. }
        { eapply djoin_supremum; auto.
          { i. destruct a; auto. }
          { i. destruct a; auto. inv INHABITED.
            eapply (@dle_transitive (rec (os X))); auto.
            { eapply rec_le_base. }
            { eapply (@djoin_upperbound _ (fun a : A => rec (os a)) X); auto. }
          }
        }
      }
      { eapply (@dle_transitive (dunion base (djoin (fun a => rec (os a))))); auto.
        { eapply djoin_wf; auto. i. destruct a; auto. }
        { eapply djoin_supremum; auto.
          { eapply djoin_wf; auto. i. destruct a; auto. }
          { i. eapply (@dle_transitive (djoin (fun a0 : A => rec (os a0)))); auto.
            { eapply djoin_wf; auto. i. destruct a0; auto. }
            { eapply (@djoin_upperbound _ (fun a0 : A => rec (os a0)) a); auto. }
            { eapply (@djoin_upperbound _ (fun b: bool => if b then base else (djoin (fun a0 : A => rec (os a0)))) false).
              i. destruct a0; auto. }
          }
        }
        { eapply rec_join. }
      }
    Qed.

    Lemma rec_is_join A (os: A -> t) o (JOIN: is_join os o)
      : deq (rec o) (dunion base (djoin (fun a => rec (os a)))).
    Proof.
      hexploit (@eq_rec (join os) o).
      { eapply is_join_unique; eauto. eapply join_is_join; auto. }
      i. inv H. split.
      - eapply (@dle_transitive (rec (join os))); auto.
        { eapply djoin_wf. i. destruct a; auto. }
        { eapply rec_join; auto. }
      - eapply (@dle_transitive (rec (join os))); auto.
        { eapply djoin_wf. i. destruct a; auto. }
        { eapply rec_join; auto. }
    Qed.

    Lemma rec_is_join_inhabited A (os: A -> t) o
          (INHABITED: inhabited A) (JOIN: is_join os o)
      : deq (rec o) (djoin (fun a => rec (os a))).
    Proof.
      hexploit (@eq_rec (join os) o).
      { eapply is_join_unique; eauto. eapply join_is_join; auto. }
      i. inv H. split.
      - eapply (@dle_transitive (rec (join os))); auto.
        { eapply rec_join_inhabited; auto. }
      - eapply (@dle_transitive (rec (join os))); auto.
        { eapply rec_join_inhabited; auto. }
    Qed.

    Lemma rec_union o0 o1
      : deq (rec (union o0 o1)) (dunion (rec o0) (rec o1)).
    Proof.
      assert (INHABITED: inhabited bool).
      { constructor. exact true. }
      split.
      { eapply (@dle_transitive (djoin (fun a : bool => rec ((fun b : bool => if b then o0 else o1) a)))); auto.
        { eapply djoin_wf; auto. i. destruct a; auto. }
        { eapply rec_join_inhabited; auto. }
        { eapply djoin_supremum.
          { i. destruct a; auto. }
          { eapply djoin_wf; auto. i. destruct a; auto. }
          { i. destruct a; auto.
            { eapply (@djoin_upperbound _ (fun b: bool => if b then (rec o0) else (rec o1)) true).
              i. destruct a; auto. }
            { eapply (@djoin_upperbound _ (fun b: bool => if b then (rec o0) else (rec o1)) false).
              i. destruct a; auto. }
          }
        }
      }
      { eapply (@dle_transitive (djoin (fun a : bool => rec ((fun b : bool => if b then o0 else o1) a)))); auto.
        { eapply djoin_wf; auto. i. destruct a; auto. }
        { eapply djoin_supremum.
          { i. destruct a; auto. }
          { eapply djoin_wf; auto. }
          { i. destruct a; auto.
            { eapply (@djoin_upperbound _ (fun b: bool => rec (if b then o0 else o1)) true).
              i. destruct a; auto. }
            { eapply (@djoin_upperbound _ (fun b: bool => rec (if b then o0 else o1)) false).
              i. destruct a; auto. }
          }
        }
        { eapply rec_join_inhabited; auto. }
      }
    Qed.

    Lemma rec_unique (f: t -> D)
          (RED: forall A (os: A -> t),
              deq (f (build os)) (dunion base (djoin (fun a => next (f (os a))))))
          (WF: forall o, wf (f o))
      :
        forall o, deq (f o) (rec o).
    Proof.
      induction o.
      assert (WFU0: wf (dunion base (djoin (fun a : A => next (f (os a)))))).
      { eapply djoin_wf; auto. i. destruct a; auto. }
      assert (WFU1: wf (dunion base (djoin (fun a : A => next (rec (os a)))))).
      { eapply djoin_wf; auto. }
      split.
      - apply (@dle_transitive (dunion base (djoin (fun a => next (f (os a)))))); auto; auto.
        + apply RED.
        + ss. apply djoin_supremum; auto.
          { i. destruct a; auto. }
          i. destruct a; auto.
          { eapply (@djoin_upperbound _ (fun b: bool => if b then base else (djoin (fun a : A => next (rec (os a))))) true).
            i. destruct a; auto. }
          apply (@dle_transitive (djoin (fun a => next (rec (os a))))); auto.
          { apply djoin_supremum; auto. i.
            apply (@dle_transitive (next (rec (os a)))); auto.
            { eapply next_mon; auto. apply H. }
            { apply (djoin_upperbound (fun a0 => next (rec (os a0))) a). auto. }
          }
          { eapply (@djoin_upperbound _ (fun b: bool => if b then base else (djoin (fun a : A => next (rec (os a))))) false).
            i. destruct a; auto. }
      - apply (@dle_transitive (dunion base (djoin (fun a => next (f (os a)))))); auto; auto.
        + ss. apply djoin_supremum; auto.
          i. destruct a; auto.
          { eapply (@djoin_upperbound _ (fun b: bool => if b then base else (djoin (fun a : A => next (f (os a))))) true).
            i. destruct a; auto. }
          apply (@dle_transitive (djoin (fun a => next (f (os a))))); auto.
          { apply djoin_supremum; auto. i.
            apply (@dle_transitive (next (f (os a)))); auto.
            { eapply next_mon; auto. apply H. }
            { apply (djoin_upperbound (fun a0 => next (f (os a0))) a). auto. }
          }
          { eapply (@djoin_upperbound _ (fun b: bool => if b then base else (djoin (fun a : A => next (f (os a))))) false).
            i. destruct a; auto. }
        + apply RED.
    Qed.
  End REC.


  Section REC2.
    Variable D: Type.
    Variable dle: D -> D -> Prop.
    Variable djoin: forall A (ds: A -> D), D.

    Variable base0: D.
    Variable next0: D -> D.

    Variable base1: D.
    Variable next1: D -> D.

    Hypothesis BASELE: dle base0 base1.
    Hypothesis NEXTLE: forall d0 d1 (LE: dle d0 d1), dle (next0 d0) (next1 d1).

    Context `{dle_PreOrder: PreOrder _ dle}.
    Hypothesis djoin_upperbound: forall A (ds: A -> D) (a: A), dle (ds a) (djoin ds).
    Hypothesis djoin_supremum: forall A (ds: A -> D) (d: D) (LE: forall a, dle (ds a) d), dle (djoin ds) d.

    Lemma rec_mon o: dle (rec base0 next0 djoin o) (rec base1 next1 djoin o).
    Proof.
      induction o. ss. eapply djoin_supremum. i.
      etransitivity; [|eapply (djoin_upperbound _ a)]. ss. destruct a; auto.
      eapply djoin_supremum. i.
      etransitivity; [|eapply (djoin_upperbound _ a)]. ss.
      eapply NEXTLE. auto.
    Qed.
  End REC2.


  Section OREC.
    Variable base: t.
    Variable next: t -> t.

    Definition orec: t -> t := rec base next join.

    Hypothesis next_le: forall o, le o (next o).
    Hypothesis next_mon: forall o0 o1 (LE: le o0 o1), le (next o0) (next o1).

    Let wf: t -> Prop := fun _ => True.

    Let dle_reflexive: forall d (WF: wf d), le d d .
    Proof. i. reflexivity. Qed.

    Let dle_transitive: forall d1 d0 d2 (WF0: wf d0) (WF1: wf d1) (WF2: wf d2) (LE0: le d0 d1) (LE1: le d1 d2),
        le d0 d2.
    Proof. i. transitivity d1; eauto. Qed.

    Let djoin_upperbound: forall A (ds: A -> t) (a: A) (WF: forall a, wf (ds a)), le (ds a) (join ds).
    Proof. i. eapply join_upperbound. Qed.
    Let djoin_supremum: forall A (ds: A -> t) (d: t) (WF: forall a, wf (ds a)) (WFD: wf d) (LE: forall a, le (ds a) d), le (join ds) d.
    Proof. i. eapply join_supremum. auto. Qed.

    Let djoin_wf: forall A (ds: A -> t) (WF: forall a, wf (ds a)), wf (join ds).
    Proof. i. ss. Qed.

    Let base_wf: wf base.
    Proof. ss. Qed.
    Let next_wf: forall d (WF: wf d), wf (next d).
    Proof. ss. Qed.

    Let le_PreOrder := le_PreOrder.
    Let join_upperbound := join_upperbound.
    Let join_supremum := join_supremum.

    Lemma le_orec (o0 o1: t) (LE: le o0 o1): le (orec o0) (orec o1).
    Proof.
      unfold orec. eapply le_rec with (wf:=wf); auto.
    Qed.

    Lemma eq_orec (o0 o1: t) (EQ: eq o0 o1): eq (orec o0) (orec o1).
    Proof.
      unfold orec. eapply eq_rec with (wf:=wf); auto.
    Qed.

    Lemma orec_is_O (o: t) (ZERO: is_O o): eq (orec o) base.
    Proof.
      unfold orec. eapply rec_is_O with (wf:=wf); auto.
    Qed.

    Lemma orec_is_S o s (SUCC: is_S o s): eq (orec s) (next (orec o)).
    Proof.
      unfold orec. eapply rec_is_S with (wf:=wf); auto.
    Qed.

    Lemma orec_is_join_inhabited A (os: A -> t) o
          (INHABITED: inhabited A) (JOIN: is_join os o)
      : eq (orec o) (join (fun a => orec (os a))).
    Proof.
      unfold orec. eapply rec_is_join_inhabited with (wf:=wf); auto.
    Qed.

    Lemma orec_is_join A (os: A -> t) o
          (JOIN: is_join os o)
      : eq (orec o) (union base (join (fun a => orec (os a)))).
    Proof.
      unfold orec. eapply rec_is_join with (wf:=wf); auto.
    Qed.

    Lemma orec_O: eq (orec O) base.
    Proof.
      eapply orec_is_O. eapply O_is_O.
    Qed.

    Lemma orec_S o: eq (orec (S o)) (next (orec o)).
    Proof.
      eapply orec_is_S. eapply S_is_S.
    Qed.

    Lemma orec_join A (os: A -> t)
      : eq (orec (join os)) (union base (join (fun a => orec (os a)))).
    Proof.
      eapply orec_is_join; eauto. eapply join_is_join.
    Qed.

    Lemma orec_join_inhabited A (os: A -> t)
          (INHABITED: inhabited A)
      : eq (orec (join os)) (join (fun a => orec (os a))).
    Proof.
      eapply orec_is_join_inhabited; eauto. eapply join_is_join.
    Qed.

    Lemma orec_build A (os: A -> t)
      :
        eq (orec (build os)) (union base (join (fun a => next (orec (os a))))).
    Proof.
      reflexivity.
    Qed.

    Lemma orec_union o0 o1:
      eq (orec (union o0 o1)) (union (orec o0) (orec o1)).
    Proof.
      eapply rec_union with (wf:=wf); auto.
    Qed.

    Lemma orec_le_base o: le base (orec o).
    Proof.
      eapply (@rec_le_base _ base next join le wf); ss.
      i. eapply next_mon; auto.
    Qed.

    Lemma orec_build_supremum o1 r
          (BASE: le base r)
          (UPPERBOUND: forall o0 (LT: lt o0 o1), le (next (orec o0)) r)
      :
        le (orec o1) r.
    Proof.
      destruct o1. ss. eapply join_supremum. i. destruct a; auto.
      eapply join_supremum. i. eapply UPPERBOUND. eapply build_upperbound.
    Qed.

    Lemma orec_unique (f: t -> t)
          (RED: forall A (os: A -> t),
              eq (f (build os)) (union base (join (fun a => next (f (os a))))))
          (WF: forall o, wf (f o))
      :
        forall o, eq (f o) (orec o).
    Proof.
      eapply (@rec_unique _ base next join le wf); ss.
      i. eapply next_mon; auto.
    Qed.
  End OREC.


  Section OREC2.
    Variable base0: t.
    Variable next0: t -> t.

    Variable base1: t.
    Variable next1: t -> t.

    Hypothesis BASELE: le base0 base1.
    Hypothesis NEXTLE: forall o0 o1 (LE: le o0 o1), le (next0 o0) (next1 o1).

    Lemma orec_mon o: le (orec base0 next0 o) (orec base1 next1 o).
    Proof.
      eapply (@rec_mon t le join base0 next0 base1 next1); auto.
      { eapply le_PreOrder. }
      { i. eapply join_upperbound. }
      { i. eapply join_supremum. auto. }
    Qed.
  End OREC2.


  Section ARITHMETIC.
    Let flip A B C (f: A -> B -> C): B -> A -> C := fun b a => f a b.

    Lemma orec_of_S: forall o, eq o (orec O S o).
    Proof.
      i. eapply orec_unique with (f:=id); auto.
      { eapply le_S. }
      { i. etransitivity.
        { eapply build_join_S. }
        { symmetry. eapply union_max. apply O_bot. }
      }
    Qed.

    Fixpoint from_nat (n: nat): t :=
      match n with
      | 0 => O
      | Datatypes.S n' => S (from_nat n')
      end.

    Definition omega: t := join from_nat.

    Section ADD.
      Definition add (o0: t): forall (o1: t), t := orec o0 S.

      Let _S_le o: le o (S o).
      Proof.
        eapply S_le.
      Qed.

      Let _le_S o0 o1 (LE: le o0 o1): le (S o0) (S o1).
      Proof.
        apply le_S. auto.
      Qed.

      Lemma add_base_l o0 o1: le o0 (add o0 o1).
      Proof.
        eapply orec_le_base; auto.
      Qed.

      Lemma add_base_r o0 o1: le o1 (add o0 o1).
      Proof.
        transitivity (orec O S o1).
        { eapply orec_of_S. }
        { eapply orec_mon; auto. eapply O_bot. }
      Qed.

      Lemma add_O_r o: eq (add o O) o.
      Proof.
        eapply (@orec_O o S); auto.
      Qed.

      Lemma add_S o0 o1: eq (add o0 (S o1)) (S (add o0 o1)).
      Proof.
        eapply (@orec_S o0 S); auto.
      Qed.

      Lemma add_join o A (os: A -> t):
        eq (add o (join os)) (union o (join (fun a => add o (os a)))).
      Proof.
        eapply (@orec_join o S); eauto.
      Qed.

      Lemma add_join_inhabited o A (os: A -> t)
            (INHABITED: inhabited A):
        eq (add o (join os)) (join (fun a => add o (os a))).
      Proof.
        eapply (@orec_join_inhabited o S); eauto.
      Qed.

      Lemma add_build o A (os: A -> t)
        :
          eq (add o (build os)) (union o (join (fun a => S (add o (os a))))).
      Proof.
        eapply orec_build.
      Qed.

      Lemma add_union o0 o1 o2
        :
          eq (add o0 (union o1 o2)) (union (add o0 o1) (add o0 o2)).
      Proof.
        eapply orec_union; auto.
      Qed.

      Lemma le_add_r o0 o1 o2 (LE: le o1 o2)
        :
          le (add o0 o1) (add o0 o2).
      Proof.
        eapply le_orec; auto.
      Qed.

      Lemma lt_add_r o0 o1 o2 (LT: lt o1 o2)
        :
          lt (add o0 o1) (add o0 o2).
      Proof.
        eapply S_spec in LT.
        eapply lt_le_lt.
        2: { eapply le_add_r. eapply LT. }
        eapply lt_eq_lt.
        { eapply add_S. }
        eapply S_lt.
      Qed.

      Lemma eq_add_r o0 o1 o2 (EQ: eq o1 o2)
        :
          eq (add o0 o1) (add o0 o2).
      Proof.
        split.
        - eapply le_add_r; eauto. eapply EQ.
        - eapply le_add_r; eauto. eapply EQ.
      Qed.

      Lemma le_add_l o0 o1 o2 (LE: le o0 o1)
        :
          le (add o0 o2) (add o1 o2).
      Proof.
        eapply (@orec_mon o0 S o1 S); auto.
      Qed.

      Lemma eq_add_l o0 o1 o2 (EQ: eq o0 o1)
        :
          eq (add o0 o2) (add o1 o2).
      Proof.
        split.
        - eapply le_add_l; eauto. eapply EQ.
        - eapply le_add_l; eauto. eapply EQ.
      Qed.

      Lemma add_O_l o: eq (add O o) o.
      Proof.
        induction o. etransitivity.
        { eapply add_build. }
        { split.
          - eapply union_spec.
            + eapply O_bot.
            + eapply join_supremum. i. eapply S_spec.
              eapply eq_lt_lt.
              * eapply H.
              * eapply build_upperbound.
          - eapply build_spec. i.
            eapply (@lt_le_lt (join (fun a0 => S (orec O S (os a0))))).
            2: { eapply union_r. }
            eapply eq_lt_lt.
            { symmetry. eapply H. }
            eapply lt_le_lt.
            { eapply S_lt. }
            { eapply (@join_upperbound _ (fun a0 => S (orec O S (os a0)))). }
        }
      Qed.

      Lemma add_assoc o0 o1 o2: eq (add (add o0 o1) o2) (add o0 (add o1 o2)).
      Proof.
        revert o0 o1. induction o2. i. etransitivity.
        { eapply add_build. } etransitivity.
        2: {
          eapply eq_add_r; auto.
          { symmetry. eapply add_build. }
        }
        etransitivity.
        2: { symmetry. eapply add_union; auto. }
        split.
        { eapply union_spec.
          { eapply union_l. }
          { eapply join_supremum. i. etransitivity.
            { apply le_S. eapply H. }
            etransitivity.
            2: { eapply union_r. }
            etransitivity.
            2: {
              eapply le_add_r.
              eapply (@join_upperbound _ (fun a0 : A => S (add o1 (os a0))) a).
            }
            eapply add_S.
          }
        }
        { eapply union_spec.
          { eapply union_l. }
          etransitivity.
          { eapply add_join. }
          eapply union_spec.
          { etransitivity.
            { eapply add_base_l. }
            { eapply union_l. }
          }
          etransitivity.
          2: { eapply union_r. }
          eapply le_join. i. exists a0.
          etransitivity.
          { eapply add_S. }
          { apply le_S. eapply H. }
        }
      Qed.

      Lemma add_lt_l o0 o1 (LT: lt O o1): lt o0 (add o0 o1).
      Proof.
        eapply S_spec in LT. eapply (@lt_le_lt (add o0 (S O))).
        { eapply lt_eq_lt.
          { eapply add_S. }
          eapply lt_le_lt.
          { eapply S_lt. }
          eapply le_S. eapply add_base_l.
        }
        { eapply le_add_r. auto. }
      Qed.
    End ADD.

    Section RECAPP.
      Variable D: Type.
      Variable next: D -> D.
      Variable djoin: forall (A: MyT) (ds: A -> D), D.

      Variable dle: D -> D -> Prop.
      Variable wf: D -> Prop.

      Hypothesis dle_reflexive: forall d (WF: wf d), dle d d.
      Hypothesis dle_transitive: forall d1 d0 d2 (WF0: wf d0) (WF1: wf d1) (WF2: wf d2) (LE0: dle d0 d1) (LE1: dle d1 d2),
          dle d0 d2.

      Hypothesis djoin_upperbound: forall A (ds: A -> D) (a: A) (WF: forall a, wf (ds a)), dle (ds a) (djoin ds).
      Hypothesis djoin_supremum: forall A (ds: A -> D) (d: D) (WF: forall a, wf (ds a)) (WFD: wf d) (LE: forall a, dle (ds a) d), dle (djoin ds) d.
      Hypothesis djoin_wf: forall A (ds: A -> D) (WF: forall a, wf (ds a)), wf (djoin ds).

      Hypothesis next_wf: forall d (WF: wf d), wf (next d).

      Hypothesis next_le: forall d (WF: wf d), dle d (next d).
      Hypothesis next_mon: forall d0 d1 (WF0: wf d0) (WF1: wf d1) (LE: dle d0 d1), dle (next d0) (next d1).

      Let deq: D -> D -> Prop :=
        fun d0 d1 => dle d0 d1 /\ dle d1 d0.

      Let dunion (d0 d1: D): D := djoin (fun b: bool => if b then d0 else d1).

      Let dunion_l d0 d1 (WF0: wf d0) (WF1: wf d1): dle d0 (dunion d0 d1).
      Proof.
        eapply (@djoin_upperbound _ (fun b: bool => if b then d0 else d1) true). i. destruct a; auto.
      Qed.

      Let dunion_r d0 d1 (WF0: wf d0) (WF1: wf d1): dle d1 (dunion d0 d1).
      Proof.
        eapply (@djoin_upperbound _ (fun b: bool => if b then d0 else d1) false). i. destruct a; auto.
      Qed.

      Let dunion_supremum d0 d1 u (WF0: wf d0) (WF1: wf d1) (WFU: wf u) (LE0: dle d0 u) (LE1: dle d1 u):
        dle (dunion d0 d1) u.
      Proof.
        eapply djoin_supremum; auto.
        { i. destruct a; auto. }
        { i. destruct a; auto. }
      Qed.

      Let dunion_wf d0 d1 (WF0: wf d0) (WF1: wf d1): wf (dunion d0 d1).
      Proof.
        eapply djoin_wf. i. destruct a; auto.
      Qed.

      Let drec_wf base (WF: wf base) o: wf (rec base next djoin o).
      Proof.
        eapply (rec_wf base next djoin dle wf); auto.
      Qed.

      Let drec_rec_wf base (WF: wf base) o0 o1:
        wf (rec (rec base next djoin o0) next djoin o1).
      Proof.
        eapply (rec_wf _ next djoin dle wf); auto.
      Qed.

      Let djoin_le A (ds0 ds1: A -> D)
          (WF0: forall a, wf (ds0 a))
          (WF1: forall a, wf (ds1 a))
          (LE: forall a, dle (ds0 a) (ds1 a))
        :
          dle (djoin ds0) (djoin ds1).
      Proof.
        eapply djoin_supremum; auto.
        i. eapply (@dle_transitive (ds1 a)); auto.
      Qed.

      Let djoin_eq A (ds0 ds1: A -> D)
          (WF0: forall a, wf (ds0 a))
          (WF1: forall a, wf (ds1 a))
          (EQ: forall a, deq (ds0 a) (ds1 a))
        :
          deq (djoin ds0) (djoin ds1).
      Proof.
        split.
        { eapply djoin_le; auto. i. eapply EQ. }
        { eapply djoin_le; auto. i. eapply EQ. }
      Qed.

      Let dunion_le dl0 dl1 dr0 dr1
          (WFL0: wf dl0) (WFL1: wf dl1) (WFR0: wf dr0) (WFR1: wf dr1)
          (LEL: dle dl0 dl1) (LER: dle dr0 dr1):
        dle (dunion dl0 dr0) (dunion dl1 dr1).
      Proof.
        eapply djoin_le.
        { i. destruct a; auto. }
        { i. destruct a; auto. }
        { i. destruct a; auto. }
      Qed.

      Let next_eq d0 d1
          (WF0: wf d0) (WF1: wf d1) (EQ: deq d0 d1)
        :
          deq (next d0) (next d1).
      Proof.
        split; eapply next_mon; auto; apply EQ.
      Qed.

      Let dunion_eq dl0 dl1 dr0 dr1
          (WFL0: wf dl0) (WFL1: wf dl1) (WFR0: wf dr0) (WFR1: wf dr1)
          (EQL: deq dl0 dl1) (EQR: deq dr0 dr1):
        deq (dunion dl0 dr0) (dunion dl1 dr1).
      Proof.
        eapply djoin_eq; auto.
        { i. destruct a; auto. }
        { i. destruct a; auto. }
        { i. destruct a; auto. }
      Qed.

      Let deq_transitive: forall d1 d0 d2 (WF0: wf d0) (WF1: wf d1) (WF2: wf d2) (LE0: deq d0 d1) (LE1: deq d1 d2),
          deq d0 d2.
      Proof.
        i. inv LE0. inv LE1. split; eauto.
      Qed.

      Let drec_red base A (os: A -> t):
        rec base next djoin (build os) =
        dunion base (djoin (fun a => next (rec base next djoin (os a)))).
      Proof.
        eapply rec_red.
      Qed.

      Lemma rec_app base o0 o1 (WF: wf base):
        deq (rec base next djoin (add o0 o1)) (rec (rec base next djoin o0) next djoin o1).
      Proof.
        induction o1.

        eapply (@deq_transitive (dunion (rec base next djoin o0) (dunion base (djoin (fun a => next (rec (rec base next djoin o0) next djoin (os a))))))); auto.
        { eapply dunion_wf; auto. }
        { eapply (@deq_transitive (rec base next djoin (union o0 (join (fun a : A => S (add o0 (os a))))))); auto.
          { eapply dunion_wf; auto. }
          { eapply (@eq_rec _ base next djoin dle wf); auto.
            symmetry. eapply add_build. }
          eapply (@deq_transitive (dunion (rec base next djoin o0) (rec base next djoin (join (fun a : A => S (add o0 (os a))))))); auto.
          { eapply dunion_wf; auto. }
          { eapply (rec_union base next djoin dle wf); auto. }
          eapply dunion_eq; auto.
          { split; apply dle_reflexive; auto. }
          { eapply (@deq_transitive (dunion base (djoin (fun a : A => rec base next djoin ((fun a0 : A => S (add o0 (os a0))) a))))); auto.
            { eapply (rec_join base next djoin dle wf); auto. }
            { eapply dunion_eq; auto.
              { split; auto. }
              { eapply djoin_eq; auto. i.
                eapply (@deq_transitive (next (rec base next djoin (add o0 (os a))))); auto.
                eapply (rec_S base next djoin dle wf); auto.
              }
            }
          }
        }

        rewrite drec_red. split.
        { eapply dunion_supremum; auto.
          eapply dunion_supremum; auto.
          eapply (@dle_transitive (rec base next djoin o0)); auto.
          eapply (rec_le_base base next djoin dle wf); auto.
        }
        { eapply dunion_le; auto. }
      Qed.
    End RECAPP.

    Section ORECAPP.
      Variable next: t -> t.
      Hypothesis next_le: forall o, le o (next o).
      Hypothesis next_mon: forall o0 o1 (LE: le o0 o1), le (next o0) (next o1).

      Lemma orec_app base o0 o1:
        eq (orec base next (add o0 o1)) (orec (orec base next o0) next o1).
      Proof.
        eapply (rec_app next join le (fun _ => True)); auto.
        { i. reflexivity. }
        { i. transitivity d1; auto. }
        { i. eapply join_upperbound. }
        { i. eapply join_supremum. auto. }
      Qed.
    End ORECAPP.


    Section MULT.
      Definition mult (o0: t): forall (o1: t), t := orec O (flip add o0).

      Lemma mult_gen_le o0 o1: le o1 (flip add o0 o1).
      Proof.
        eapply add_base_l.
      Qed.
      Let _mult_gen_le := mult_gen_le.

      Lemma mult_gen_mon o o0 o1 (LE: le o0 o1): le (flip add o o0) (flip add o o1).
      Proof.
        eapply le_add_l. auto.
      Qed.
      Let _mult_gen_mon := mult_gen_mon.

      Lemma mult_O_r o: eq (mult o O) O.
      Proof.
        eapply (@orec_O O (flip add o)); auto.
      Qed.

      Lemma mult_S o0 o1: eq (mult o0 (S o1)) (add (mult o0 o1) o0).
      Proof.
        eapply (@orec_S O (flip add o0)); auto.
      Qed.

      Lemma mult_join o A (os: A -> t):
        eq (mult o (join os)) (join (fun a => mult o (os a))).
      Proof.
        transitivity (union O (join (fun a => mult o (os a)))).
        { eapply (@orec_join O (flip add _)); eauto. }
        { eapply union_max. eapply O_bot. }
      Qed.

      Lemma mult_build o A (os: A -> t)
        :
          eq (mult o (build os)) (join (fun a => add (mult o (os a)) o)).
      Proof.
        transitivity (union O (join (fun a => add (mult o (os a)) o))).
        { eapply (@orec_build O (flip add _)); eauto. }
        { eapply union_max. eapply O_bot. }
      Qed.

      Lemma mult_union o0 o1 o2
        :
          eq (mult o0 (union o1 o2)) (union (mult o0 o1) (mult o0 o2)).
      Proof.
        eapply orec_union; auto.
      Qed.

      Lemma le_mult_r o0 o1 o2 (LE: le o1 o2)
        :
          le (mult o0 o1) (mult o0 o2).
      Proof.
        eapply le_orec; auto.
      Qed.

      Lemma eq_mult_r o0 o1 o2 (EQ: eq o1 o2)
        :
          eq (mult o0 o1) (mult o0 o2).
      Proof.
        split.
        - eapply le_mult_r; eauto. eapply EQ.
        - eapply le_mult_r; eauto. eapply EQ.
      Qed.

      Lemma le_mult_l o0 o1 o2 (LE: le o0 o1)
        :
          le (mult o0 o2) (mult o1 o2).
      Proof.
        eapply (@orec_mon O (flip add o0) O (flip add o1)); auto.
        { reflexivity. }
        { i. unfold flip. transitivity (add o4 o0).
          { eapply le_add_l; auto. }
          { eapply le_add_r; auto. }
        }
      Qed.

      Lemma eq_mult_l o0 o1 o2 (EQ: eq o0 o1)
        :
          eq (mult o0 o2) (mult o1 o2).
      Proof.
        split.
        - eapply le_mult_l; eauto. eapply EQ.
        - eapply le_mult_l; eauto. eapply EQ.
      Qed.

      Lemma lt_mult_r o0 o1 o2 (LT: lt o1 o2) (POS: lt O o0)
        :
          lt (mult o0 o1) (mult o0 o2).
      Proof.
        eapply S_spec in LT.
        eapply lt_le_lt.
        2: { eapply le_mult_r. eapply LT. }
        eapply lt_eq_lt.
        { eapply mult_S. }
        eapply add_lt_l. auto.
      Qed.

      Lemma mult_O_l o: eq (mult O o) O.
      Proof.
        induction o. etransitivity.
        { eapply mult_build. }
        { split.
          - eapply join_supremum. i.
            transitivity (mult O (os a)); auto.
            { eapply add_O_r. }
            { eapply H. }
          - eapply O_bot. }
      Qed.

      Lemma mult_1_r o: eq (mult o (S O)) o.
      Proof.
        unfold from_nat. etransitivity.
        { eapply mult_S. }
        etransitivity.
        { eapply eq_add_l. eapply mult_O_r. }
        eapply add_O_l.
      Qed.

      Lemma mult_1_l o: eq (mult (S O) o) o.
      Proof.
        unfold from_nat. transitivity (orec O S o).
        2: { symmetry. eapply orec_of_S. }
        split.
        { eapply orec_mon.
          { reflexivity. }
          { i. unfold flip. etransitivity.
            { eapply add_S. }
            { apply le_S. transitivity o0; auto.
              eapply add_O_r.
            }
          }
        }
        { eapply orec_mon.
          { reflexivity. }
          { i. unfold flip. etransitivity.
            { apply le_S. eapply LE. }
            transitivity (S (add o1 O)); auto.
            { apply le_S. eapply add_O_r. }
            { eapply add_S. }
          }
        }
      Qed.

      Lemma mult_dist o0 o1 o2: eq (mult o0 (add o1 o2)) (add (mult o0 o1) (mult o0 o2)).
      Proof.
        revert o0 o1. induction o2. i. etransitivity.
        { eapply eq_mult_r. eapply add_build. }
        etransitivity.
        2: { eapply eq_add_r. symmetry. eapply mult_build. }
        etransitivity.
        { eapply mult_union. }
        etransitivity.
        { eapply eq_union.
          { reflexivity. }
          { eapply mult_join. }
        }
        etransitivity.
        2: { symmetry. eapply add_join. }
        eapply eq_union.
        { reflexivity. } split.
        { eapply le_join. i. exists a0.
          etransitivity.
          { eapply mult_S. }
          etransitivity.
          { eapply eq_add_l. symmetry. eapply H. }
          eapply add_assoc.
        }
        { eapply le_join. i. exists a0.
          etransitivity.
          { eapply add_assoc. }
          etransitivity.
          { eapply eq_add_l. eapply H. }
          eapply mult_S.
        }
      Qed.

      Lemma mult_assoc o0 o1 o2: eq (mult (mult o0 o1) o2) (mult o0 (mult o1 o2)).
      Proof.
        revert o0 o1. induction o2. i. etransitivity.
        { eapply mult_build. } etransitivity.
        2: {
          eapply eq_mult_r; auto.
          { symmetry. eapply mult_build. }
        }
        etransitivity.
        2: { symmetry. eapply mult_join. }
        split.
        { eapply le_join. i. exists a0.
          etransitivity.
          { eapply le_add_l. eapply H. }
          { eapply mult_dist. }
        }
        { eapply le_join. i. exists a0.
          etransitivity.
          { eapply mult_dist. }
          { eapply le_add_l. eapply H. }
        }
      Qed.

      Lemma mult_le_l o0 o1 (POS: lt O o0): le o1 (mult o1 o0).
      Proof.
        eapply S_spec in POS. etransitivity.
        2: { eapply le_mult_r in POS. eauto. }
        eapply mult_1_r.
      Qed.

      Lemma mult_lt_l o0 o1 (POS: lt O o1)
            (TWO: lt (S O) o0): lt o1 (mult o1 o0).
      Proof.
        eapply S_spec in TWO. eapply (@lt_le_lt (mult o1 (S (S O)))).
        { eapply lt_eq_lt.
          { eapply mult_S. }
          eapply lt_eq_lt.
          { eapply eq_add_l. eapply mult_S. }
          eapply lt_eq_lt.
          { eapply add_assoc. }
          eapply lt_le_lt.
          2: { eapply add_base_r. }
          eapply add_lt_l. apply POS.
        }
        { eapply le_mult_r. auto. }
      Qed.

    End MULT.


    Section EXPN.
      Definition expn (o0: t): forall (o1: t), t := orec (S O) (flip mult o0).

      Let expn_gen_mon o o0 o1 (LE: le o0 o1):
        le (flip mult o o0) (flip mult o o1).
      Proof.
        eapply le_mult_l. auto.
      Qed.

      Section BASE.
        Variable base: t.

        Lemma expn_O o: eq (expn o O) (S O).
        Proof.
          eapply orec_O; auto.
        Qed.

        Lemma expn_pos o: lt O (expn base o).
        Proof.
          eapply lt_le_lt.
          { eapply S_lt. }
          { eapply orec_le_base. auto. }
        Qed.

        Section POSITIVE.
          Hypothesis POS: lt O base.

          Let expn_gen_le o: le o (flip mult base o).
          Proof.
            eapply mult_le_l; auto.
          Qed.

          Lemma expn_S o:
            eq (expn base (S o)) (mult (expn base o) base).
          Proof.
            eapply orec_S; auto.
          Qed.

          Lemma le_expn_r o0 o1 (LE: le o0 o1):
            le (expn base o0) (expn base o1).
          Proof.
            eapply le_orec; auto.
          Qed.

          Lemma eq_expn_r o0 o1 (EQ: eq o0 o1):
            eq (expn base o0) (expn base o1).
          Proof.
            eapply eq_orec; auto.
          Qed.

          Lemma expn_join A (os: A -> t):
            eq (expn base (join os)) (union (S O) (join (fun a => expn base (os a)))).
          Proof.
            eapply orec_join; auto.
          Qed.

          Lemma expn_join_inhabited A (os: A -> t)
                (INHABITED: inhabited A):
            eq (expn base (join os)) (join (fun a => expn base (os a))).
          Proof.
            eapply orec_join_inhabited; auto.
          Qed.

          Lemma expn_build A (os: A -> t):
            eq (expn base (build os)) (union (S O) (join (fun a => mult (expn base (os a)) base))).
          Proof.
            eapply orec_build.
          Qed.

          Lemma expn_union o0 o1
            :
              eq (expn base (union o0 o1)) (union (expn base o0) (expn base o1)).
          Proof.
            eapply orec_union; auto.
          Qed.

          Lemma expn_1_r: eq (expn base (S O)) base.
          Proof.
            etransitivity.
            { eapply expn_S. }
            etransitivity.
            { eapply eq_mult_l. eapply expn_O. }
            eapply mult_1_l.
          Qed.

          Lemma expn_add o0 o1:
            eq (expn base (add o0 o1)) (mult (expn base o0) (expn base o1)).
          Proof.
            revert o0. induction o1. i. etransitivity.
            { eapply eq_expn_r. eapply add_build. }
            etransitivity.
            { eapply expn_union. }
            etransitivity.
            2: { eapply eq_mult_r. symmetry. eapply expn_build. }
            etransitivity.
            2: { symmetry. eapply mult_union. }
            etransitivity.
            { eapply eq_union.
              { reflexivity. }
              eapply expn_join.
            }
            etransitivity.
            { eapply union_assoc. }
            eapply eq_union.
            { etransitivity.
              { eapply union_comm. }
              { etransitivity.
                2: { symmetry. eapply mult_1_r. }
                { eapply union_max. eapply S_spec. eapply expn_pos. }
              }
            }
            etransitivity.
            2: { symmetry. eapply mult_join. }
            eapply eq_join. i.
            etransitivity.
            { eapply expn_S. }
            etransitivity.
            2: { eapply mult_assoc. }
            eapply eq_mult_l.
            eapply H.
          Qed.
        End POSITIVE.

        Lemma lt_expn_r (TWO: lt (S O) base) o0 o1 (LT: lt o0 o1):
          lt (expn base o0) (expn base o1).
        Proof.
          assert (POS: lt O base).
          { eapply le_lt_lt; eauto. eapply S_le. }
          eapply (@lt_le_lt (expn base (S o0))).
          { eapply lt_eq_lt.
            { eapply expn_S. auto. }
            { eapply mult_lt_l; auto. eapply expn_pos. }
          }
          { eapply le_expn_r. eapply S_spec. auto. }
        Qed.
      End BASE.

      Lemma expn_1_l o: eq (expn (S O) o) (S O).
      Proof.
        induction o. etransitivity.
        { eapply expn_build. }
        etransitivity.
        { eapply union_comm. }
        eapply union_max. eapply join_supremum.
        i. eapply eq_le_le.
        { eapply mult_1_r. }
        eapply H.
      Qed.

      Lemma le_expn_l o0 o1 o2 (LE: le o0 o1):
        le (expn o0 o2) (expn o1 o2).
      Proof.
        eapply orec_mon.
        { reflexivity. }
        { i. transitivity (mult o3 o1).
          { eapply le_mult_r. auto. }
          { eapply le_mult_l. auto. }
        }
      Qed.

      Lemma eq_expn_l o0 o1 o2 (EQ: eq o0 o1):
        eq (expn o0 o2) (expn o1 o2).
      Proof.
        split; eapply le_expn_l; apply EQ.
      Qed.

      Lemma expn_mult o0 (POS: lt O o0) o1 o2:
        eq (expn o0 (mult o1 o2)) (expn (expn o0 o1) o2).
      Proof.
        induction o2.
        etransitivity.
        { eapply eq_expn_r. eapply mult_build. }
        etransitivity.
        { eapply expn_join. auto. }
        etransitivity.
        2: { symmetry. eapply expn_build. }
        eapply eq_union.
        { reflexivity. }
        eapply eq_join. i.
        etransitivity.
        { eapply expn_add. auto. }
        eapply eq_mult_l. auto.
      Qed.
    End EXPN.

    Section FROMNAT.
      Lemma from_nat_from_peano_lt n:
        eq (from_nat n) (from_wf PeanoNat.Nat.lt_wf_0 n).
      Proof.
        induction n; ss.
        { i. split.
          { eapply O_bot. }
          { unfold from_wf. destruct (PeanoNat.Nat.lt_wf_0 0). ss.
            econs. i. destruct a0. inv l. }
        }
        { etransitivity.
          { eapply eq_S. eapply IHn. }
          split.
          { eapply S_spec. eapply from_acc_lt. econs. }
          { unfold from_wf at 1.
            destruct (PeanoNat.Nat.lt_wf_0 (Datatypes.S n)). ss.
            econs. i. destruct a0. exists tt. ss.
            dup l. eapply Lt.lt_n_Sm_le in l0.
            eapply Lt.le_lt_or_eq in l0. des.
            { eapply lt_le. eapply from_acc_lt. auto. }
            { subst. eapply same_acc_le. }
          }
        }
      Qed.

      Lemma omega_from_peano_lt_set:
        eq omega (from_wf_set PeanoNat.Nat.lt_wf_0).
      Proof.
        split.
        { eapply join_supremum. i. eapply eq_le_le.
          { eapply from_nat_from_peano_lt. }
          eapply lt_le. eapply from_wf_set_upperbound.
        }
        { eapply build_spec. i. eapply lt_le_lt.
          { eapply from_wf_lt. econs. }
          eapply eq_le_le.
          { symmetry. eapply from_nat_from_peano_lt. }
          { eapply join_upperbound. }
        }
      Qed.

      Lemma le_from_nat n0 n1 (LE: Peano.le n0 n1):
        le (from_nat n0) (from_nat n1).
      Proof.
        induction LE.
        { reflexivity. }
        { etransitivity; eauto. ss. eapply S_le. }
      Qed.

      Lemma lt_from_nat n0 n1 (LT: Peano.lt n0 n1):
        lt (from_nat n0) (from_nat n1).
      Proof.
        eapply lt_le_lt.
        2: { eapply le_from_nat. eapply LT. }
        { ss. eapply S_lt. }
      Qed.

      Lemma add_from_nat n0 n1:
        eq (from_nat (n0 + n1)) (add (from_nat n0) (from_nat n1)).
      Proof.
        induction n1; ss.
        { rewrite PeanoNat.Nat.add_0_r.
          symmetry. eapply add_O_r. }
        { rewrite PeanoNat.Nat.add_succ_r. ss.
          etransitivity.
          { eapply eq_S. eapply IHn1. }
          symmetry. eapply add_S.
        }
      Qed.

      Lemma mult_from_nat n0 n1:
        eq (from_nat (n0 * n1)) (mult (from_nat n0) (from_nat n1)).
      Proof.
        induction n1; ss.
        { rewrite PeanoNat.Nat.mul_0_r.
          symmetry. eapply mult_O_r. }
        { rewrite PeanoNat.Nat.mul_succ_r.
          etransitivity.
          { eapply add_from_nat. }
          etransitivity.
          { eapply eq_add_l. eapply IHn1. }
          symmetry. eapply mult_S.
        }
      Qed.

      Lemma expn_from_nat n0 (POS: 0 < n0) n1:
        eq (from_nat (Nat.pow n0 n1)) (expn (from_nat n0) (from_nat n1)).
      Proof.
        induction n1; ss.
        { symmetry. eapply expn_O. }
        { etransitivity.
          { rewrite PeanoNat.Nat.mul_comm. eapply mult_from_nat. }
          etransitivity.
          { eapply eq_mult_l. eapply IHn1. }
          symmetry. eapply expn_S.
          eapply (@lt_from_nat 0 n0). auto.
        }
      Qed.
    End FROMNAT.
  End ARITHMETIC.

  Definition hartogs (A: MyT) := @build (@sig (A -> A -> Prop) (@well_founded _)) (fun RWF => from_wf_set (proj2_sig RWF)).

End TYPE.
End Ord.
