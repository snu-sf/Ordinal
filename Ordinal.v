Require Import sflib.

Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms. (* TODO: Use Morphisms *)
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.
Set Primitive Projections.

Module Cardinality.
  Variant le (A B: Type): Prop :=
  | le_intro
      (f: A -> B)
      (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
  .
  Hint Constructors le.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. eapply le_intro with (f:=id). i. ss.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H. inv H0. eapply le_intro with (f := compose f0 f).
    i. eapply INJ. eapply INJ0. auto.
  Qed.

  Variant oto (A B: Type): Prop :=
  | oto_intro
      (f: A -> B)
      (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
      (SURJ: forall b, exists a, f a = b)
  .
  Hint Constructors oto.

  Variant bij (A B: Type): Prop :=
  | bij_intro
      (f: A -> B) (g: B -> A)
      (FG: forall a, g (f a) = a)
      (GF: forall b, f (g b) = b)
  .
  Hint Constructors bij.

  Lemma bij_oto_equiv A B: bij A B <-> oto A B.
  Proof.
    split; i.
    - inv H. eapply oto_intro with (f:=f).
      + i. eapply f_equal with (f:=g) in EQ.
        repeat rewrite FG in EQ.  auto.
      + i. exists (g b). auto.
    - inv H. eapply choice in SURJ. des.
      eapply bij_intro with (f:=f) (g:=f0); auto.
  Qed.

  Global Program Instance bij_Equivalence: Equivalence bij.
  Next Obligation.
  Proof.
    ii. eapply bij_intro with (f:=id) (g:=id); auto.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H. eapply bij_intro with (f:=g) (g:=f); auto.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H. inv H0. eapply bij_intro with (f:=compose f0 f) (g:=compose g g0); auto.
    - i. unfold compose. rewrite FG0. eapply FG.
    - i. unfold compose. rewrite GF. eapply GF0.
  Qed.

  Global Program Instance oto_Equivalence: Equivalence oto.
  Next Obligation.
  Proof.
    ii. eapply bij_oto_equiv. reflexivity.
  Qed.
  Next Obligation.
  Proof.
    ii. eapply bij_oto_equiv. eapply bij_oto_equiv in H. symmetry. auto.
  Qed.
  Next Obligation.
  Proof.
    ii. eapply bij_oto_equiv. eapply bij_oto_equiv in H. eapply bij_oto_equiv in H0.
    transitivity y; auto.
  Qed.

  Lemma oto_le A B (OTO: oto A B): le A B.
  Proof.
    inv OTO. eapply le_intro with (f:=f). auto.
  Qed.

  Lemma bij_le A B (BIJ: bij A B): le A B.
  Proof.
    eapply bij_oto_equiv in BIJ. eapply oto_le; auto.
  Qed.

  Definition eq (A B: Type): Prop := le A B /\ le B A.

  Lemma eq_le A B (EQ: eq A B): le A B.
  Proof.
    eapply EQ.
  Qed.

  Global Program Instance eq_Equivalence: Equivalence eq.
  Next Obligation.
  Proof.
    ii. split; reflexivity.
  Qed.
  Next Obligation.
  Proof.
    ii. destruct H. split; auto.
  Qed.
  Next Obligation.
  Proof.
    ii. destruct H, H0. split; etransitivity; eauto.
  Qed.

  Global Program Instance le_eq_PartialOrder: PartialOrder eq le.
  Next Obligation.
  Proof. ss. Qed.

  Section SANDWICH.
    Variable A1 B A: Type.
    Variable sub0: A1 -> B.
    Variable sub1: B -> A.
    Variable f: A -> A1.

    Hypothesis SUB0: forall a0 a1 (EQ: sub0 a0 = sub0 a1), a0 = a1.
    Hypothesis SUB1: forall b0 b1 (EQ: sub1 b0 = sub1 b1), b0 = b1.
    Hypothesis INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1.

    Let Fixpoint aseq (n: nat) (a: A): A :=
      match n with
      | 0 => a
      | S n' => sub1 (sub0 (f (aseq n' a)))
      end.

    Let Fixpoint bseq (n: nat) (b: B): A :=
      match n with
      | 0 => sub1 b
      | S n' => sub1 (sub0 (f (bseq n' b)))
      end.

    Let bseq_aseq n:
      forall b, exists a, bseq n b = aseq n a.
    Proof.
      induction n; ss.
      - i. eauto.
      - i. specialize (IHn b). des. exists a. rewrite IHn. auto.
    Qed.

    Let aseq_S_bseq n:
      forall a, exists b, aseq (S n) a = bseq n b.
    Proof.
      induction n; ss.
      - i. eauto.
      - i. specialize (IHn a). des. exists b. rewrite IHn. auto.
    Qed.

    Let aseq_decrease n:
      forall a0, exists a1, aseq (S n) a0 = aseq n a1.
    Proof.
      i. hexploit (aseq_S_bseq n a0). i. des.
      hexploit (bseq_aseq n b). i. des.
      exists a. rewrite H. auto.
    Qed.

    Let bseq_decrease n:
      forall b0, exists b1, bseq (S n) b0 = bseq n b1.
    Proof.
      i. hexploit (bseq_aseq (S n) b0). i. des.
      hexploit (aseq_S_bseq n a). i. des.
      exists b. rewrite H. auto.
    Qed.

    Let in_gap (n: nat) (a1: A): Prop :=
      (exists a0, aseq n a0 = a1) /\
      (forall b0, bseq n b0 <> a1).

    Let in_gap_step (n: nat) (a1: A):
      in_gap (S n) a1 <->
      (exists a0, in_gap n a0 /\ a1 = sub1 (sub0 (f a0))).
    Proof.
      unfold in_gap. split; i.
      - des. ss. exists (aseq n a0). esplits; eauto.
        ii. eapply (H0 b0). rewrite H1. auto.
      - des. subst. ss. esplits; eauto. ii.
        eapply SUB1 in H. eapply SUB0 in H.
        eapply INJ in H. eapply H1; eauto.
    Qed.

    Let in_gap_all (a1: A): Prop :=
      exists n, in_gap n a1.

    Let is_g (g: A -> B): Prop :=
      forall a,
        (forall (GAP: in_gap_all a), g a = sub0 (f a)) /\
        (forall (NGAP: ~ in_gap_all a), sub1 (g a) = a)
    .

    Let is_g_exists: exists g, is_g g.
    Proof.
      eapply (choice (fun a b =>
                        (forall (GAP: in_gap_all a), b = sub0 (f a)) /\
                        (forall (NGAP: ~ in_gap_all a), sub1 b = a))).
      intros a. destruct (classic (in_gap_all a)).
      - exists (sub0 (f a)). split; eauto. ss.
      - destruct (classic (exists b, sub1 b = a)).
        { des. exists b. splits; ss. }
        exfalso. eapply H. exists 0. econs; ss; eauto.
    Qed.

    Let g_inj (g: A -> B) (G: is_g g):
      forall a0 a1 (EQ: g a0 = g a1), a0 = a1.
    Proof.
      i. edestruct (G a0). edestruct (G a1).
      destruct (classic (in_gap_all a0)), (classic (in_gap_all a1)).
      - eapply H in H3. eapply H1 in H4.
        rewrite H3 in *. rewrite H4 in *.
        eapply SUB0 in EQ. eapply INJ in EQ; auto.
      - exfalso. dup H3. dup H4.
        eapply H in H5. eapply H2 in H6.
        inv H3. eapply H4. exists (S x).
        eapply in_gap_step. esplits; eauto.
        rewrite <- H6. rewrite <- EQ. rewrite H5. auto.
      - exfalso. dup H3. dup H4.
        eapply H0 in H5. eapply H1 in H6.
        inv H4. eapply H3. exists (S x).
        eapply in_gap_step. esplits; eauto.
        rewrite <- H6. rewrite <- EQ. rewrite H5. auto.
      - eapply H0 in H3. eapply H2 in H4.
        rewrite EQ in H3. rewrite H3 in *. auto.
    Qed.

    Let g_surj (g: A -> B) (G: is_g g):
      forall b, exists a, g a = b.
    Proof.
      i. destruct (classic (in_gap_all (sub1 b))).
      - dup H. eapply G in H0. inv H. destruct x.
        { unfold in_gap in H1. des. ss. subst. exfalso. eapply H2; eauto. }
        eapply in_gap_step in H1. des. eapply SUB1 in H2. subst.
        dup H1. destruct (G a0). exploit H.
        { exists x. auto. } i. eauto.
      - dup H. eapply G in H0. eapply SUB1 in H0. eauto.
    Qed.

    Lemma sandwich_oto: oto A B.
    Proof.
      hexploit is_g_exists. i. des.
      eapply oto_intro with (f:=g).
      - eapply g_inj. auto.
      - eapply g_surj. auto.
    Qed.

  End SANDWICH.

  Lemma eq_oto_equiv A B: eq A B <-> oto A B.
  Proof.
    split; i.
    - inv H. inv H0. inv H1.
      eapply sandwich_oto with (A1:=A) (sub0:=f) (sub1:=f0) (f:=id); auto.
    - eapply bij_oto_equiv in H. inv H. split.
      + eapply le_intro with (f:=f).
        i. eapply f_equal with (f:=g) in EQ. repeat rewrite FG in EQ. auto.
      + eapply le_intro with (f:=g).
        i. eapply f_equal with (f:=f) in EQ. repeat rewrite GF in EQ. auto.
  Qed.

  Lemma eq_bij_equiv A B: eq A B <-> bij A B.
  Proof.
    erewrite bij_oto_equiv. eapply eq_oto_equiv.
  Qed.

  Global Program Instance le_bij_PartialOrder: PartialOrder bij le.
  Next Obligation.
  Proof.
    ii. ss. rewrite <- eq_bij_equiv. eauto.
  Qed.

  Global Program Instance le_oto_PartialOrder: PartialOrder oto le.
  Next Obligation.
  Proof.
    ii. ss. rewrite <- eq_oto_equiv. eauto.
  Qed.

  Definition lt A B: Prop := le A B /\ ~ eq A B.

  Lemma lt_le A B (LT: lt A B): le A B.
  Proof.
    eapply LT.
  Qed.

  Lemma lt_le_lt B A C (LT: lt A B) (LE: le B C): lt A C.
  Proof.
    inv LT. split.
    - transitivity B; eauto.
    - ii. inv H1. eapply H0. split; auto. transitivity C; auto.
  Qed.

  Lemma le_lt_lt B A C (LE: le A B) (LT: lt B C): lt A C.
  Proof.
    inv LT. split.
    - transitivity B; eauto.
    - ii. inv H1. eapply H0. split; auto. transitivity A; auto.
  Qed.

  Program Instance lt_StrictOrder: StrictOrder lt.
  Next Obligation.
  Proof.
    ii. inv H. eapply H1. reflexivity.
  Qed.
  Next Obligation.
  Proof.
    ii. eapply (@lt_le_lt y); eauto. eapply lt_le; eauto.
  Qed.

  Lemma lt_not_le o0 o1 (LT: lt o0 o1) (LE: le o1 o0): False.
  Proof.
    eapply lt_StrictOrder. eapply le_lt_lt; eauto.
  Qed.

  Lemma lt_eq_lt A B0 B1 (EQ: eq B0 B1):
    lt A B0 <-> lt A B1.
  Proof.
    split; i.
    - inv EQ. eapply lt_le_lt; eauto.
    - inv EQ. eapply lt_le_lt; eauto.
  Qed.

  Lemma eq_lt_lt A0 A1 B (EQ: eq A0 A1):
    lt A0 B <-> lt A1 B.
  Proof.
    split; i.
    - inv EQ. eapply le_lt_lt; eauto.
    - inv EQ. eapply le_lt_lt; eauto.
  Qed.

  Lemma le_eq_le A B0 B1 (EQ: eq B0 B1):
    le A B0 <-> le A B1.
  Proof.
    split; i.
    - inv EQ. transitivity B0; auto.
    - inv EQ. transitivity B1; auto.
  Qed.

  Lemma eq_le_le A0 A1 B (EQ: eq A0 A1):
    le A0 B <-> le A1 B.
  Proof.
    split; i.
    - inv EQ. transitivity A0; auto.
    - inv EQ. transitivity A1; auto.
  Qed.

  Lemma le_eq_or_lt A B:
    le A B <-> (lt A B \/ eq A B).
  Proof.
    split; i.
    - destruct (classic (eq A B)); auto. left. split; auto.
    - des.
      + eapply H.
      + eapply eq_le. auto.
  Qed.
End Cardinality.

Module Ordinal.
  Inductive t: Type :=
  | build (A: Type) (os: A -> t)
  .

  Inductive le: t -> t -> Prop :=
  | le_intro
      A0 A1 os0 os1
      (LE: forall (a0: A0), exists (a1: A1), le (os0 a0) (os1 a1))
    :
      le (build os0) (build os1)
  .
  Hint Constructors le.

  Variant lt: t -> t -> Prop :=
  | lt_intro
      o A os (a: A)
      (LE: le o (os a))
    :
      lt o (build os)
  .
  Hint Constructors le.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. induction x. econs; eauto.
  Qed.
  Next Obligation.
  Proof.
    ii. revert x y H H0. induction z. i.
    dependent destruction H1. dependent destruction H0.
    econs. i. hexploit (LE a0); eauto. i. des.
    hexploit (LE0 a1); eauto. i. des.
    hexploit (H a2 (os1 a0) (os0 a1)); eauto.
  Qed.

  Lemma lt_le o0 o1 (LT: lt o0 o1): le o0 o1.
  Proof.
    ginduction o1. i.
    dependent destruction LT. dependent destruction LE.
    econs. i. hexploit (LE a0); eauto. i. des.
    hexploit (H a (os0 a0)); eauto.
    rewrite <- x. econs; eauto.
  Qed.

  Lemma le_lt_lt o1 o0 o2 (LE: le o0 o1) (LT: lt o1 o2): lt o0 o2.
  Proof.
    dependent destruction LT. econs. etransitivity; eauto.
  Qed.

  Lemma lt_well_founded: well_founded lt.
  Proof.
    ii. cut (forall b (LE: le b a), Acc lt b).
    { i. eapply H. reflexivity. }
    induction a. i. econs. i. dependent destruction H0.
    dependent destruction LE. hexploit (LE a); eauto. i. des.
    eapply H; eauto. etransitivity; eauto.
  Qed.

  Program Instance lt_StrictOrder: StrictOrder lt.
  Next Obligation.
  Proof.
    ii. eapply (well_founded_induction lt_well_founded (fun o => ~ lt o o)); eauto.
  Qed.
  Next Obligation.
  Proof.
    ii. eapply le_lt_lt; eauto. eapply lt_le; eauto.
  Qed.

  Definition eq (o0 o1: t): Prop := le o0 o1 /\ le o1 o0.

  Global Program Instance eq_Equivalence: Equivalence eq.
  Next Obligation.
  Proof.
    ii. split; reflexivity.
  Qed.
  Next Obligation.
  Proof.
    ii. destruct H. split; auto.
  Qed.
  Next Obligation.
  Proof.
    ii. destruct H, H0. split; etransitivity; eauto.
  Qed.

  Global Program Instance le_PartialOrder: PartialOrder eq le.
  Next Obligation.
  Proof. ss. Qed.

  Lemma total o0 o1: le o0 o1 \/ lt o1 o0.
  Proof.
    cut ((le o0 o1 \/ lt o1 o0) /\ (le o1 o0 \/ lt o0 o1)).
    { i. des; auto. }
    ginduction o0. i. split.
    { destruct (classic (exists (a: A), le o1 (os a))).
      { des. right. econs; eauto. }
      assert (forall a, lt (os a) o1).
      { i. eapply not_ex_all_not in H0. instantiate (1:=a) in H0.
        destruct (H a o1). clear H1. des; ss. } clear H0.
      left. destruct o1. econs. i.
      specialize (H1 a0). dependent destruction H1. eauto.
    }
    { destruct o1.
      destruct (classic (forall (a0: A0), exists (a: A), le (os0 a0) (os a))).
      { left. econs; eauto. }
      eapply not_all_ex_not in H0. des.
      assert (forall a, lt (os a) (os0 n)).
      { i. eapply not_ex_all_not in H0. instantiate (1:=a) in H0.
        destruct (H a (os0 n)). clear H1. des; ss. } clear H0.
      right. econs. instantiate (1:=n).
      destruct (os0 n). econs. i. specialize (H1 a0).
      dependent destruction H1. eauto.
    }
  Qed.

  Lemma lt_not_le o0 o1 (LT: lt o0 o1) (LE: le o1 o0): False.
  Proof.
    eapply lt_StrictOrder. eapply le_lt_lt; eauto.
  Qed.

  Lemma lt_le_lt o1 o0 o2 (LT: lt o0 o1) (LE: le o1 o2): lt o0 o2.
  Proof.
    destruct (total o2 o0); auto. exfalso.
    eapply lt_not_le; eauto. etransitivity; eauto.
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

  Lemma le_eq_or_lt o0 o1:
    le o0 o1 <-> (lt o0 o1 \/ eq o0 o1).
  Proof.
    split; i.
    - destruct (total o1 o0).
      + right. split; auto.
      + left. auto.
    - destruct H.
      + eapply lt_le; auto.
      + destruct H. auto.
  Qed.

  Lemma trichotomy o0 o1: lt o0 o1 \/ eq o0 o1 \/ lt o1 o0.
  Proof.
    destruct (total o0 o1); auto. eapply le_eq_or_lt in H. des; auto.
  Qed.

  Lemma build_upperbound A (os: A -> t): forall a, lt (os a) (build os).
  Proof.
    i. econs; eauto. reflexivity.
  Qed.

  Lemma build_spec A (os: A -> t) o (UB: forall a, lt (os a) o):
    le (build os) o.
  Proof.
    destruct o. econs. i.
    specialize (UB a0). dependent destruction UB. eauto.
  Qed.

  Program Fixpoint from_acc A (R: A -> A -> Prop) (a1: A) (ACC: Acc R a1): t :=
    @build (sig (fun a0 => R a0 a1)) (fun a0p =>
                                        @from_acc _ R (proj1_sig a0p) _).
  Next Obligation.
    inv ACC. eapply H0; eauto.
  Defined.

  Arguments from_acc [A R] a1 ACC.

  Lemma from_acc_lt A (R: A -> A -> Prop) (a0 a1: A) (LT: R a0 a1)
        (ACC1: Acc R a1) (ACC0: Acc R a0)
    :
      lt (from_acc a0 ACC0) (from_acc a1 ACC1).
  Proof.
    destruct ACC1. ss.
    set (exist (fun a0 => R a0 a1) a0 LT).
    replace ACC0 with (from_acc_obligation_1 (Acc_intro a1 a) s).
    2: { eapply proof_irrelevance. }
    eapply (build_upperbound (fun a0p => from_acc (proj1_sig a0p) (from_acc_obligation_1 (Acc_intro a1 a) a0p)) s).
  Qed.

  Definition from_wf A (R: A -> A -> Prop) (WF: well_founded R) (a1: A): t :=
    from_acc a1 (WF a1).

  Lemma from_wf_lt A (R: A -> A -> Prop) (WF: well_founded R) (a0 a1: A) (LT: R a0 a1)
    :
      lt (from_wf WF a0) (from_wf WF a1).
  Proof.
    eapply from_acc_lt; eauto.
  Qed.

  Definition from_wf_set A (R: A -> A -> Prop) (WF: well_founded R): t :=
    @build A (from_wf WF).

  Lemma from_wf_set_upperbound A (R: A -> A -> Prop) (WF: well_founded R) a:
    lt (from_wf WF a) (from_wf_set WF).
  Proof.
    eapply build_upperbound.
  Qed.

  Definition is_meet (P: t -> Prop) (o0: t): Prop :=
    P o0 /\ forall o1 (IN: P o1), le o0 o1.

  Lemma meet_exists (P: t -> Prop) (INHABITED: exists o, P o):
    exists o0, is_meet P o0.
  Proof.
    apply NNPP. ii. des.
    hexploit (well_founded_induction lt_well_founded (fun o => ~ P o)); eauto.
    ii. eapply not_ex_all_not in H. instantiate (1:=x) in H.
    apply not_and_or in H. des; ss. eapply H. i.
    destruct (total x o1); auto. eapply H0 in H2. ss.
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

  Lemma is_O_eq o0 o1 (ZERO0: is_O o0) (ZERO1: is_O o1): eq o0 o1.
  Proof.
    split.
    - eapply ZERO0.
    - eapply ZERO1.
  Qed.

  Lemma is_S_eq o s0 s1 (SUCC: is_S o s0): eq s0 s1 <-> is_S o s1.
  Proof.
    split; i.
    - econs.
      + eapply (@lt_le_lt s0).
        * eapply SUCC.
        * eapply H.
      + i. transitivity s0.
        * eapply H.
        * eapply SUCC; auto.
    - split.
      + eapply SUCC. eapply H.
      + eapply H. eapply SUCC.
  Qed.

  Lemma eq_is_S o0 o1 s (SUCC: is_S o0 s): eq o0 o1 <-> is_S o1 s.
  Proof.
    split; i.
    - econs.
      + eapply (@le_lt_lt o0).
        * eapply H.
        * eapply SUCC.
      + i. eapply SUCC.
        eapply le_lt_lt; eauto. eapply H.
    - split.
      + destruct (total o0 o1); auto. exfalso.
        eapply H in H0. eapply (@lt_not_le o0 s); auto. eapply SUCC.
      + destruct (total o1 o0); auto. exfalso.
        eapply SUCC in H0. eapply (@lt_not_le o1 s); auto. eapply H.
  Qed.

  Lemma is_join_eq A (os: A -> t) o0 o1 (JOIN: is_join os o0):
    eq o0 o1 <-> is_join os o1.
  Proof.
    split; i.
    - econs.
      + i. transitivity o0.
        * eapply JOIN.
        * eapply H.
      + i. transitivity o0.
        * eapply H.
        * eapply JOIN. auto.
    - split.
      + eapply JOIN. eapply H.
      + eapply H. eapply JOIN.
  Qed.

  Definition O: t := build (False_rect _).

  Lemma O_bot o: le O o.
  Proof.
    destruct (total O o); auto. dependent destruction H. ss.
  Qed.

  Lemma O_is_O: is_O O.
  Proof.
    ii. destruct (total O o1); auto. dependent destruction H. ss.
  Qed.

  Definition S (o: t): t := build (unit_rect _ o).

  Lemma S_lt o: lt o (S o).
  Proof.
    eapply (build_upperbound (unit_rect _ o) tt).
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

  Lemma S_le_mon o0 o1:
    le o0 o1 <-> le (S o0) (S o1).
  Proof.
    split; i.
    - eapply S_spec. eapply le_lt_lt; eauto. eapply S_lt.
    - destruct (total o0 o1); auto. exfalso.
      eapply S_spec in H0. eapply lt_StrictOrder. eapply le_lt_lt.
      { eapply H. } eapply le_lt_lt.
      { eapply H0. }
      eapply S_lt.
  Qed.

  Lemma S_lt_mon o0 o1:
    lt o0 o1 <-> lt (S o0) (S o1).
  Proof.
    split ;i.
    - destruct (total (S o1) (S o0)); auto.
      erewrite <- S_le_mon in H0. exfalso. eapply lt_not_le; eauto.
    - destruct (total o1 o0); auto.
      erewrite S_le_mon in H0. exfalso. eapply lt_not_le; eauto.
  Qed.

  Section JOIN.
    Let le_lemma o0 B1 (os1: B1 -> t)
          (LE: forall B0 os0 (b0: B0)
                      (EQ: o0 = @build B0 os0),
              exists b1, le (os0 b0) (os1 b1))
    :
      le o0 (build os1).
    Proof.
      destruct o0. econs. i. exploit LE; eauto.
    Defined.

    Let T := Type.
    Variable A: T.
    Variable os: A -> t.
    Let Y: (A -> T) :=
      fun a: A =>
        match (os a) with
        | @build B _ => B
        end.

    Let X: T :=
      @sigT _ Y.

    Definition join: t.
    Proof.
      econs. instantiate (1:=X).
      ii. destruct X0. unfold Y in y.
      destruct (os x). eapply (os0 y).
    Defined.

    Lemma join_upperbound: forall a, le (os a) join.
    Proof.
      ii. unfold join. unfold X. unfold Y. eapply le_lemma. i.
      set (s:= @eq_rect_r t (build os0) (fun x => match x with
                                               | @build B _ => B
                                               end) b0 (os a) EQ).
      exists (existT _ a s).
      replace (os0 b0) with (match os a as t0 return (match t0 with
                                                      | @build B _ => B
                                                      end -> t) with
                             | @build A0 os1 => fun y : A0 => os1 y
                             end s); auto.
      { reflexivity. }
      unfold s. rewrite EQ. ss.
    Qed.

    Let build_fst_eq A0 A1 os0 os1 (EQ: @build A0 os0 = @build A1 os1):
      A0 = A1.
    Proof.
      inversion EQ. auto.
    Defined.

    Lemma join_supremum o (LE: forall a, le (os a) o):
      le join o.
    Proof.
      destruct o. econs. i. destruct a0; ss.
      specialize (LE x). remember (build os0). inv LE.
      specialize (LE0 (@eq_rect _ (os x) (fun t0 => match t0 return T with
                                                    | @build B _ => B
                                                    end) y _ (eq_sym H0))). des.
      exists (@eq_rect _ A2 id a1 A0 (build_fst_eq H1)).

      subst X Y. ss. destruct (os x).
      assert (os2 a1 = os0 (eq_rect A2 id a1 A0 (build_fst_eq H1))).
      { dependent destruction H1. ss. } rewrite <- H.
      assert ((os1
                 (eq_rect (build os3) (fun t0 : t => match t0 return T with
                                                  | @build B _ => B
                                                  end) y (build os1) (eq_sym H0))) =
              (os3 y)).
      { clear LE0 H. dependent destruction H0. dependent destruction H1. auto. }
      rewrite <- H2. auto.
    Qed.
  End JOIN.

  Lemma join_le A0 A1 (os0: A0 -> t) (os1: A1 -> t)
        (LE: forall a0, exists a1, le (os0 a0) (os1 a1))
    :
      le (join os0) (join os1).
  Proof.
    eapply join_supremum. i. specialize (LE a). des.
    etransitivity; eauto. eapply join_upperbound.
  Qed.

  Lemma join_is_join A (os: A -> t):
    is_join os (join os).
  Proof.
    econs.
    - eapply join_upperbound.
    - eapply join_supremum.
  Qed.

  Lemma limit_or_S o:
    (exists o0, is_S o0 o) \/
    (exists A (os: A -> t), is_join os o /\ open os).
  Proof.
    destruct o. destruct (classic (forall a0, exists a1, lt (os a0) (os a1))).
    - right. exists A, os. split; auto. split.
      + i. eapply lt_le. eapply build_upperbound.
      + i. eapply build_spec. i. specialize (H a). des.
        eapply lt_le_lt; eauto.
    - left. eapply not_all_ex_not in H. des.
      exists (os n). split.
      + eapply build_upperbound.
      + i. eapply build_spec. i. destruct (total (os a) (os n)); auto.
        * eapply le_lt_lt; eauto.
        * exfalso. eapply H; eauto.
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
      i. destruct (total (os a) o0); auto.
      eapply SUCC.(is_S_spec) in H.
      specialize (OPEN a). des.
      exfalso. eapply (@lt_not_le (os a) o); auto.
      eapply lt_le_lt; eauto. eapply JOIN.(is_join_upperbound). }
    i. eapply (@lt_not_le o0 o); auto. eapply SUCC.(is_S_lt).
  Qed.

  Lemma build_is_join A (os: A -> t) (OPEN: open os): is_join os (build os).
  Proof.
    econs.
    - i. eapply lt_le. eapply build_upperbound.
    - i. eapply build_spec. i. specialize (OPEN a). des.
      eapply lt_le_lt; eauto.
  Qed.

  Lemma ind
        (P: t -> Prop)
        (ZERO: forall o (ZERO: is_O o)
                      (HELPER: forall o' (LT: lt o' o), P o'), P o)
        (SUCC: forall o s (SUCC: is_S o s) (IH: P o)
                      (HELPER: forall o' (LT: lt o' s), P o'), P s)
        (LIMIT: forall A (os: A -> t) o (JOIN: is_join os o)
                       (INHABITED: inhabited A) (OPEN: open os)
                       (IH: forall a, P (os a))
                       (HELPER: forall o' (LT: lt o' o), P o'), P o)
    :
      forall o, P o.
  Proof.
    eapply well_founded_induction.
    { eapply lt_well_founded. }
    i. destruct (limit_or_S x).
    - des. eapply SUCC; eauto. eapply H. eapply H0.
    - des. destruct (classic (inhabited A)).
      + eapply LIMIT; eauto. i. eapply H.
        specialize (H1 a). des. eapply lt_le_lt; eauto. eapply H0.
      + eapply ZERO; eauto. ii. eapply H0.
        i. exfalso. eapply H2. eauto.
  Qed.

  Section REC.
    Variable D: Type.
    Variable dle: D -> D -> Prop.
    Variable djoin: forall A (ds: A -> D), D.
    Variable wf: D -> Prop.

    Let deq: D -> D -> Prop :=
      fun d0 d1 => dle d0 d1 /\ dle d1 d0.

    Variable base: D.
    Variable next: D -> D.

    Hypothesis dle_reflexive: forall d (WF: wf d), dle d d.
    Hypothesis dle_transitive: forall d1 d0 d2 (WF0: wf d0) (WF1: wf d1) (WF2: wf d2) (LE0: dle d0 d1) (LE1: dle d1 d2),
        dle d0 d2.

    Hypothesis djoin_upperbound: forall A (ds: A -> D) (a: A) (CHAIN: forall a0 a1, dle (ds a0) (ds a1) \/ dle (ds a1) (ds a0)) (WF: forall a, wf (ds a)), dle (ds a) (djoin ds).
    Hypothesis djoin_supremum: forall A (ds: A -> D) (d: D) (CHAIN: forall a0 a1, dle (ds a0) (ds a1) \/ dle (ds a1) (ds a0)) (WF: forall a, wf (ds a)) (WFD: wf d) (LE: forall a, dle (ds a) d), dle (djoin ds) d.
    Hypothesis djoin_wf: forall A (ds: A -> D) (CHAIN: forall a0 a1, dle (ds a0) (ds a1) \/ dle (ds a1) (ds a0)) (WF: forall a, wf (ds a)), wf (djoin ds).

    Hypothesis base_wf: wf base.
    Hypothesis next_wf: forall d (WF: wf d), wf (next d).

    Hypothesis next_le: forall d (WF: wf d), dle d (next d).
    Hypothesis next_eq: forall d0 d1 (WF0: wf d0) (WF1: wf d1) (EQ: deq d0 d1), deq (next d0) (next d1).

    Let dunion (d0 d1: D): D := djoin (fun b: bool => if b then d0 else d1).

    Fixpoint rec (o: t): D :=
      match o with
      | @build X xs =>
        dunion base (djoin (fun x => next (rec (xs x))))
      end.

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
      assert (CHAIN0:
                forall
                  A0 (os0: A0 -> t)
                  (LE: forall a0, exists a, le (os0 a0) (os a))
                  a0 a1,
                  dle (next (rec (os0 a0))) (next (rec (os0 a1))) \/ dle (next (rec (os0 a1))) (next (rec (os0 a0)))).
      { i. generalize (trichotomy (os0 a0) (os0 a1)). i. des.
        - eapply IHS0 in H; auto. left. eapply (@dle_transitive (rec (os0 a1))).
          + eapply next_wf. eapply IHS0; auto.
          + eapply IHS0; auto.
          + eapply next_wf. eapply IHS0; auto.
          + auto.
          + eapply next_le. eapply IHS0; auto.
        - hexploit (@next_eq (rec (os0 a0)) (rec (os0 a1))).
          + eapply IHS0; auto.
          + eapply IHS0; auto.
          + inv H. econs.
            * eapply IHS0; auto.
            * eapply IHS0; auto.
          + i. left. eapply H0.
        - eapply IHS0 in H; auto. right. eapply (@dle_transitive (rec (os0 a0))).
          + eapply next_wf. eapply IHS0; auto.
          + eapply IHS0; auto.
          + eapply next_wf. eapply IHS0; auto.
          + auto.
          + eapply next_le. eapply IHS0; auto.
      }
      assert (WF0:
                forall
                  A0 (os0: A0 -> t)
                  (LE: forall a0, exists a, le (os0 a0) (os a))
                  a,
                  wf (next (rec (os0 a)))).
      { i. eapply next_wf. eapply IHS0; eauto. }
      assert (CHAINU0:
                forall
                  A0 (os0: A0 -> t)
                  (LE: forall a0, exists a, le (os0 a0) (os a))
                  (b0 b1: bool),
                  dle (if b0 then base else djoin (fun x => next (rec (os0 x)))) (if b1 then base else djoin (fun x => next (rec (os0 x)))) \/
                  dle (if b1 then base else djoin (fun x => next (rec (os0 x)))) (if b0 then base else djoin (fun x => next (rec (os0 x))))).
      { i. assert (dle base (djoin (fun x => next (rec (os0 x)))) \/
                   dle (djoin (fun x => next (rec (os0 x)))) base).
        { destruct (classic (inhabited A0)).
          - destruct H as [a]. left.
            eapply (@dle_transitive (next (rec (os0 a)))); auto.
            + eapply (@dle_transitive (rec (os0 a))); auto.
              * eapply IHS0; eauto.
              * eapply IHS0; eauto.
              * eapply next_le. eapply IHS0; eauto.
            + eapply (djoin_upperbound (fun x => next (rec (os0 x))) a); auto.
          - right. eapply djoin_supremum; eauto. i. exfalso. eapply H; eauto.
        }
        destruct b0, b1; auto. des; auto.
      }
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
        - i. dependent destruction LE. ss. eapply djoin_supremum; eauto.
          i. destruct a.
          + unfold dunion.
            eapply (@djoin_upperbound _ (fun b: bool => if b then base else djoin (fun x => next (rec (os x)))) true); auto.
          + eapply (@dle_transitive (djoin (fun x => next (rec (os x))))); eauto.
            * eapply djoin_supremum; eauto. i. hexploit (LE a); eauto. i. des.
              eapply (@dle_transitive (next (rec (os a1)))); eauto.
              { eapply le_eq_or_lt in H. des.
                { eapply IHS0 in H; eauto.
                  eapply (@dle_transitive (rec (os a1))); eauto.
                  { eapply IHS0; eauto. }
                  { eapply next_le. eapply IHS0; eauto. }
                }
                { assert (deq (next (rec (os0 a))) (next (rec (os a1)))).
                  2: { eapply H0. }
                  eapply next_eq; eauto.
                  { eapply IHS0; eauto. }
                  { eapply IHS0; eauto. }
                  { inv H. econs.
                    { eapply IHS0; eauto. }
                    { eapply IHS0; eauto. }
                  }
                }
              }
              { eapply (@djoin_upperbound _ (fun x => next (rec (os x))) a1); eauto. }
            * eapply (@djoin_upperbound _  (fun b: bool => if b then base else djoin (fun x => next (rec (os x)))) false); auto.
        - eapply djoin_wf; eauto.
        - eapply (@djoin_upperbound _  (fun b: bool => if b then base else djoin (fun x => next (rec (os x)))) true); auto.
      }

      destruct H as [RECLE [WF BASE]]. splits; auto. i.
      destruct (classic (exists o1, lt o0 o1 /\ lt o1 (build os))).
      { des. hexploit (IH o1); eauto. i. des. eapply H2 in H.
        eapply (@dle_transitive (rec o1)); auto.
        { eapply IH in LT. des. auto. }
        eapply RECLE. eapply lt_le. auto.
      }
      { assert (exists a, eq o0 (os a)).
        { eapply NNPP. ii. eapply lt_not_le.
          { eapply LT. }
          eapply build_spec. i.
          destruct (trichotomy (os a) o0) as [|[|]]; auto.
          { exfalso. eapply H0. exists a. symmetry. auto. }
          { exfalso. eapply H. esplits; eauto. eapply build_upperbound. }
        }
        des.
        assert (deq (rec o0) (rec (os a))).
        { inv H0. econs.
          { eapply IH; eauto. eapply le_lt_lt; eauto. }
          { eapply IH; eauto. }
        }
        eapply next_eq in H1; eauto.
        { inv H1.
          eapply (@dle_transitive (next (rec (os a)))); auto.
          { eapply IH in LT. des. auto. }
          eapply (@dle_transitive (djoin (fun x => next (rec (os x))))); eauto.
          { eapply (@djoin_upperbound _  (fun x => next (rec (os x))) a); auto. }
          { eapply (@djoin_upperbound _  (fun b: bool => if b then base else djoin (fun x => next (rec (os x)))) false); auto. }
        }
        { eapply IH; eauto. }
        { eapply IH; eauto. eapply le_lt_lt; eauto. eapply H0. }
      }
    Qed.

    Lemma rec_le (o0 o1: t) (LE: le o0 o1): dle (rec o0) (rec o1).
    Proof.
      eapply rec_all; auto.
    Qed.

    Lemma rec_eq (o0 o1: t) (EQ: eq o0 o1): deq (rec o0) (rec o1).
    Proof.
      split.
      - eapply rec_le. eapply EQ.
      - eapply rec_le. eapply EQ.
    Qed.

    Lemma rec_lt (o0 o1: t) (LT: lt o0 o1): dle (next (rec o0)) (rec o1).
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
      eapply le_eq_or_lt in LE. des.
      - eapply rec_lt in LE. eapply (@dle_transitive (rec o1)); eauto.
      - eapply rec_eq in LE. eapply next_eq in LE; eauto. eapply LE.
    Qed.

    Let chain_helper X (xs: X -> t)
      :
        forall x0 x1, dle (next (rec (xs x0))) (next (rec (xs x1))) \/
                      dle (next (rec (xs x1))) (next (rec (xs x0))).
    Proof.
      i. destruct (total (xs x0) (xs x1)).
      - left. eapply rec_next_le. auto.
      - right. eapply lt_le in H. eapply rec_next_le. auto.
    Qed.

    Let wf_helper X (xs: X -> t)
      :
        forall x, wf (next (rec (xs x))).
    Proof.
      i. auto.
    Qed.

    Let chainu_helper X (xs: X -> t)
      :
        forall (b0 b1: bool),
          dle (if b0 then base else djoin (fun x => next (rec (xs x))))
              (if b1 then base else djoin (fun x => next (rec (xs x)))) \/
          dle (if b1 then base else djoin (fun x => next (rec (xs x))))
              (if b0 then base else djoin (fun x => next (rec (xs x)))).
    Proof.
      assert (dle base (djoin (fun x => next (rec (xs x)))) \/
              dle (djoin (fun x => next (rec (xs x)))) base).
      { destruct (classic (inhabited X)).
        - destruct H as [x]. left.
          eapply (@dle_transitive (next (rec (xs x)))); auto.
          + eapply (@dle_transitive (rec (xs x))); auto. eapply rec_le_base.
          + eapply (@djoin_upperbound _ (fun x0 => next (rec (xs x0))) x); auto.
        - right. eapply djoin_supremum; auto.
          i. exfalso. eapply H; eauto.
      }
      i. destruct b0, b1; auto. des; auto.
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
      - eapply (@djoin_upperbound _ (fun b: bool => if b then base else djoin (fun x => next (rec !))) true); auto.
    Qed.

    Lemma rec_is_O o (ZERO: is_O o): deq (rec o) base.
    Proof.
      hexploit (@rec_eq O o).
      { eapply is_O_eq; auto. eapply O_is_O. }
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
      - eapply (@dle_transitive (djoin (fun x => next (rec (unit_rect (fun _ : () => t) o x))))); auto.
        { eapply djoin_wf; auto. }
        + eapply (djoin_upperbound (fun x : () => next (rec (unit_rect (fun _ : () => t) o x))) tt); auto.
        + eapply (@djoin_upperbound _ (fun b: bool => if b then base else djoin (fun x => next (rec (unit_rect (fun _ : () => t) o x)))) false); auto.
    Qed.

    Lemma rec_is_S o s (SUCC: is_S o s): deq (rec s) (next (rec o)).
    Proof.
      hexploit (@rec_eq (S o) s).
      { eapply is_S_eq; eauto. eapply S_is_S. }
      i. inv H. split.
      - eapply (@dle_transitive (rec (S o))); auto. eapply rec_S.
      - eapply (@dle_transitive (rec (S o))); auto. eapply rec_S.
    Qed.

    Lemma rec_build A (os: A -> t)
          (INHABITED: inhabited A) (OPEN: open os)
      : deq (rec (build os)) (djoin (fun a => rec (os a))).
    Proof.
      assert (CHAINJOIN: forall a0 a1 : A, dle (rec (os a0)) (rec (os a1)) \/ dle (rec (os a1)) (rec (os a0))).
      { i. destruct (total (os a0) (os a1)).
        - left. eapply rec_le; auto.
        - right. eapply lt_le in H. eapply rec_le; auto.
      }
      destruct INHABITED as [a'].
      split; ss.
      - eapply djoin_supremum; auto. i. destruct a; auto.
        + eapply (@dle_transitive (rec (os a'))); auto.
          * eapply rec_le_base.
          * eapply (@djoin_upperbound _ (fun a : A => rec (os a)) a'); auto.
        + eapply djoin_supremum; auto. i.
          hexploit (OPEN a). i. des.
          eapply rec_lt in H; auto.
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

    Lemma rec_is_join A (os: A -> t) o
          (INHABITED: inhabited A) (OPEN: open os) (JOIN: is_join os o)
      : deq (rec o) (djoin (fun a => rec (os a))).
    Proof.
      assert (CHAINJOIN: forall a0 a1 : A, dle (rec (os a0)) (rec (os a1)) \/ dle (rec (os a1)) (rec (os a0))).
      { i. destruct (total (os a0) (os a1)).
        - left. eapply rec_le; auto.
        - right. eapply lt_le in H. eapply rec_le; auto.
      }
      hexploit (@rec_eq (build os) o).
      { eapply is_join_eq; eauto. eapply build_is_join; auto. }
      i. inv H. split.
      - eapply (@dle_transitive (rec (build os))); auto.
        eapply rec_build; auto.
      - eapply (@dle_transitive (rec (build os))); auto.
        eapply rec_build; auto.
    Qed.

    Lemma rec_join A (os: A -> t)
          (INHABITED: inhabited A) (OPEN: open os)
      : deq (rec (join os)) (djoin (fun a => rec (os a))).
    Proof.
      eapply rec_is_join; auto. eapply join_is_join.
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

    Lemma rec_mon o: dle (rec djoin base0 next0 o) (rec djoin base1 next1 o).
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

    Definition orec: t -> t := rec join base next.

    Hypothesis next_le: forall o, le o (next o).
    Hypothesis next_eq: forall o0 o1 (EQ: eq o0 o1), eq (next o0) (next o1).

    Let wf: t -> Prop := fun _ => True.

    Let dle_reflexive: forall d (WF: wf d), le d d .
    Proof. i. reflexivity. Qed.

    Let dle_transitive: forall d1 d0 d2 (WF0: wf d0) (WF1: wf d1) (WF2: wf d2) (LE0: le d0 d1) (LE1: le d1 d2),
        le d0 d2.
    Proof. i. transitivity d1; eauto. Qed.

    Let djoin_upperbound: forall A (ds: A -> t) (a: A) (CHAIN: forall a0 a1, le (ds a0) (ds a1) \/ le (ds a1) (ds a0)) (WF: forall a, wf (ds a)), le (ds a) (join ds).
    Proof. i. eapply join_upperbound. Qed.
    Let djoin_supremum: forall A (ds: A -> t) (d: t) (CHAIN: forall a0 a1, le (ds a0) (ds a1) \/ le (ds a1) (ds a0)) (WF: forall a, wf (ds a)) (WFD: wf d) (LE: forall a, le (ds a) d), le (join ds) d.
    Proof. i. eapply join_supremum. auto. Qed.

    Let djoin_wf: forall A (ds: A -> t) (CHAIN: forall a0 a1, le (ds a0) (ds a1) \/ le (ds a1) (ds a0)) (WF: forall a, wf (ds a)), wf (join ds).
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
      unfold orec. eapply rec_le with (wf:=wf); auto. i. eapply next_eq. auto.
    Qed.

    Lemma eq_orec (o0 o1: t) (EQ: eq o0 o1): eq (orec o0) (orec o1).
    Proof.
      unfold orec. eapply rec_eq with (wf:=wf); auto. i. eapply next_eq. auto.
    Qed.

    Lemma orec_is_O (o: t) (ZERO: is_O o): eq (orec o) base.
    Proof.
      unfold orec. eapply rec_is_O with (wf:=wf); auto. i. eapply next_eq. auto.
    Qed.

    Lemma orec_is_S o s (SUCC: is_S o s): eq (orec s) (next (orec o)).
    Proof.
      unfold orec. eapply rec_is_S with (wf:=wf); auto.
      i. eapply next_eq. auto.
    Qed.

    Lemma orec_is_join A (os: A -> t) o
          (INHABITED: inhabited A) (OPEN: open os) (JOIN: is_join os o)
      : eq (orec o) (join (fun a => orec (os a))).
    Proof.
      unfold orec. eapply rec_is_join with (wf:=wf); auto.
      i. eapply next_eq. auto.
    Qed.
  End OREC.

  Definition add (o0: t): forall (o1: t), t := orec o0 S.
  Definition mult (o0: t): forall (o1: t), t := orec O (flip add o0).
  Definition expn (o0: t): forall (o1: t), t := orec (S O) (flip mult o0).

  Fixpoint from_nat (n: nat): t :=
    match n with
    | 0 => O
    | Datatypes.S n' => S (from_nat n')
    end.

  Definition omega: t := join from_nat.

  Definition is_hartogs A (h: t): Prop :=
    is_meet (fun o => forall (R: A -> A -> Prop) (WF: well_founded R),
                 ~ eq (from_wf_set WF) o) h.

  Lemma hartogs_exists A:
    exists h, is_hartogs A h.
  Proof.
    eapply meet_exists.
    exists (@build
              (@sig (A -> A -> Prop) (@well_founded A))
              (fun rwf => from_wf_set (proj2_sig rwf))).
    ii. eapply lt_StrictOrder. eapply lt_eq_lt; [eauto|].
    eapply (@build_upperbound _ (fun rwf => from_wf_set (proj2_sig rwf)) (@exist _ _ R WF)).
  Qed.

  Section CARDINAL.
    Variable X: Type.
    Record subX: Type :=
      subX_mk {
          P: X -> Prop;
          R: X -> X -> Prop;
        }.

    Record subX_wf (X': subX): Type :=
      subX_wf_intro {
          sound: forall a0 a1 (LT: X'.(R) a0 a1), X'.(P) a0 /\ X'.(P) a1;
          complete: forall a0 a1 (IN0: X'.(P) a0) (IN1: X'.(P) a1),
              X'.(R) a0 a1 \/ a0 = a1 \/ X'.(R) a1 a0;
          wfo: well_founded X'.(R);
        }.

    Record leX (s0 s1: subX): Prop :=
      leX_intro {
          P_incl: forall a (IN: s0.(P) a), s1.(P) a;
          R_incl: forall a0 a1 (LT: s0.(R) a0 a1), s1.(R) a0 a1;
          no_insert: forall a0 a1 (IN: s0.(P) a1), s1.(R) a0 a1 <-> s0.(R) a0 a1;
        }.

    Let joinX A (Xs: A -> subX): subX :=
      subX_mk (fun x => exists a, (Xs a).(P) x) (fun x0 x1 => exists a, (Xs a).(R) x0 x1).

    Let base: subX := subX_mk (fun _ => False) (fun _ _ => False).

    Let leX_reflexive: forall d (WF: subX_wf d), leX d d.
    Proof.
      i. econs; eauto.
    Qed.

    Let leX_transitive: forall d1 d0 d2 (WF0: subX_wf d0) (WF1: subX_wf d1) (WF2: subX_wf d2) (LE0: leX d0 d1) (LE1: leX d1 d2),
        leX d0 d2.
    Proof.
      i. inv LE0. inv LE1. econs; eauto.
      i. rewrite no_insert1; eauto.
    Qed.

    Let joinX_upperbound: forall A (ds: A -> subX) (a: A) (CHAIN: forall a0 a1, leX (ds a0) (ds a1) \/ leX (ds a1) (ds a0)) (WF: forall a, subX_wf (ds a)), leX (ds a) (joinX ds).
    Proof.
      i. econs; ss; eauto. i. split; i.
      - des. destruct (CHAIN a a2).
        + eapply H0 in H; eauto.
        + eapply H0. eauto.
      - eauto.
    Qed.

    Let joinX_supremum: forall A (ds: A -> subX) (d: subX) (CHAIN: forall a0 a1, leX (ds a0) (ds a1) \/ leX (ds a1) (ds a0)) (WF: forall a, subX_wf (ds a)) (WFD: subX_wf d) (LE: forall a, leX (ds a) d), leX (joinX ds) d.
    Proof.
      i. econs; ss.
      - i. des. eapply LE in IN. auto.
      - i. des. eapply LE in LT. auto.
      - i. des. split; i.
        + eapply LE in H; eauto.
        + des. eapply LE; eauto.
    Qed.

    Let joinX_wf: forall A (ds: A -> subX) (CHAIN: forall a0 a1, leX (ds a0) (ds a1) \/ leX (ds a1) (ds a0)) (WF: forall a, subX_wf (ds a)), subX_wf (joinX ds).
    Proof.
      i. econs; ss.
      - i. des. eapply WF in LT. des. eauto.
      - i. des. destruct (CHAIN a2 a).
        + eapply H in IN0. hexploit ((WF a).(complete) a0 a1); eauto.
          i. des; eauto.
        + eapply H in IN1. hexploit ((WF a2).(complete) a0 a1); eauto.
          i. des; eauto.
      - intros x1. econs. intros x0. i. des.
        assert (ACC: Acc (R (ds a)) x0).
        { eapply WF. }
        eapply WF in H. des. clear H0.
        revert H. induction ACC. i.
        econs. i. des.
        assert (LT: R (ds a) y x).
        { destruct (CHAIN a a0).
          - eapply H3 in H2; auto.
          - eapply H3 in H2; auto.
        }
        eapply H0; eauto. eapply WF in LT. des. auto.
    Qed.

    Let base_wf: subX_wf base.
    Proof.
      econs; ss.
    Qed.

    Section NEXT.
      Hypothesis next: subX -> subX.

      Hypothesis next_wf: forall d (WF: subX_wf d), subX_wf (next d).
      Hypothesis next_le: forall d (WF: subX_wf d), leX d (next d).
      Hypothesis next_exhausted: forall d (WF: subX_wf d),
          (forall x, d.(P) x) \/
          (exists x, (next d).(P) x /\ ~ d.(P) x)
      .

      Let next_eq: forall d0 d1 (WF0: subX_wf d0) (WF1: subX_wf d1) (EQ: leX d0 d1 /\ leX d1 d0), leX (next d0) (next d1) /\ leX (next d1) (next d0).
      Proof.
        i. assert (d0 = d1).
        { des. destruct d0, d1. f_equal.
          - extensionality x. eapply propositional_extensionality. split.
            + eapply EQ.
            + eapply EQ0.
          - extensionality x0. extensionality x1.
            eapply propositional_extensionality. split.
            + eapply EQ.
            + eapply EQ0.
        }
        subst. split; auto.
      Qed.

      Let hartogs_exhausted h
            (HARTOGS: is_hartogs X h)
        :
          forall x, (rec joinX base next h).(P) x.
      Proof.
      Admitted.

      Lemma choice_then_well_ordering_principle
        :
          exists (R: X -> X -> Prop),
            well_founded R /\
            (forall x0 x1, R x0 x1 \/ x0 = x1 \/ R x1 x0).
      Proof.
        hexploit (hartogs_exists X). i. des.
        exists (rec joinX base next h).(R).
        assert (WF: subX_wf (rec joinX base next h)).
        { hexploit (@rec_wf _ leX joinX subX_wf base next); eauto. }
        split.
        - eapply WF.
        - i. eapply WF.
          + eapply hartogs_exhausted; auto.
          + eapply hartogs_exhausted; auto.
      Qed.
    End NEXT.

    Lemma well_ordering_principle
      :
        exists (R: X -> X -> Prop),
          well_founded R /\
          (forall x0 x1, R x0 x1 \/ x0 = x1 \/ R x1 x0).
    Proof.
      assert (exists (next: subX -> subX),
                 (forall d (WF: subX_wf d), subX_wf (next d)) /\
                 (forall d (WF: subX_wf d), leX d (next d)) /\
                 (forall d (WF: subX_wf d),
                     (forall x, d.(P) x) \/
                     (exists x, (next d).(P) x /\ ~ d.(P) x))).
      { admit. }
      des. eapply choice_then_well_ordering_principle; eauto.
    Admitted.
  End CARDINAL.

End Ordinal.

Module iProp.
  Definition t := Ordinal.t -> Prop.
  Definition le (P0 P1: t): Prop := forall i (IN: P0 i), P1 i.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. eauto.
  Qed.
  Next Obligation.
  Proof.
    ii. eauto.
  Qed.

  Global Program Instance le_Antisymmetric: Antisymmetric _ eq le.
  Next Obligation.
  Proof.
    extensionality i. eapply propositional_extensionality. eauto.
  Qed.

  Definition ge := flip le.

  Definition closed (P: t): Prop :=
    forall i0 i1 (IN: P i0) (LE: Ordinal.le i0 i1), P i1.

  Definition next (P: t): t :=
    fun i1 => exists i0, P i0 /\ Ordinal.lt i0 i1.

  Lemma next_incl P (CLOSED: closed P): le (next P) P.
  Proof.
    unfold next in *. ii. des. eapply CLOSED; eauto. eapply Ordinal.lt_le; eauto.
  Qed.

  Lemma next_mon P0 P1 (LE: le P0 P1): le (next P0) (next P1).
  Proof.
    unfold next in *. ii. des. exists i0; eauto.
  Qed.

  Definition meet A (Ps: A -> t): t :=
    fun i => forall a, Ps a i.

  Lemma meet_lowerbound A (Ps: A -> t) a:
      le (meet Ps) (Ps a).
  Proof.
    ii. eauto.
  Qed.

  Lemma meet_infimum A (Ps: A -> t) P
        (LE: forall a, le P (Ps a))
    :
      le P (meet Ps).
  Proof.
    ii. eapply LE in IN; eauto.
  Qed.

  Lemma meet_closed A (Ps: A -> t) (CLOSED: forall a, closed (Ps a)): closed (meet Ps).
  Proof.
    unfold meet. ii. eapply CLOSED; eauto.
  Qed.

  Definition top: t := meet (False_rect _).

  Lemma top_spec P: le P top.
  Proof.
    eapply meet_infimum. i. ss.
  Qed.

  Definition next_o (P: t) (o: Ordinal.t): t := Ordinal.rec meet P next o.

  Lemma next_o_le (P: t) (o0 o1: Ordinal.t) (LE: Ordinal.le o0 o1):
    le (next_o P o1) (next_o P o0).
  Proof.
    eapply (@Ordinal.le_rec t ge meet P next); auto.
    - eapply flip_PreOrder. eapply le_PreOrder.
    - i. eapply meet_lowerbound.
    - i. eapply meet_infimum. auto.
    - i. eapply next_mon; auto.
  Qed.

  Lemma next_o_eq (P: t) (o0 o1: Ordinal.t) (EQ: Ordinal.eq o0 o1):
    next_o P o1 = next_o P o0.
  Proof.
    eapply le_Antisymmetric.
    - eapply next_o_le. eapply EQ.
    - eapply next_o_le. eapply EQ.
  Qed.

  Lemma next_o_mon P0 P1 (LE: le P0 P1) o: le (next_o P0 o) (next_o P1 o).
  Proof.
    revert o P0 P1 LE. induction o. i. ss.
    eapply meet_infimum. i. etransitivity; [eapply (meet_lowerbound a)|].
    destruct a; auto.
    eapply meet_infimum. i. etransitivity; [eapply (meet_lowerbound a)|].
    eapply next_mon. eauto.
  Qed.
End iProp.

  (* Definition bot: t := join (False_rect _). *)

  (* Lemma bot_spec P: le bot P. *)
  (* Proof. *)
  (*   eapply join_supremum. i. ss. *)
  (* Qed. *)

  (* Definition future (P: t): t := *)
  (*   fun i1 => exists i0, P i0. *)

  (* Lemma future_mon P0 P1 (LE: le P0 P1): le (future P0) (future P1). *)
  (* Proof. *)
  (*   unfold future in *. ii. des. eauto. *)
  (* Qed. *)

  (* Lemma future_incl P: le P (future P). *)
  (* Proof. *)
  (*   unfold future. ii. eauto. *)
  (* Qed. *)

  (* Lemma meet_mon A Ps0 Ps1 (LE: forall (a: A), le (Ps0 a) (Ps1 a)): le (meet Ps0) (meet Ps1). *)
  (* Proof. *)
  (*   unfold meet in *. ii. eapply LE; eauto. *)
  (* Qed. *)

  (* Definition join A (Ps: A -> t): t := *)
  (*   fun i => exists a, Ps a i. *)

  (* Lemma join_mon A Ps0 Ps1 (LE: forall (a: A), le (Ps0 a) (Ps1 a)): le (join Ps0) (join Ps1). *)
  (* Proof. *)
  (*   unfold join in *. ii. des. eapply LE in IN. eauto. *)
  (* Qed. *)

  (* Lemma join_upperbound A (Ps: A -> t) a *)
  (*   : *)
  (*     le (Ps a) (join Ps). *)
  (* Proof. *)
  (*   unfold join. ii. eauto. *)
  (* Qed. *)

  (* Lemma join_supremum A (Ps: A -> t) P *)
  (*       (LE: forall a, le (Ps a) P) *)
  (*   : *)
  (*     le (join Ps) P. *)
  (* Proof. *)
  (*   unfold join. ii. des. eapply LE; eauto. *)
  (* Qed. *)

  (* Lemma meet_meet A (B: A -> Type) (k: forall a (b: B a), t) *)
  (*   : *)
  (*     meet (fun a => meet (k a)) = *)
  (*     meet (fun (ab: sigT B) => let (a, b) := ab in k a b). *)
  (* Proof. *)
  (*   eapply le_Antisymmetric. *)
  (*   - ii. destruct a as [a b]. eapply IN; eauto. *)
  (*   - ii. specialize (IN (existT _ a a0)). eauto. *)
  (* Qed. *)

(*   Lemma meet_join A (B: A -> Type) (k: forall a (b: B a), t) *)
(*     : *)
(*       meet (fun a => join (k a)) = *)
(*       join (fun (f: forall a, B a) => meet (fun a => k a (f a))). *)
(*   Proof. *)
(*     eapply le_Antisymmetric. *)
(*     - unfold join, meet. ii. eapply forall_exists_commute in IN; eauto. *)
(*     - unfold join, meet. ii. revert a. eapply forall_exists_commute_rev; eauto. *)
(*   Qed. *)

(*   Lemma join_meet A (B: A -> Type) (k: forall a (b: B a), t) *)
(*     : *)
(*       join (fun a => meet (k a)) = *)
(*       meet (fun (f: forall a, B a) => join (fun a => k a (f a))). *)
(*   Proof. *)
(*     eapply le_Antisymmetric. *)
(*     - unfold join, meet. ii. eapply exists_forall_commute in IN; eauto. *)
(*     - unfold join, meet. ii. eapply exists_forall_commute_rev; eauto. *)
(*   Qed. *)

(*   Lemma join_join A (B: A -> Type) (k: forall a (b: B a), t) *)
(*     : *)
(*       join (fun a => join (k a)) = *)
(*       join (fun (ab: sigT B) => let (a, b) := ab in k a b). *)
(*   Proof. *)
(*     unfold join. eapply le_Antisymmetric. *)
(*     - ii. des. exists (existT _ a a0). eauto. *)
(*     - ii. des. destruct a as [a b]. eauto. *)
(*   Qed. *)

(*   Lemma join_next A k *)
(*         (INHABITED: inhabited A) *)
(*     : *)
(*       join (fun a: A => next (k a)) = next (join k). *)
(*   Proof. *)
(*     destruct INHABITED. unfold next, join. *)
(*     eapply le_Antisymmetric. *)
(*     - ii. des. exists i0. esplits; eauto. *)
(*     - ii. des. esplits; eauto. *)
(*   Qed. *)

(*   Definition upper (o0: Index.t): t := *)
(*     fun o1 => Index.le o0 o1. *)

(*   Lemma next_upper o: upper (Index.S o) = next (upper o). *)
(*   Proof. *)
(*     unfold next, upper. eapply le_Antisymmetric. *)
(*     - ii. exists o. splits. *)
(*       + reflexivity. *)
(*       + eapply Index.lt_le_lt. *)
(*         * eapply Index.S_lt. *)
(*         * eauto. *)
(*     - ii. des. eapply Index.S_spec in IN0. *)
(*       etransitivity; eauto. eapply Index.S_spec. *)
(*       eapply Index.le_lt_lt; eauto. eapply Index.S_lt. *)
(*   Qed. *)

(*   Lemma meet_upper A (k: A -> Index.t): meet (fun a => upper (k a)) = upper (Index.join k). *)
(*   Proof. *)
(*     unfold meet, upper. eapply le_Antisymmetric. *)
(*     - ii. eapply Index.join_supremum; eauto. *)
(*     - ii. etransitivity. *)
(*       + eapply Index.join_upperbound; eauto. *)
(*       + auto. *)
(*   Qed. *)

(*   Lemma future_upper o: future (upper o) = upper Index.O. *)
(*   Proof. *)
(*     unfold future, upper. eapply le_Antisymmetric. *)
(*     - ii. eapply Index.O_bot. *)
(*     - ii. exists o. reflexivity. *)
(*   Qed. *)

(*   Lemma join_upper A (k: A -> Index.t) (INHABITED: inhabited A): *)
(*     exists o, join (fun a => upper (k a)) = upper o /\ Index.set_meet k o. *)
(*   Proof. *)
(*     unfold join, upper. *)
(*     exploit Index.set_meet_exists; eauto. i. des. esplits; eauto. clear INHABITED. *)
(*     eapply le_Antisymmetric. *)
(*     - ii. des. destruct x0. des. clarify. *)
(*       hexploit (H0 (k a)); eauto. i. etransitivity; eauto. *)
(*     - ii. destruct x0. des. clarify. eauto. *)
(*   Qed. *)

(*   Lemma closed_upper P (CLOSED: closed P) *)


(*     - ii. eapply *)


(*         in IN. eauto. *)
(*       { *)

(*       eapply Index.join_upperbound. *)

(*       des. etransitivity; eauto. eapply Index.join_upperbound. *)

(*       esplits; eauto. *)

(*       exists o. splits. *)
(*       + reflexivity. *)
(*       + eapply Index.lt_le_lt. *)
(*         * eapply Index.S_lt. *)
(*         * eauto. *)
(*     - ii. des. eapply Index.S_spec in IN0. *)
(*       etransitivity; eauto. eapply Index.S_spec. *)
(*       eapply Index.le_lt_lt; eauto. eapply Index.S_lt. *)

(*                                            next (join k)) = *)

(*                                    next (join k) = upper (Index.S o). *)
(*   Proof. *)
(*     unfold next, upper. eapply le_Antisymmetric. *)
(*     - ii. des. eapply Index.S_spec in IN0. *)
(*       etransitivity; eauto. eapply Index.S_spec. *)
(*       eapply Index.le_lt_lt; eauto. eapply Index.S_lt. *)
(*     - ii. exists o. splits. *)
(*       + reflexivity. *)
(*       + eapply Index.lt_le_lt. *)
(*         * eapply Index.S_lt. *)
(*         * eauto. *)
(*   Qed. *)

(*   Lemma upper_closed o: closed (upper o). *)
(*   Proof. *)
(*     ii. eapply LE. *)

(*   Definition closure (P: t): t := *)
(*     fun i1 => exists i0, P i0 /\ Index.le i0 i1. *)

(*   Lemma next_closed P: closed (next P). *)
(*   Proof. *)
(*     unfold closed, next in *. ii. des. esplits; eauto. eapply Index.lt_le_lt; eauto. *)
(*   Qed. *)

(*   Lemma future_closed P: closed (future P). *)
(*     unfold closed, future in *. ii. des. esplits; eauto. *)
(*   Qed. *)

(*   Lemma closure_closed P: closed (closure P). *)
(*   Proof. *)
(*     unfold closure, closed. i. des. esplits; eauto. etransitivity; eauto. *)
(*   Qed. *)

(*   Lemma closure_mon P0 P1 (LE: le P0 P1): *)
(*     le (closure P0) (closure P1). *)
(*   Proof. *)
(*     unfold closure. ii. des. esplits; eauto. *)
(*   Qed. *)

(*   Lemma closure_incl P: le P (closure P). *)
(*   Proof. *)
(*     unfold closure. ii. esplits; eauto. reflexivity. *)
(*   Qed. *)

(*   Lemma closed_closure P (CLOSED: closed P): closure P = P. *)
(*   Proof. *)
(*     eapply le_Antisymmetric. *)
(*     - ii. unfold closure in *. des. eapply CLOSED; eauto. *)
(*     - eapply closure_incl. *)
(*   Qed. *)

(*   Lemma join_closed A (Ps: A -> t) (CLOSED: forall a, closed (Ps a)): closed (join Ps). *)
(*   Proof. *)
(*     unfold join. ii. des. esplits; eauto. eapply CLOSED; eauto. *)
(*   Qed. *)

(*   Lemma top_closed: closed top. *)
(*   Proof. *)
(*     eapply meet_closed; eauto. i. ss. *)
(*   Qed. *)

(*   Lemma bot_closed: closed bot. *)
(*   Proof. *)
(*     eapply join_closed; eauto. i. ss. *)
(*   Qed. *)

(*   Lemma join_empty A k *)
(*         (INHABITED: ~ inhabited A) *)
(*     : *)
(*       @join A k = bot. *)
(*   Proof. *)
(*     eapply le_Antisymmetric. *)
(*     - eapply join_supremum. i. exfalso. eapply INHABITED. econs; eauto. *)
(*     - eapply bot_spec. *)
(*   Qed. *)

(*   Lemma meet_empty A k *)
(*         (INHABITED: ~ inhabited A) *)
(*     : *)
(*       @meet A k = top. *)
(*   Proof. *)
(*     eapply le_Antisymmetric. *)
(*     - eapply top_spec. *)
(*     - eapply meet_infimum. i. exfalso. eapply INHABITED. econs; eauto. *)
(*   Qed. *)

(*   Lemma next_meet A k *)
(*     : *)
(*       le (next (meet k)) (meet (fun a: A => next (k a))). *)
(*   Proof. *)
(*     unfold next. ii. des. exists i0. splits; auto. *)
(*   Qed. *)

(*   Lemma meet_next A k (CLOSED: forall a, closed (k a)) *)
(*     : *)
(*       le (meet (fun a: A => next (k a))) (next (meet k)) . *)
(*   Proof. *)
(*     unfold next. ii. des. exists i0. splits; auto. *)
(*   Qed. *)

(*   Lemma next_future P: future (next P) = future P. *)
(*   Proof. *)
(*     unfold next, future. eapply le_Antisymmetric. *)
(*     - ii. des. esplits; eauto. *)
(*     - ii. des. esplits; eauto. eapply (Index.S_lt). *)
(*   Qed. *)

(*   Lemma future_future P: future (future P) = future P. *)
(*   Proof. *)
(*     eapply le_Antisymmetric. *)
(*     - unfold future. ii. des. esplits; eauto. *)
(*     - eapply future_incl; eauto. *)
(*   Qed. *)

(*   Lemma join_future A k *)
(*     : *)
(*       join (fun a: A => future (k a)) = future (join k). *)
(*   Proof. *)
(*     unfold join, future. eapply le_Antisymmetric. *)
(*     - ii. des. esplits; eauto. *)
(*     - ii. des. esplits; eauto. *)
(*   Qed. *)

(*   Lemma future_meet A k *)
(*     : *)
(*       le (future (meet k)) (meet (fun a: A => future (k a))). *)
(*   Proof. *)
(*     unfold future. ii. des. esplits; eauto. *)
(*   Qed. *)

(*   Lemma meet_future A k (CLOSED: forall a, closed (k a)) *)
(*     : *)
(*       meet (fun a: A => future (k a)) = future (meet k). *)
(*   Proof. *)
(*     unfold meet, future. eapply le_Antisymmetric. *)
(*     - ii. eapply choice in IN. des. *)
(*       exists (Index.join f). i. eapply CLOSED; eauto. eapply Index.join_upperbound. *)
(*     - eapply future_meet. *)
(*   Qed. *)

(*   Fixpoint next_n (P: t) (n: nat): t := *)
(*     match n with *)
(*     | S n' => next (next_n P n') *)
(*     | 0 => P *)
(*     end. *)

(*   Lemma next_n_mon P0 P1 (LE: le P0 P1) n: le (next_n P0 n) (next_n P1 n). *)
(*   Proof. *)
(*     induction n; ss. eapply next_mon; eauto. *)
(*   Qed. *)

(*   Lemma next_n_closed P (CLOSED: closed P) n: closed (next_n P n). *)
(*   Proof. *)
(*     destruct n; ss. eapply next_closed. *)
(*   Qed. *)

(*   Lemma next_n_incl P (CLOSED: closed P) n: le (next_n P n) P. *)
(*   Proof. *)
(*     induction n; ss. etransitivity; eauto. *)
(*     eapply next_incl; eauto. eapply next_n_closed; eauto. *)
(*   Qed. *)

(*   Lemma join_next_n A k n *)
(*         (INHABITED: inhabited A) *)
(*     : *)
(*       join (fun a: A => next_n (k a) n) = next_n (join k) n. *)
(*   Proof. *)
(*     induction n; ss. *)
(*     erewrite join_next; eauto. *)
(*     erewrite IHn. auto. *)
(*   Qed. *)

(*   Lemma next_n_meet A k n *)
(*     : *)
(*       le (next_n (meet k) n) (meet (fun a: A => next_n (k a) n)). *)
(*   Proof. *)
(*     induction n; ss. etransitivity. *)
(*     - eapply next_mon; eauto. *)
(*     - eapply next_meet; eauto. *)
(*   Qed. *)

(*   Lemma next_n_future P n: future (next_n P n) = future P. *)
(*   Proof. *)
(*     induction n; ss. erewrite next_future; eauto. *)
(*   Qed. *)

(*   Lemma next_n_next P n: next_n (next P) n = next (next_n P n). *)
(*   Proof. *)
(*     induction n; ss. erewrite IHn. ss. *)
(*   Qed. *)

(*   Definition next_omega P: t := meet (next_n P). *)

(*   Lemma next_omega_mon P0 P1 (LE: le P0 P1): le (next_omega P0) (next_omega P1). *)
(*   Proof. *)
(*     eapply meet_mon; eauto. i. eapply next_n_mon; eauto. *)
(*   Qed. *)

(*   Lemma next_omega_closed P (CLOSED: closed P): closed (next_omega P). *)
(*   Proof. *)
(*     eapply meet_closed. i. eapply next_n_closed; eauto. *)
(*   Qed. *)

(*   Lemma next_omega_incl P (CLOSED: closed P): le (next_omega P) P. *)
(*   Proof. *)
(*     eapply (@meet_lowerbound nat (next_n P) 0). *)
(*   Qed. *)

(*   Lemma next_omega_next P (CLOSED: closed P): next_omega (next P) = next_omega P. *)
(*   Proof. *)
(*     eapply le_Antisymmetric. *)
(*     - eapply meet_infimum. i. etransitivity. *)
(*       + eapply (@meet_lowerbound nat (next_n (next P)) a). *)
(*       + ss. erewrite next_n_next. eapply next_incl. *)
(*         eapply next_n_closed; auto. *)
(*     - eapply meet_infimum. i. etransitivity. *)
(*       + eapply (@meet_lowerbound nat (next_n P) (S a)). *)
(*       + erewrite next_n_next. reflexivity. *)
(*   Qed. *)

(*   Lemma next_omega_future P (CLOSED: closed P): future (next_omega P) = future P. *)
(*   Proof. *)
(*     eapply le_Antisymmetric. *)
(*     - unfold next_omega. erewrite future_meet. etransitivity. *)
(*       + eapply meet_lowerbound. *)
(*       + instantiate (1:=0). ss. *)
(*     - unfold next_omega. erewrite <- meet_future. *)
(*       + eapply meet_infimum. i. rewrite next_n_future. reflexivity. *)
(*       + i. eapply next_n_closed; eauto. *)
(*   Qed. *)

(*   Lemma next_omega_meet A k *)
(*     : *)
(*       le (next_omega (meet k)) (meet (fun a: A => next_omega (k a))). *)
(*   Proof. *)
(*     eapply meet_infimum. i. eapply meet_infimum. i. etransitivity. *)
(*     - eapply meet_lowerbound. *)
(*     - etransitivity. *)
(*       + eapply next_n_meet. *)
(*       +  ss. *)
(*   Qed. *)

(*   Lemma join_next_omega A k *)
(*     : *)
(*       le (join (fun a: A => next_omega (k a))) (next_omega (join k)). *)
(*   Proof. *)
(*     destruct (classic (inhabited A)). *)
(*     - unfold next_omega. ii. erewrite <- join_next_n; eauto. *)
(*       unfold join in *. des. exists a0. eauto. *)
(*     - ii. destruct IN. exfalso. eauto. *)
(*   Qed. *)

(*   Lemma next_omega_join A k *)
(*     : *)
(*       join (fun a: A => next_omega (k a)) = next_omega (join k). *)
(*   Proof. *)
(*     unfold next_omega. eapply le_Antisymmetric. *)
(*     - eapply join_next_omega; auto. *)
(*     - destruct (classic (inhabited A)). *)
(*       2: { ii. specialize (IN 0). ss. destruct IN. exfalso. eapply H; eauto. } *)
(*       ii. *)

(*       replace (next_n (join k)) with (fun n => join (fun a => next_n (k a) n)) in IN. *)
(*       2: { extensionality n. erewrite join_next_n; eauto. } *)
(*       eapply join_mon. *)
(*       + *)


(*         next_n_meet *)
(*         eapply next_omega_meet. *)

(*       erewrite join_meet. ii. erewrite <- join_next_n. *)

(* join_next_n *)
(*      : forall (A : Type) (k : A -> t) (n : nat), *)
(*        inhabited A -> join (fun a : A => next_n (k a) n) = next_n (join k) n *)


(*       destruct H. *)
(*       unfold join. eapply NNPP. ii. *)

(*       specialize ( *)

(*       exp *)

(*       auto. *)


(*       { admit. } *)
(*       { exten *)



(*       eapply meet_mon in IN. *)
(*       2: { instantiate (1:=fun n => next_n (join k) n). i. ss. } *)
(*       setoid_rewrite <- join_next_n in IN. *)

(*       r *)

(*             join_next_n *)
(*      : forall (A : Type) (k : A -> t) (n : nat), *)
(*        inhabited A -> join (fun a : A => next_n (k a) n) = next_n (join k) n *)


(*       un *)

(*       erewrite join_meet in IN. specialie ( *)

(*       ). *)


(*       erewrite join_meet. *)



(*     erewrite <- (join_next_n k). *)

(*     unfold meet. *)

(*   Lemma meet_next_n A k n *)
(*         (INHABITED: inhabited A) *)
(*         (CLOSED: forall a, closed (k a)) *)
(*     : *)
(*       le (next_n (meet k) n) (meet (fun a: A => next_n (k a) n)). *)
(*   Proof. *)
(*     induction n; ss. etransitivity. *)
(*     - eapply next_mon; eauto. *)
(*     - eapply meet_next; eauto. *)
(*   Qed. *)


(*     f_equal. *)

(*     induction n; ss. *)
(*     erewrite join_next; eauto. *)
(*     erewrite IHn. auto. *)
(*   Qed. *)

(* next_omega next *)

(*   L *)
