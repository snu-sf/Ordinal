Require Import sflib.

Require Import Coq.Classes.RelationClasses Coq.Relations.Relation_Operators Coq.Classes.Morphisms. (* TODO: Use Morphisms *)
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.
Set Primitive Projections.

Lemma clos_trans_well_founded
      A (R: A -> A -> Prop) (WF: well_founded R)
  :
    well_founded (clos_trans_n1 _ R).
Proof.
  ii. hexploit (well_founded_induction WF (fun a1 => forall a0 (LT: clos_trans_n1 A R a0 a1 \/ a0 = a1), Acc (clos_trans_n1 A R) a0)).
  { clear a. intros a1 IH. i. econs. i. des.
    - inv LT.
      + eapply IH; eauto.
      + eapply IH; eauto. left.
        eapply Operators_Properties.clos_trans_tn1. econs 2.
        * eapply Operators_Properties.clos_tn1_trans; eauto.
        * eapply Operators_Properties.clos_tn1_trans; eauto.
    - subst. inv H; eauto.
  }
  { right. reflexivity. }
  { eauto. }
Qed.

Lemma well_founded_irreflexive A (R: A -> A -> Prop) (WF: well_founded R)
      a
      (LT: R a a)
  :
    False.
Proof.
  hexploit (well_founded_induction WF (fun a' => ~ (a' = a))).
  { ii. des; clarify. eapply H; eauto. }
  i. eapply H. eauto.
Qed.

Module Ordinal.
  Section TYPE.
  Let MyT := Type.
  Inductive t: Type :=
  | build (A: MyT) (os: A -> t)
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

  Lemma total_le o0 o1: le o0 o1 \/ le o1 o0.
  Proof.
    destruct (total o0 o1); auto. right. eapply lt_le. auto.
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

  Lemma acc_mon A (R0 R1: A -> A -> Prop) (INCL: forall a0 a1 (LE: R0 a0 a1), R1 a0 a1)
        a (ACC: Acc R1 a)
    :
      Acc R0 a.
  Proof.
    induction ACC. econs. i. eapply H0; eauto.
  Qed.

  Lemma wf_mon A (R0 R1: A -> A -> Prop) (INCL: forall a0 a1 (LE: R0 a0 a1), R1 a0 a1)
        (WF: well_founded R1)
    :
      well_founded R0.
  Proof.
    econs. i. eapply acc_mon; eauto.
  Qed.

  Program Fixpoint from_acc A (R: A -> A -> Prop) (a1: A) (ACC: Acc R a1): t :=
    @build (sig (fun a0 => R a0 a1)) (fun a0p =>
                                        @from_acc _ R (proj1_sig a0p) _).
  Next Obligation.
    inv ACC. eapply H0; eauto.
  Defined.
  Arguments from_acc [A R] a1 ACC.

  Let Acc_prop A (R: A -> A -> Prop) a (p0 p1: Acc R a):
    p0 = p1.
  Proof.
    eapply (@Acc_ind _ R (fun a => forall (p0 p1: Acc R a), p0 = p1)); auto.
    i. destruct p2, p3. f_equal.
    extensionality y. extensionality r.
    eapply H0; eauto.
  Qed.

  Let well_founded_prop A (R: A -> A -> Prop) (WF0 WF1: well_founded R):
    WF0 = WF1.
  Proof.
    extensionality a. eapply Acc_prop.
  Qed.

  Lemma from_acc_lt A (R: A -> A -> Prop) (a0 a1: A) (LT: R a0 a1)
        (ACC1: Acc R a1) (ACC0: Acc R a0)
    :
      lt (from_acc a0 ACC0) (from_acc a1 ACC1).
  Proof.
    destruct ACC1. ss.
    set (exist (fun a0 => R a0 a1) a0 LT).
    replace ACC0 with (from_acc_obligation_1 (Acc_intro a1 a) s).
    2: { eapply Acc_prop. }
    eapply (build_upperbound (fun a0p => from_acc (proj1_sig a0p) (from_acc_obligation_1 (Acc_intro a1 a) a0p)) s).
  Qed.

  Lemma from_acc_complete A (R: A -> A -> Prop) a1 (ACC1: Acc R a1)
        o (LT: lt o (from_acc a1 ACC1))
    :
      exists a0 (ACC0: Acc R a0), eq o (from_acc a0 ACC0).
  Proof.
    dup ACC1. revert o LT. induction ACC0. i. destruct ACC1.
    ss. dependent destruction LT. destruct a0 as [a0 p0]. ss.
    eapply le_eq_or_lt in LE. des; eauto.
  Qed.

  Definition from_wf A (R: A -> A -> Prop) (WF: well_founded R) (a1: A): t :=
    from_acc a1 (WF a1).

  Lemma from_wf_lt A (R: A -> A -> Prop) (WF: well_founded R) (a0 a1: A) (LT: R a0 a1)
    :
      lt (from_wf WF a0) (from_wf WF a1).
  Proof.
    eapply from_acc_lt; eauto.
  Qed.

  Lemma from_wf_supremum A (R: A -> A -> Prop) (WF: well_founded R) o a1
        (LE: forall a0 (LT: R a0 a1), lt (from_wf WF a0) o)
    :
      le (from_wf WF a1) o.
  Proof.
    unfold from_wf. destruct (WF a1). ss.
    eapply build_spec. i. destruct a0 as [a0 r]. ss.
    specialize (LE a0 r). unfold from_wf in LE.
    replace (a a0 r) with (WF a0); auto.
  Qed.

  Lemma from_wf_complete A (R: A -> A -> Prop) (WF: well_founded R) a1
        o (LT: lt o (from_wf WF a1))
    :
      exists a0, eq o (from_wf WF a0).
  Proof.
    eapply from_acc_complete in LT. des. exists a0.
    unfold from_wf. replace (WF a0) with ACC0; auto.
  Qed.

  Definition from_wf_set A (R: A -> A -> Prop) (WF: well_founded R): t :=
    @build A (from_wf WF).

  Lemma from_wf_set_upperbound A (R: A -> A -> Prop) (WF: well_founded R) a:
    lt (from_wf WF a) (from_wf_set WF).
  Proof.
    eapply build_upperbound.
  Qed.

  Lemma from_wf_set_complete A (R: A -> A -> Prop) (WF: well_founded R)
        o (LT: lt o (from_wf_set WF))
    :
      exists a, eq o (from_wf WF a).
  Proof.
    dependent destruction LT. eapply le_eq_or_lt in LE. des; eauto.
    eapply from_wf_complete in LE. eauto.
  Qed.

  Lemma from_acc_mon A (R0 R1: A -> A -> Prop) (INCL: forall a0 a1 (LE: R0 a0 a1), R1 a0 a1)
        a (ACC0: Acc R0 a) (ACC1: Acc R1 a)
    :
      le (from_acc a ACC0) (from_acc a ACC1).
  Proof.
    dup ACC1. rename ACC2 into ACC. revert ACC0 ACC1. induction ACC.
    i. destruct ACC0, ACC1. ss. econs. i.
    destruct a1 as [a1 p1]. ss. exists (exist _ a1 (INCL _ _ p1)). ss.
    eapply H0; eauto.
  Qed.

  Lemma from_wf_mon A (R0 R1: A -> A -> Prop) (INCL: forall a0 a1 (LE: R0 a0 a1), R1 a0 a1)
        (WF0: well_founded R0) (WF1: well_founded R1) a
    :
      le (from_wf WF0 a) (from_wf WF1 a).
  Proof.
    unfold from_wf. eapply from_acc_mon; eauto.
  Qed.

  Lemma from_wf_set_le A (R0 R1: A -> A -> Prop) (INCL: forall a0 a1 (LE: R0 a0 a1), R1 a0 a1)
        (WF0: well_founded R0) (WF1: well_founded R1)
    :
      le (from_wf_set WF0) (from_wf_set WF1).
  Proof.
    econs. i. exists a0. eapply from_wf_mon; auto.
  Qed.

  Lemma from_wf_set_lt A (R0 R1: A -> A -> Prop) (INCL: forall a0 a1 (LE: R0 a0 a1), R1 a0 a1)
        (WF0: well_founded R0) (WF1: well_founded R1)
        (TOP: exists a2 x, R1 x a2 /\ forall a0 a1 (LT: R0 a0 a1), R1 a1 a2)
    :
      lt (from_wf_set WF0) (from_wf_set WF1).
  Proof.
    des. eapply lt_intro with (a:=a2).
    unfold from_wf. destruct (WF1 a2). ss. econs. intros a1.
    destruct (classic (exists a0, R0 a0 a1)).
    - des. exists (exist _ a1 (TOP0 _ _ H)). ss.
      unfold from_wf. eapply from_acc_mon; auto.
    - exists (exist _ x TOP). ss.
      unfold from_wf. destruct (WF0 a1), (a x TOP). econs. i.
      exfalso. destruct a4. eapply H; eauto.
  Qed.

  Lemma from_wf_preserve A B (f: A -> B)
        (RA: A -> A -> Prop) (RB: B -> B -> Prop)
        (WFA: well_founded RA)
        (WFB: well_founded RB)
        (LE: forall a0 a1 (LT: RA a0 a1), RB (f a0) (f a1))
    :
      forall a, le (from_wf WFA a) (from_wf WFB (f a)).
  Proof.
    eapply (well_founded_induction WFA); auto.
    intros a IH. unfold from_wf.
    destruct (WFA a) as [GA], (WFB (f a)) as [GB].
    ss. econs; ss. i.
    destruct a0 as [a0 r0]. ss. exists (exist _ (f a0) (LE _ _ r0)).
    ss. specialize (IH a0 r0). unfold from_wf in IH.
    replace (GA a0 r0) with (WFA a0).
    2: { eapply Acc_prop. }
    replace (GB (f a0) (LE a0 a r0)) with (WFB (f a0)).
    2: { eapply Acc_prop. }
    auto.
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

    Variable A: MyT.
    Variable os: A -> t.
    Let Y: (A -> MyT) :=
      fun a: A =>
        match (os a) with
        | @build B _ => B
        end.

    Let X: MyT :=
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
      specialize (LE0 (@eq_rect _ (os x) (fun t0 => match t0 return MyT with
                                                    | @build B _ => B
                                                    end) y _ (eq_sym H0))). des.
      exists (@eq_rect _ A2 id a1 A0 (build_fst_eq H1)).

      subst X Y. ss. destruct (os x).
      assert (os2 a1 = os0 (eq_rect A2 id a1 A0 (build_fst_eq H1))).
      { dependent destruction H1. ss. } rewrite <- H.
      assert ((os1
                 (eq_rect (build os3) (fun t0 : t => match t0 return MyT with
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
    Variable djoin: forall (A: MyT) (ds: A -> D), D.
    Variable wf: D -> Prop.

    Let deq: D -> D -> Prop :=
      fun d0 d1 => dle d0 d1 /\ dle d1 d0.

    Variable next: D -> D.
    Variable base: D.

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

    Lemma rec_mon o: dle (rec djoin next0 base0 o) (rec djoin next1 base1 o).
    Proof.
      induction o. ss. eapply djoin_supremum. i.
      etransitivity; [|eapply (djoin_upperbound _ a)]. ss. destruct a; auto.
      eapply djoin_supremum. i.
      etransitivity; [|eapply (djoin_upperbound _ a)]. ss.
      eapply NEXTLE. auto.
    Qed.
  End REC2.

  Section OREC.
    Variable next: t -> t.
    Variable base: t.

    Definition orec: t -> t := rec join next base.

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

    Lemma orec_le (o0 o1: t) (LE: le o0 o1): le (orec o0) (orec o1).
    Proof.
      unfold orec. eapply rec_le with (wf:=wf); auto. i. eapply next_eq. auto.
    Qed.

    Lemma orec_eq (o0 o1: t) (EQ: eq o0 o1): eq (orec o0) (orec o1).
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

    Lemma orec_le_base o: le base (orec o).
    Proof.
      eapply (@rec_le_base _ le join wf next base); ss.
      i. eapply next_eq; auto.
    Qed.
  End OREC.

  Definition add (o0: t): forall (o1: t), t := orec S o0.
  Definition mult (o0: t): forall (o1: t), t := orec (flip add o0) O.
  Definition expn (o0: t): forall (o1: t), t := orec (flip mult o0) (S O).

  Fixpoint from_nat (n: nat): t :=
    match n with
    | 0 => O
    | Datatypes.S n' => S (from_nat n')
    end.

  Definition omega: t := join from_nat.

  Definition is_hartogs A (h: t): Prop :=
    is_meet (fun o => forall (R: A -> A -> Prop) (WF: well_founded R),
                 ~ le o (from_wf_set WF)) h.

  Lemma hartogs_exists A:
    exists h, is_hartogs A h.
  Proof.
    eapply meet_exists.
    exists (@build
              (@sig (A -> A -> Prop) (@well_founded A))
              (fun rwf => from_wf_set (proj2_sig rwf))).
    ii. eapply lt_StrictOrder. eapply lt_le_lt; [|eauto].
    eapply (@build_upperbound _ (fun rwf => from_wf_set (proj2_sig rwf)) (@exist _ _ R WF)).
  Qed.

  Section WO.
    Variable X: Type.

    Record subos: Type :=
      subos_mk {
          subos_set: X -> Prop;
          subos_rel: X -> X -> Prop;
        }.
    Let subX := subos.
    Let P := subos_set.
    Let R := subos_rel.

    Record subos_wf (X': subos): Type :=
      subos_wf_intro {
          subos_sound: forall a0 a1 (LT: X'.(R) a0 a1), X'.(P) a0 /\ X'.(P) a1;
          subos_complete: forall a0 a1 (IN0: X'.(P) a0) (IN1: X'.(P) a1),
              X'.(R) a0 a1 \/ a0 = a1 \/ X'.(R) a1 a0;
          subos_wfo: well_founded X'.(R);
        }.

    Variable x_bot: X.

    Let wfX := subos_wf.
    Let sound := subos_sound.
    Let complete := subos_complete.
    Let wfo := subos_wfo.

    Record _leX (s0 s1: subX): Prop :=
      _leX_intro {
          _P_incl: forall a (IN: s0.(P) a), s1.(P) a;
          _R_incl: forall a0 a1 (LT: s0.(R) a0 a1), s1.(R) a0 a1;
          _no_insert: forall a0 a1 (IN: s0.(P) a1), s1.(R) a0 a1 <-> s0.(R) a0 a1;
        }.
    Let leX := _leX.
    Let P_incl := _P_incl.
    Let R_incl := _R_incl.
    Let no_insert := _no_insert.

    Let joinX A (Xs: A -> subX): subX :=
      subos_mk (fun x => exists a, (Xs a).(P) x) (fun x0 x1 => exists a, (Xs a).(R) x0 x1).

    Let base: subX := subos_mk (fun x => x = x_bot) (fun _ _ => False).

    Let leX_reflexive: forall d (WF: wfX d), leX d d.
    Proof.
      i. econs; eauto.
    Qed.

    Let leX_transitive: forall d1 d0 d2 (WF0: wfX d0) (WF1: wfX d1) (WF2: wfX d2) (LE0: leX d0 d1) (LE1: leX d1 d2),
        leX d0 d2.
    Proof.
      i. inv LE0. inv LE1. econs; eauto.
      i. rewrite _no_insert1; eauto.
    Qed.

    Let joinX_upperbound: forall A (ds: A -> subX) (a: A) (CHAIN: forall a0 a1, leX (ds a0) (ds a1) \/ leX (ds a1) (ds a0)) (WF: forall a, wfX (ds a)), leX (ds a) (joinX ds).
    Proof.
      i. econs; ss; eauto. i. split; i.
      - des. destruct (CHAIN a a2).
        + eapply H0 in H; eauto.
        + eapply H0. eauto.
      - eauto.
    Qed.

    Let joinX_supremum: forall A (ds: A -> subX) (d: subX) (CHAIN: forall a0 a1, leX (ds a0) (ds a1) \/ leX (ds a1) (ds a0)) (WF: forall a, wfX (ds a)) (WFD: wfX d) (LE: forall a, leX (ds a) d), leX (joinX ds) d.
    Proof.
      i. econs; ss.
      - i. des. eapply LE in IN. auto.
      - i. des. eapply LE in LT. auto.
      - i. des. split; i.
        + eapply LE in H; eauto.
        + des. eapply LE; eauto.
    Qed.

    Let joinX_wf: forall A (ds: A -> subX) (CHAIN: forall a0 a1, leX (ds a0) (ds a1) \/ leX (ds a1) (ds a0)) (WF: forall a, wfX (ds a)), wfX (joinX ds).
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

    Let base_wf: wfX base.
    Proof.
      econs; ss. i. subst. auto.
    Qed.

    Section NEXT.
      Hypothesis next: subX -> subX.

      Hypothesis next_wf: forall d (WF: wfX d), wfX (next d).
      Hypothesis next_le: forall d (WF: wfX d), leX d (next d).
      Hypothesis next_exhausted: forall d (WF: wfX d),
          (forall x, d.(P) x) \/
          (exists x, (next d).(P) x /\ ~ d.(P) x)
      .

      Let next_eq: forall d0 d1 (WF0: wfX d0) (WF1: wfX d1) (EQ: leX d0 d1 /\ leX d1 d0), leX (next d0) (next d1) /\ leX (next d1) (next d0).
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

      Let srec o := rec joinX next base o.

      Let srec_wf o: wfX (srec o).
      Proof.
        eapply rec_wf; eauto.
      Qed.

      Let srec_o o := @from_wf_set X (srec o).(R) (srec_wf o).(wfo).

      Let srec_le o0 o1 (LE: le o0 o1):
        leX (srec o0) (srec o1).
      Proof.
        eapply rec_le in LE; eauto.
      Qed.

      Let srec_o_le o0 o1 (LE: le o0 o1):
        le (srec_o o0) (srec_o o1).
      Proof.
        unfold srec_o. eapply from_wf_set_le. eapply srec_le; auto.
      Qed.

      Let srec_o_S o0 o1 (SUCC: is_S o0 o1) (NTOP: ~ forall x, (srec o0).(P) x):
        lt (srec_o o0) (srec_o o1).
      Proof.
        assert (SRECLE: leX (srec o0) (srec o1)).
        { eapply srec_le; eauto. eapply lt_le. eapply SUCC. }
        eapply from_wf_set_lt; auto.
        { eapply SRECLE. }
        hexploit (next_exhausted (srec_wf o0)). i. des.
        { exfalso. eapply NTOP. eauto. } clear NTOP.
        hexploit (@rec_is_S _ leX joinX wfX next base); eauto.
        i. des.
        assert (TOP: forall a1 (LT: P (srec o0) a1), R (srec o1) a1 x).
        { i. hexploit ((srec_wf o1).(complete) a1 x); auto.
          { eapply SRECLE; auto. }
          { eapply H2; auto. }
          i. des; auto; clarify.
          erewrite SRECLE.(no_insert) in H3; auto.
          eapply (srec_wf o0) in H3. des. ss.
        }
        exists x, x_bot. split.
        - eapply TOP. apply (@rec_le_base _ leX joinX wfX); ss.
        - i. eapply TOP. eapply (srec_wf o0) in LT. des. auto.
      Qed.

      Let srec_o_lt o0 o1 (LT: lt o0 o1) (NTOP: ~ forall x, (srec o0).(P) x):
        lt (srec_o o0) (srec_o o1).
      Proof.
        eapply (@lt_le_lt (srec_o (S o0))).
        - eapply srec_o_S; eauto. eapply S_is_S.
        - eapply srec_o_le; auto. eapply S_spec; auto.
      Qed.

      Let eventually_exhausted
        :
          exists o, forall x, (rec joinX next base o).(P) x.
      Proof.
        eapply NNPP. ii. assert (forall o, le o (srec_o o)).
        { eapply (@well_founded_induction _ lt).
          { eapply lt_well_founded. }
          i. destruct (total x (srec_o x)); auto. exfalso.
          dup H1. eapply H0 in H1. eapply srec_o_lt in H2; eauto.
          eapply (@lt_not_le (srec_o (srec_o x)) (srec_o x)); eauto.
        }
        hexploit (hartogs_exists X). i. des. specialize (H0 h).
        unfold is_hartogs, is_meet in H1. des.
        eapply H1. eauto.
      Qed.

      Lemma choice_then_well_ordering_theorem
        :
          exists (R: X -> X -> Prop),
            well_founded R /\
            (forall x0 x1, R x0 x1 \/ x0 = x1 \/ R x1 x0).
      Proof.
        hexploit eventually_exhausted. i. des.
        assert (WF: wfX (rec joinX next base o)).
        { hexploit (@rec_wf _ leX joinX wfX next base); eauto. }
        exists (rec joinX next base o).(R). splits; auto.
      Qed.
    End NEXT.

    Lemma inhabited_well_ordering_theorem
      :
        exists (R: X -> X -> Prop),
          well_founded R /\
          (forall x0 x1, R x0 x1 \/ x0 = x1 \/ R x1 x0).
    Proof.
      assert (exists (next: subX -> subX),
                 (forall d (WF: wfX d), wfX (next d)) /\
                 (forall d (WF: wfX d), leX d (next d)) /\
                 (forall d (WF: wfX d),
                     (forall x, d.(P) x) \/
                     (exists x, (next d).(P) x /\ ~ d.(P) x))).
      { hexploit (choice (fun d0 d1 =>
                            forall (WF: wfX d0),
                              wfX d1 /\ leX d0 d1 /\
                              ((forall x, P d0 x) \/ (exists x, P d1 x /\ ~ P d0 x)))).
        { intros d0. destruct (classic (forall x, P d0 x)).
          { exists d0. i. split; auto. }
          eapply not_all_ex_not in H. des.
          exists (subos_mk (fun x => P d0 x \/ x = n) (fun x0 x1 => R d0 x0 x1 \/ (P d0 x0 /\ x1 = n))).
          i. splits.
          - econs; ss.
            + i. des; clarify; splits; auto.
              * left. eapply WF in LT. des; eauto.
              * left. eapply WF in LT. des; eauto.
            + i. des; clarify; eauto.
              destruct (WF.(complete) a0 a1) as [|[|]]; auto.
            + assert (forall x, Acc (R d0) x -> P d0 x -> Acc (fun x0 x1 : X => R d0 x0 x1 \/ P d0 x0 /\ x1 = n) x).
              { i. revert H1. induction H0. econs. i. des; clarify.
                eapply H1; eauto. eapply WF in H3. des; eauto. }
              econs. i. des; clarify.
              * eapply H0.
                { eapply WF. }
                { eapply WF in H1. des; auto. }
              * eapply H0; eauto. eapply WF.
          - econs; ss; auto. i. split; i; auto. des; clarify.
          - i. right. ss. eauto.
        }
        i. des. exists f. splits; i; try apply H; eauto.
      }
      des. eapply choice_then_well_ordering_theorem; eauto.
    Qed.
  End WO.

  Lemma _well_ordering_theorem (X: Type)
    :
      exists (R: X -> X -> Prop),
        well_founded R /\
        (forall x0 x1, R x0 x1 \/ x0 = x1 \/ R x1 x0).
  Proof.
    destruct (classic (inhabited X)) as [[x]|].
    { eapply inhabited_well_ordering_theorem; auto. }
    { exists (fun _ _ => False). econs; i; ss. exfalso. eapply H; eauto. }
  Qed.

  Section ZORNLT.
    Variable B: MyT.
    Variable R: B -> B -> Prop.
    Hypothesis antisym: forall b0 b1 (LT0: R b0 b1) (LT1: R b1 b0), False.

    Let chain := B -> Prop.

    Let restricted_order (c: chain): B -> B -> Prop :=
      fun b0 b1 => R b0 b1 /\ c b0 /\ c b1.

    Let wf: chain -> Prop :=
      fun c =>
        (forall b0 b1 (IN0: c b0) (IN1: c b1), R b0 b1 \/ b0 = b1 \/ R b1 b0) /\
        (well_founded (restricted_order c))
    .

    Let chain_le (c0 c1: chain) :=
      (forall b (IN: c0 b), c1 b) /\
      (forall b1 (IN: c1 b1), c0 b1 \/ (forall b0 (IN: c0 b0), R b0 b1))
    .

    Let chain_le_restricted (c0 c1: chain) (LE: chain_le c0 c1):
      forall b0 b1 (LT: restricted_order c0 b0 b1), restricted_order c1 b0 b1.
    Proof.
      i. inv LT. des. econs; eauto. split.
      - eapply LE; eauto.
      - eapply LE; eauto.
    Qed.

    Let chain_le_antisymmetric (c0 c1: chain) (LE0: chain_le c0 c1) (LE1: chain_le c1 c0): c0 = c1.
    Proof.
      extensionality b. eapply propositional_extensionality.
      destruct LE0, LE1. split; auto.
    Qed.

    Let chain_join (A: MyT) (cs: A -> chain): chain := fun b => exists a, cs a b.

    Let chain_le_reflexive: forall d (WF: wf d), chain_le d d.
    Proof.
      split; ii; auto.
    Qed.

    Let chain_le_transitive: forall d1 d0 d2 (WF0: wf d0) (WF1: wf d1) (WF2: wf d2) (LE0: chain_le d0 d1) (LE1: chain_le d1 d2),
        chain_le d0 d2.
    Proof.
      i. destruct LE0, LE1. split; ii; auto.
      eapply H2 in IN. des; auto.
    Qed.

    Let chain_join_upperbound: forall A (ds: A -> chain) (a: A) (CHAIN: forall a0 a1, chain_le (ds a0) (ds a1) \/ chain_le (ds a1) (ds a0)) (WF: forall a, wf (ds a)), chain_le (ds a) (chain_join ds).
    Proof.
      ii. split.
      - exists a. auto.
      - i. inv IN. destruct (CHAIN a x).
        + eapply H0 in H. des; auto.
        + eapply H0 in H. auto.
    Qed.

    Let chain_join_supremum: forall A (ds: A -> chain) (d: chain) (CHAIN: forall a0 a1, chain_le (ds a0) (ds a1) \/ chain_le (ds a1) (ds a0)) (WF: forall a, wf (ds a)) (WFD: wf d) (LE: forall a, chain_le (ds a) d), chain_le (chain_join ds) d.
    Proof.
      ii. split.
      - i. destruct IN. eapply LE in H. eauto.
      - i. eapply NNPP. ii. eapply not_or_and in H. des. eapply H0.
        i. inv IN0. eapply (LE x) in IN. des; auto.
        exfalso. eapply H. econs; eauto.
    Qed.

    Let chain_join_wf: forall A (ds: A -> chain) (CHAIN: forall a0 a1, chain_le (ds a0) (ds a1) \/ chain_le (ds a1) (ds a0)) (WF: forall a, wf (ds a)), wf (chain_join ds).
    Proof.
      ii. split.
      - i. unfold chain_join in IN0, IN1. des. destruct (CHAIN a0 a).
        + eapply H in IN0. destruct (proj1 (WF a) b0 b1); auto.
        + eapply H in IN1. destruct (proj1 (WF a0) b0 b1); auto.
      - assert (forall (a: A) b (IN: ds a b), Acc (restricted_order (chain_join ds)) b).
        { intros a. eapply (well_founded_induction (proj2 (WF a)) (fun b => forall (IN: ds a b), Acc (restricted_order (chain_join ds)) b)).
          i. econs. i. inv H0. des. clear H0. inv H2.
          destruct (CHAIN a x0).
          { dup H0. eapply H2 in H0. des.
            { eapply H; eauto. econs; eauto. }
            { exfalso. dup IN. eapply H0 in IN.
              eapply well_founded_irreflexive.
              { eapply clos_trans_well_founded. eapply (WF x0). }
              econs 2.
              { econs; eauto. split; auto. eapply H2; eauto. }
              econs 1; eauto. econs; eauto. split; auto. eapply H2; auto.
            }
          }
          { eapply H2 in H0. eapply H; eauto. econs; eauto. }
        }
        ii. econs. i. dup H0. inv H0. des. inv H0.
        eapply H in H4; eauto. eapply H4. auto.
    Qed.

    Section INCR.
      Variable f: chain -> B.
      Hypothesis INCR: forall c (WF: wf c) b (IN: c b), R b (f c).

      Let base := fun b => b = f (fun _ => False).
      Let base_wf: wf base.
      Proof.
        split.
        - ii. inv IN0; inv IN1; auto.
        - ii. econs. i. inv H. des. inv H1; inv H2.
          exfalso. eapply antisym; eauto.
      Qed.

      Let next: chain -> chain := fun c => fun b => c b \/ b = f c.
      Let next_wf: forall d (WF: wf d), wf (next d).
      Proof.
        i. dup WF. inv WF. split.
        - unfold next. i. des; subst; auto.
        - assert (forall b (IN: d b), Acc (restricted_order (next d)) b).
          { eapply (well_founded_induction H0 (fun b => forall (IN: d b), Acc (restricted_order (next d)) b)).
            i. econs. i. inv H2. unfold next in H4. destruct H4 as [[|] _].
            - eapply H1; eauto. econs; eauto.
            - subst. exfalso. eapply antisym.
              + eapply H3.
              + eapply INCR; eauto.
          }
          ii. econs. i. dup H2. inv H2. des. destruct H2.
          { eapply (H1 a); auto. }
          { subst. destruct H5.
            { eapply H1 in H2; auto. }
            { subst. exfalso. eapply antisym; eauto. }
          }
      Qed.

      Let next_le: forall d (WF: wf d), chain_le d (next d).
      Proof.
        i. split.
        { i. left. auto. }
        { i. destruct IN; auto. subst. right. i. eapply INCR; eauto. }
      Qed.

      Let next_eq: forall d0 d1 (WF0: wf d0) (WF1: wf d1) (EQ: chain_le d0 d1 /\ chain_le d1 d0),
          chain_le (next d0) (next d1) /\ chain_le (next d1) (next d0).
      Proof.
        i. des. assert (d0 = d1).
        { eapply chain_le_antisymmetric; auto. }
        subst. split.
        { split; auto. }
        { split; auto. }
      Qed.

      Let srec := rec chain_join next base.

      Let srec_wf o: wf (srec o).
      Proof.
        eapply (@rec_wf _ chain_le chain_join wf next base); auto.
      Qed.

      Let srec_le o0 o1 (LE: le o0 o1):
        le (from_wf_set (proj2 (srec_wf o0))) (from_wf_set (proj2 (srec_wf o1))).
      Proof.
        eapply from_wf_set_le. eapply chain_le_restricted; eauto.
        eapply (@rec_le _ chain_le chain_join wf next base); eauto.
      Qed.

      Let next_lt c (WF: wf c) (BASE: chain_le base c):
        lt (from_wf_set (proj2 WF)) (from_wf_set (proj2 (next_wf WF))).
      Proof.
        eapply from_wf_set_lt.
        { eapply chain_le_restricted; eauto. }
        { exists (f c), (f (fun _ => False)). split.
          { econs.
            - eapply INCR; auto. eapply BASE. ss.
            - unfold next. split; auto. left.
              eapply BASE. ss.
          }
          { i. inv LT. des. econs.
            - eapply INCR; eauto.
            - unfold next. splits; auto.
          }
        }
      Qed.

      Let srec_lt o0 o1 (LT: lt o0 o1):
        lt (from_wf_set (proj2 (srec_wf o0))) (from_wf_set (proj2 (srec_wf o1))).
      Proof.
        eapply lt_le_lt.
        { eapply next_lt.
          eapply (@rec_le_base _ chain_le chain_join wf next base); eauto. }
        eapply S_spec in LT. eapply srec_le in LT.
        etransitivity; [|eapply LT]. eapply from_wf_set_le.
        eapply chain_le_restricted.
        eapply (@rec_S _ chain_le chain_join wf next base); eauto.
      Qed.

      Let srec_larger:
        forall o, le o (from_wf_set (proj2 (srec_wf o))).
      Proof.
        induction o. eapply build_spec. i.
        eapply le_lt_lt; [eapply H|].
        eapply srec_lt. eapply build_upperbound.
      Qed.

      Lemma eventually_maximal h (HARTOGS: is_hartogs B h): False.
      Proof.
        hexploit (srec_larger h). i.
        unfold is_hartogs, is_meet in HARTOGS. des. eapply HARTOGS; eauto.
      Qed.
    End INCR.

    Hypothesis transitive: forall b0 b1 b2 (LT0: R b0 b1) (LT1: R b1 b2), R b0 b2.

    Hypothesis upperbound_exists:
      forall (c: B -> Prop) (CHAIN: forall b0 b1 (IN0: c b0) (IN1: c b1), R b0 b1 \/ b0 = b1 \/ R b1 b0),
      exists b_u, forall b (IN: c b), R b b_u \/ b = b_u.

    Lemma _zorn_lemma_lt:
      exists b_m, forall b, ~ R b_m b.
    Proof.
      eapply NNPP. ii.
      hexploit (choice (fun (c: chain) (b1: B) =>
                          forall (WF: wf c) b0 (IN: c b0), R b0 b1)).
      { intros c. destruct (classic (wf c)).
        - hexploit upperbound_exists.
          { eapply H0. }
          i. des. eapply not_ex_all_not in H. eapply not_all_ex_not in H. des.
          eapply NNPP in H. exists n. i.
          destruct (H1 b0 IN); subst; eauto.
        - hexploit (upperbound_exists (fun _ => False)); ss.
          i. des. exists b_u. ss.
      }
      i. des. hexploit (hartogs_exists B); eauto. i. des.
      eapply eventually_maximal; eauto.
    Qed.
  End ZORNLT.

  Section ZORNANTISYM.
    Variable B: MyT.
    Variable R: B -> B -> Prop.
    Hypothesis le_PreOrder: PreOrder R.
    Local Existing Instance le_PreOrder.
    Hypothesis antisym: forall b0 b1 (LE0: R b0 b1) (LE1: R b1 b0), b0 = b1.

    Hypothesis upperbound_exists:
      forall (c: B -> Prop) (CHAIN: forall b0 b1 (IN0: c b0) (IN1: c b1), R b0 b1 \/ R b1 b0),
      exists b_u, forall b (IN: c b), R b b_u.

    Lemma _zorn_lemma_antisym:
      exists b_m, forall b (LE: R b_m b), b = b_m.
    Proof.
      hexploit (@_zorn_lemma_lt B (fun b0 b1 => R b0 b1 /\ b0 <> b1)).
      { i. des. exploit antisym; eauto. }
      { i. des. splits; auto.
        - etransitivity; eauto.
        - ii. subst. hexploit antisym; eauto. }
      { i. hexploit (upperbound_exists c).
        { i. hexploit (CHAIN b0 b1); eauto.
          i. des; auto. subst. left. reflexivity.
        }
        i. des. exists b_u. i. destruct (classic (b = b_u)); auto.
      }
      i. des. exists b_m. i. eapply NNPP. ii. eapply H; eauto.
    Qed.
  End ZORNANTISYM.

  Section ZORN.
    Variable B: MyT.
    Variable R: B -> B -> Prop.
    Hypothesis le_PreOrder: PreOrder R.
    Local Existing Instance le_PreOrder.

    Hypothesis upperbound_exists:
      forall (c: B -> Prop) (CHAIN: forall b0 b1 (IN0: c b0) (IN1: c b1), R b0 b1 \/ R b1 b0),
      exists b_u, forall b (IN: c b), R b b_u.

    Let equiv_class: MyT :=
      @sig (B -> Prop) (fun s => (exists a, s a) /\
                                 (forall a0 a1 (IN0: s a0),
                                     s a1 <-> (R a0 a1 /\ R a1 a0))).

    Let to_equiv_class_p (a0: B):
      (fun s => (exists a, s a) /\
                (forall a0 a1 (IN0: s a0),
                    s a1 <-> (R a0 a1 /\ R a1 a0)))
        (fun a1 => R a0 a1 /\ R a1 a0).
    Proof.
      split.
      { exists a0. split; reflexivity. }
      { i. split; i.
        - des. split; etransitivity; eauto.
        - des. split; etransitivity; eauto.
      }
    Qed.

    Let to_equiv_class (a0: B): equiv_class :=
      exist _ (fun a1 => R a0 a1 /\ R a1 a0) (to_equiv_class_p a0).

    Let equiv_class_rel: equiv_class -> equiv_class -> Prop :=
      fun s0 s1 => exists a0 a1, (proj1_sig s0) a0 /\ (proj1_sig s1) a1 /\ R a0 a1.

    Let to_equiv_class_eq a (s: equiv_class) (IN: proj1_sig s a):
      s = to_equiv_class a.
    Proof.
      destruct s. unfold to_equiv_class.
      assert (x = (fun a1 : B => R a a1 /\ R a1 a)).
      { ss. des.
        extensionality b. eapply propositional_extensionality. split; i.
        - eapply a1; eauto.
        - eapply a1; eauto.
      }
      subst. f_equal. apply proof_irrelevance.
    Qed.

    Let equiv_class_rel_PreOrder: PreOrder equiv_class_rel.
    Proof.
      econs.
      - ii. destruct x. des. exists a1, a1.
        ss. splits; auto. reflexivity.
      - ii. inv H. inv H0. des. exists x0, a1. splits; auto.
        etransitivity; eauto. etransitivity; eauto.
        destruct y. ss. des. exploit (a2 x1 a0); eauto.
        i. eapply x4; eauto.
    Qed.
    Local Existing Instance equiv_class_rel_PreOrder.

    Let antisym: forall b0 b1 (LE0: equiv_class_rel b0 b1) (LE1: equiv_class_rel b1 b0), b0 = b1.
    Proof.
      i. inv LE0. inv LE1. des.
      assert (R x a1 /\ R a1 x).
      { eapply (proj2_sig b0); eauto. }
      assert (R x0 a0 /\ R a0 x0).
      { eapply (proj2_sig b1); eauto. } des.
      assert (proj1_sig b0 x0).
      { eapply (proj2_sig b0); eauto. split.
        - transitivity x; auto. transitivity a0; auto.
        - transitivity a0; auto. transitivity x0; auto. }
      transitivity (to_equiv_class x0).
      { eapply to_equiv_class_eq; eauto. }
      { symmetry. eapply to_equiv_class_eq; eauto. }
    Qed.

    Let to_equiv_class_preserve a0 a1:
      R a0 a1 <-> equiv_class_rel (to_equiv_class a0) (to_equiv_class a1).
    Proof.
      split; i.
      { exists a0, a1. ss. splits; auto.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - reflexivity. }
      { inv H. des. ss. des.
        transitivity x; auto. transitivity a2; auto. }
    Qed.

    Let to_equiv_rel_iff a0 a1 (s0 s1: equiv_class) (IN0: proj1_sig s0 a0) (IN1: proj1_sig s1 a1):
      R a0 a1 <-> equiv_class_rel s0 s1.
    Proof.
      eapply to_equiv_class_eq in IN0.
      eapply to_equiv_class_eq in IN1. subst.
      eapply to_equiv_class_preserve.
    Qed.

    Let equiv_class_upperbound_exists:
      forall (c: equiv_class -> Prop) (CHAIN: forall b0 b1 (IN0: c b0) (IN1: c b1), equiv_class_rel b0 b1 \/ equiv_class_rel b1 b0),
      exists b_u, forall b (IN: c b), equiv_class_rel b b_u.
    Proof.
      i. hexploit (@upperbound_exists (fun b => exists s, c s /\ proj1_sig s b)).
      { i. des. hexploit (CHAIN s0 s); eauto. i.
        hexploit (to_equiv_rel_iff _ _ _ _ IN3 IN2). i.
        hexploit (to_equiv_rel_iff _ _ _ _ IN2 IN3). i. des; eauto. }
      { i. des. exists (to_equiv_class b_u). i.
        hexploit (proj2_sig b); eauto. i. des.
        exploit H; eauto. i.
        eapply to_equiv_class_eq in H0. subst.
        eapply to_equiv_class_preserve; eauto. }
    Qed.

    Lemma _zorn_lemma:
      exists b_m, forall b (LE: R b_m b), R b b_m.
    Proof.
      hexploit (@_zorn_lemma_antisym _ equiv_class_rel); eauto. i. des.
      hexploit (proj2_sig b_m); eauto. i. des. exists a. i.
      eapply to_equiv_class_preserve in LE.
      eapply to_equiv_class_eq in H0; eauto. subst. ss.
      eapply H in LE; eauto.
      eapply to_equiv_class_preserve. rewrite LE. reflexivity.
    Qed.
  End ZORN.

  Section ZORNWEAK.
    Variable B: MyT.
    Hypothesis INHABITED: inhabited B.
    Variable R: B -> B -> Prop.
    Hypothesis le_PreOrder: PreOrder R.

    Hypothesis upperbound_exists:
      forall (c: B -> Prop) (INHABITED: exists b, c b)
             (CHAIN: forall b0 b1 (IN0: c b0) (IN1: c b1), R b0 b1 \/ R b1 b0),
      exists b_u, forall b (IN: c b), R b b_u.

    Lemma _zorn_lemma_weak:
      exists b_m, forall b (LE: R b_m b), R b b_m.
    Proof.
      eapply _zorn_lemma; eauto. i. destruct (classic (exists b, c b)).
      { eapply upperbound_exists; eauto. }
      { dup INHABITED. inv INHABITED. exists X. i. exfalso. eapply H; eauto. }
    Qed.
  End ZORNWEAK.

  Section EXTEND.
    Variable A: Type.
    Variable RT: A -> A -> Prop.
    Variable WFT: well_founded RT.
    Hypothesis TOTAL: forall a0 a1, RT a0 a1 \/ a0 = a1 \/ RT a1 a0.

    Variable R: A -> A -> Prop.
    Variable WF: well_founded R.

    Definition extended (a0 a1: A): Prop :=
      lt (from_wf WF a0) (from_wf WF a1) \/
      (eq (from_wf WF a0) (from_wf WF a1) /\ RT a0 a1)
    .

    Lemma extended_total:
      forall a0 a1, extended a0 a1 \/ a0 = a1 \/ extended a1 a0.
    Proof.
      i. destruct (trichotomy (from_wf WF a0) (from_wf WF a1)) as [|[]].
      - left. left. auto.
      - destruct (@TOTAL a0 a1) as [|[]]; auto.
        + left. right. auto.
        + right. right. right. split; auto. symmetry. auto.
      - right. right. left. auto.
    Qed.

    Lemma extended_well_founded: well_founded extended.
    Proof.
      ii. hexploit (well_founded_induction
                      lt_well_founded
                      (fun o => forall a (LE: le (from_wf WF a) o), Acc extended a)); eauto.
      { clear a. intros o IH.
        assert (LTS: forall a (LT: lt (from_wf WF a) o), Acc extended a).
        { i. econs. i.
          hexploit (IH _ LT).
          { reflexivity. }
          i. inv H0. eauto.
        }
        i. eapply le_eq_or_lt in LE. des; auto.
        eapply (well_founded_induction
                  WFT (fun a => eq (from_wf WF a) o -> Acc extended a)); eauto.
        clear a LE. i. econs. i. inv H1.
        { eapply (IH (from_wf WF y)).
          { eapply lt_eq_lt; eauto. symmetry. auto. }
          { reflexivity. }
        }
        { des. eapply H; eauto. transitivity (from_wf WF x); auto. }
      }
      { eapply lt_le. eapply from_wf_set_upperbound. }
    Qed.

    Lemma extended_incl:
      forall a0 a1 (LT: R a0 a1), extended a0 a1.
    Proof.
      i. left. eapply from_wf_lt; auto.
    Qed.
  End EXTEND.

  Lemma well_order_extendable A (R0: A -> A -> Prop) (WF: well_founded R0):
    exists R1,
      well_founded R1 /\
      (forall a0 a1 (LT: R0 a0 a1), R1 a0 a1) /\
      (forall a0 a1, R1 a0 a1 \/ a0 = a1 \/ R1 a1 a0).
  Proof.
    hexploit (_well_ordering_theorem A); eauto. i. des.
    exists (extended R WF). splits.
    - eapply extended_well_founded; eauto.
    - eapply extended_incl; eauto.
    - eapply extended_total; eauto.
  Qed.

  Lemma from_wf_set_embed A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
        (WFA: well_founded RA) (WFB: well_founded RB)
        (LE: le (from_wf_set WFA) (from_wf_set WFB))
        (TOTALB: forall b0 b1, RB b0 b1 \/ b0 = b1 \/ RB b1 b0)
    :
      exists (f: A -> B), forall a0 a1 (LT: RA a0 a1), RB (f a0) (f a1).
  Proof.
    exploit (choice (fun a b => eq (from_wf WFA a) (from_wf WFB b))).
    { intros a. eapply from_wf_set_complete.
      eapply lt_le_lt; eauto. eapply from_wf_set_upperbound. }
    i. des. exists f. i. eapply from_wf_lt with (WF:=WFA) in LT.
    assert (lt (from_wf WFB (f a0)) (from_wf WFB (f a1))).
    { eapply (@le_lt_lt (from_wf WFA a0)); eauto.
      - eapply x0.
      - eapply (@lt_le_lt (from_wf WFA a1)); auto. eapply x0. }
    destruct (TOTALB (f a0) (f a1)) as [|[]].
    - auto.
    - rewrite H0 in *. eapply lt_not_le in H; ss. reflexivity.
    - eapply from_wf_lt with (WF:=WFB) in H0; eauto.
      exfalso. eapply lt_not_le in H; ss. eapply lt_le; auto.
  Qed.

  Lemma from_wf_set_comparable A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
        (WFA: well_founded RA) (WFB: well_founded RB)
        (TOTALA: forall a0 a1, RA a0 a1 \/ a0 = a1 \/ RA a1 a0)
        (TOTALB: forall b0 b1, RB b0 b1 \/ b0 = b1 \/ RB b1 b0)
    :
      (exists (f: A -> B), forall a0 a1 (LT: RA a0 a1), RB (f a0) (f a1)) \/
      (exists (f: B -> A), forall b0 b1 (LT: RB b0 b1), RA (f b0) (f b1)).
  Proof.
    destruct (total_le (from_wf_set WFA) (from_wf_set WFB)).
    - left. eapply from_wf_set_embed; eauto.
    - right. eapply from_wf_set_embed; eauto.
  Qed.

  Lemma set_comparable A B
    :
      (exists (f: A -> B), forall a0 a1 (EQ: f a0 = f a1), a0 = a1) \/
      (exists (f: B -> A), forall b0 b1 (EQ: f b0 = f b1), b0 = b1).
  Proof.
    hexploit (@_well_ordering_theorem A); eauto. i. des.
    hexploit (@_well_ordering_theorem B); eauto. i. des.
    hexploit (from_wf_set_comparable H H1); eauto. i. des.
    - left. exists f. i. destruct (H0 a0 a1) as [|[]]; auto.
      + eapply H3 in H4. rewrite EQ in *. exfalso.
        eapply (well_founded_irreflexive H1); eauto.
      + eapply H3 in H4. rewrite EQ in *. exfalso.
        eapply (well_founded_irreflexive H1); eauto.
    - right. exists f. i. destruct (H2 b0 b1) as [|[]]; auto.
      + eapply H3 in H4. rewrite EQ in *. exfalso.
        eapply (well_founded_irreflexive H); eauto.
      + eapply H3 in H4. rewrite EQ in *. exfalso.
        eapply (well_founded_irreflexive H); eauto.
  Qed.

  Lemma from_wf_inj A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
        (WFA: well_founded RA) (WFB: well_founded RB)
        f
        (INJ: forall a0 a1 (LT: RA a0 a1), RB (f a0) (f a1))
    :
      forall a, le (from_wf WFA a) (from_wf WFB (f a)).
  Proof.
    eapply (well_founded_induction WFA). i. eapply from_wf_supremum.
    i. dup LT. eapply H in LT. eapply le_lt_lt; eauto.
    eapply from_wf_lt; eauto.
  Qed.

  Lemma from_wf_set_inj A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
        (WFA: well_founded RA) (WFB: well_founded RB)
        f
        (INJ: forall a0 a1 (LT: RA a0 a1), RB (f a0) (f a1))
    :
      le (from_wf_set WFA) (from_wf_set WFB).
  Proof.
    eapply build_spec. i. eapply le_lt_lt.
    { eapply from_wf_inj; eauto. }
    eapply from_wf_set_upperbound.
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
  Hint Constructors projected_rel.

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
    eapply wf_mon.
    { eapply inj_projected_rel_incl. eapply INJ. }
    { eauto. }
  Qed.

  Lemma from_wf_projected_rel_eq A B (RA: A -> A -> Prop)
        (WFA: well_founded RA)
        (f: A -> B)
        (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
    :
      forall a, eq (from_wf WFA a) (from_wf (embed_projected_rel_well_founded WFA f INJ) (f a)).
  Proof.
    eapply (well_founded_induction WFA). i. split.
    - eapply from_wf_supremum. i. exploit H; eauto. i.
      eapply eq_lt_lt; eauto. eapply from_wf_lt.
      econs; eauto.
    - eapply from_wf_supremum. i. inv LT.
      eapply INJ in H2. subst. exploit H; eauto. i.
      symmetry in x0. eapply eq_lt_lt; eauto.
      eapply from_wf_lt; eauto.
  Qed.

  Lemma from_wf_set_projected_rel_le A B (RA: A -> A -> Prop)
        (WFA: well_founded RA)
        (f: A -> B)
        (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
    :
      le (from_wf_set WFA) (from_wf_set (embed_projected_rel_well_founded WFA f INJ)).
  Proof.
    eapply build_spec. i. eapply eq_lt_lt.
    { eapply from_wf_projected_rel_eq. }
    eapply build_upperbound.
  Qed.

  Lemma from_wf_set_projected_rel_eq A B (RA: A -> A -> Prop)
        (INHABITED: inhabited A)
        (WFA: well_founded RA)
        (f: A -> B)
        (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
    :
      eq (from_wf_set WFA) (from_wf_set (embed_projected_rel_well_founded WFA f INJ)).
  Proof.
    split.
    - eapply from_wf_set_projected_rel_le.
    - eapply build_spec. i.
      destruct (classic (exists a', f a' = a)).
      { des. subst. eapply eq_lt_lt.
        { symmetry. eapply from_wf_projected_rel_eq. }
        { eapply build_upperbound. }
      }
      { destruct INHABITED. eapply le_lt_lt.
        2: { eapply (build_upperbound _ X). }
        eapply from_wf_supremum. i. inv LT.
        exfalso. eauto.
      }
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
  Hint Constructors projected_rel_sig.

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
      forall a, eq (from_wf WFA a) (from_wf (projected_rel_sig_well_founded WFA f INJ) (to_projected_sig f a)).
  Proof.
    eapply (well_founded_induction WFA). i. split.
    - eapply from_wf_supremum. i. exploit H; eauto. i.
      eapply eq_lt_lt; eauto. eapply from_wf_lt.
      econs; eauto.
    - eapply from_wf_supremum. i. inv LT.
      eapply INJ in H2. subst. exploit H; eauto. i.
      symmetry in x0. eapply eq_lt_lt; eauto.
      eapply from_wf_lt; eauto.
  Qed.

  Lemma from_wf_set_projected_rel_sig_le A B (RA: A -> A -> Prop)
        (WFA: well_founded RA)
        (f: A -> B)
        (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
    :
      le (from_wf_set WFA) (from_wf_set (projected_rel_sig_well_founded WFA f INJ)).
  Proof.
    eapply build_spec. i. eapply eq_lt_lt.
    { eapply from_wf_projected_rel_sig_eq. }
    eapply build_upperbound.
  Qed.

  Lemma from_wf_set_projected_rel_sig_eq A B (RA: A -> A -> Prop)
        (WFA: well_founded RA)
        (f: A -> B)
        (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
    :
      eq (from_wf_set WFA) (from_wf_set (projected_rel_sig_well_founded WFA f INJ)).
  Proof.
    split.
    - eapply from_wf_set_projected_rel_sig_le.
    - eapply build_spec. i. destruct a. des. subst. eapply eq_lt_lt.
      { symmetry. eapply from_wf_projected_rel_sig_eq. }
      { eapply build_upperbound. }
  Qed.

  Definition union_set (A: MyT) (Ts: A -> MyT): MyT := @sigT A (fun a => option (Ts a)).

  Inductive union_rel (A: MyT)
            (Ts: A -> MyT) (R: forall a, Ts a -> Ts a -> Prop):
    union_set Ts -> union_set Ts -> Prop :=
  | union_rel_top
      a x
    :
      union_rel R (existT _ a (Some x)) (existT _ a None)
  | union_rel_normal
      a x0 x1
      (LT: R a x0 x1)
    :
      union_rel R (existT _ a (Some x0)) (existT _ a (Some x1))
  .
  Hint Constructors union_rel.

  Lemma union_rel_well_founded (A: MyT) (Ts: A -> MyT)
        (R: forall a, Ts a -> Ts a -> Prop)
        (WF: forall a, well_founded (R a))
    :
      well_founded (union_rel R).
  Proof.
    assert (forall a x, Acc (union_rel R) (existT _ a (Some x))).
    { intros a. eapply (well_founded_induction (WF a)); auto.
      i. econs. i. dependent destruction H0. eapply H; eauto. }
    ii. destruct a as [a [x|]]; eauto.
    econs. i. inv H0; eauto.
  Qed.

  Lemma bot_well_founded A: @well_founded A (fun _ _ => False).
  Proof.
    ii. econs; ss.
  Qed.

  Lemma from_wf_union (A: MyT) (Ts: A -> MyT)
        (R: forall a, Ts a -> Ts a -> Prop)
        (WF: forall a, well_founded (R a))
        (a: A) (x: Ts a)
    :
      eq (from_wf (WF a) x)
         (from_wf (union_rel_well_founded R WF) (existT _ a (Some x))).
  Proof.
    revert x. eapply (well_founded_induction (WF a)).
    i. split.
    { eapply from_wf_supremum. i. specialize (H _ LT). inv H.
      eapply le_lt_lt; eauto. eapply from_wf_lt. econs; eauto. }
    { eapply from_wf_supremum. i. dependent destruction LT.
      specialize (H _ LT). inv H.
      eapply le_lt_lt; eauto. eapply from_wf_lt. auto. }
  Qed.

  Lemma from_wf_set_union (A: MyT) (Ts: A -> MyT)
        (R: forall a, Ts a -> Ts a -> Prop)
        (WF: forall a, well_founded (R a))
    :
      eq (@build A (fun a => from_wf_set (WF a)))
         (from_wf_set (union_rel_well_founded R WF)).
  Proof.
    split.
    { econs. i. exists (existT _ a0 None). eapply build_spec. i.
      eapply (@le_lt_lt (from_wf (union_rel_well_founded R WF) (existT _ a0 (Some a)))).
      { eapply from_wf_union. }
      { eapply from_wf_lt. econs. }
    }
    { econs. i. destruct a0 as [a0 [x|]].
      { exists a0. transitivity (from_wf (WF a0) x).
        { eapply from_wf_union. }
        { eapply lt_le. eapply from_wf_set_upperbound. }
      }
      { exists a0. eapply from_wf_supremum. i.
        dependent destruction LT.
        eapply (@le_lt_lt (from_wf (WF a0) x)).
        { eapply from_wf_union. }
        { eapply from_wf_set_upperbound. }
      }
    }
  Qed.

  Fixpoint to_set (o: t): @sigT MyT (fun A => A -> A -> Prop) :=
    match o with
    | @build A os => existT
                       _
                       (union_set (fun a => projT1 (to_set (os a))))
                       (union_rel (fun a => projT2 (to_set (os a))))
    end.

  Lemma to_set_well_founded: forall o, well_founded (projT2 (to_set o)).
  Proof.
    induction o. ss. eapply union_rel_well_founded; auto.
  Defined.

  Lemma to_set_eq o:
    eq o (from_wf_set (to_set_well_founded o)).
  Proof.
    induction o. etransitivity.
    2: { eapply from_wf_set_union. }
    split.
    { econs. i. exists a0. eapply H. }
    { econs. i. exists a0. eapply H. }
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

  Lemma from_wf_cut A (R: A -> A -> Prop) (WF: well_founded R)
        (TOTAL: forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0)
        (a1: A):
    forall a0 (LT: R a0 a1),
      eq (from_wf WF a0) (from_wf (cut_rel_well_founded WF a1) (exist _ a0 LT)).
  Proof.
    eapply (well_founded_induction
              WF
              (fun a0 => forall (LT: R a0 a1), eq (from_wf WF a0) (from_wf (cut_rel_well_founded WF a1) (exist _ a0 LT)))).
    intros a0 IH. i. split.
    { eapply from_wf_supremum. i.
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
      eapply (@le_lt_lt (from_wf (cut_rel_well_founded WF a1)
                                 (exist _ a2 LT1))).
      { eapply IH; auto. }
      { eapply from_wf_lt. ss. }
    }
    { eapply from_wf_supremum. i. destruct a2 as [a2 LT1].
      unfold cut_rel in LT0. ss.
      eapply (@le_lt_lt (from_wf WF a2)).
      { eapply IH; auto. }
      { eapply from_wf_lt. ss. }
    }
  Qed.

  Lemma from_wf_set_cut A (R: A -> A -> Prop) (WF: well_founded R)
        (TOTAL: forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0)
        (a1: A):
      eq (from_wf WF a1) (from_wf_set (cut_rel_well_founded WF a1)).
  Proof.
    split.
    { eapply from_wf_supremum. i.
      eapply lt_intro with (a:=exist _ a0 LT).
      eapply from_wf_cut; eauto. }
    { eapply build_spec. intros [a0 r].
      eapply (@le_lt_lt (from_wf WF a0)).
      { eapply from_wf_cut; eauto. }
      { eapply from_wf_lt; eauto. }
    }
  Qed.

  Lemma to_total_exists (o: t):
    exists (A: MyT) (R: A -> A -> Prop) (WF: well_founded R),
      eq o (from_wf_set WF) /\
      (forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0).
  Proof.
    hexploit (to_set_eq o). intros EQ.
    hexploit (well_order_extendable (to_set_well_founded o)). i. des.
    assert (le o (from_wf_set H)).
    { transitivity (from_wf_set (to_set_well_founded o)); auto.
      { eapply EQ. }
      { eapply from_wf_set_le; auto. }
    }
    eapply le_eq_or_lt in H2. des.
    { eapply from_wf_set_complete in H2. des.
      hexploit (from_wf_set_cut H H1 a). i.
      eexists _, _, (cut_rel_well_founded H a). splits.
      { transitivity (from_wf H a); auto. }
      { eapply cut_rel_total; eauto. }
    }
    { esplits; eauto. }
  Qed.

  Section TOTALIFY.
    (* propositional extensionality is used in this section *)
    Variable A: MyT.
    Variable R: A -> A -> Prop.
    Hypothesis WF: well_founded R.

    Definition equiv_class: MyT :=
      @sig (A -> Prop) (fun s => (exists a, s a) /\
                                 (forall a0 a1 (IN0: s a0), s a1 <-> eq (from_wf WF a0) (from_wf WF a1))).

    Program Definition to_equiv_class (a0: A): equiv_class :=
      exist _ (fun a1 => eq (from_wf WF a0) (from_wf WF a1)) _.
    Next Obligation.
      split.
      { exists a0. reflexivity. }
      { i. split; i.
        - transitivity (from_wf WF a0); eauto. symmetry. auto.
        - transitivity (from_wf WF a1); eauto.
      }
    Qed.

    Let to_equiv_class_equiv a (s: equiv_class) (IN: proj1_sig s a):
      s = to_equiv_class a.
    Proof.
      destruct s. ss. unfold to_equiv_class.
      assert (x = (fun a1 : A => eq (from_wf WF a) (from_wf WF a1))).
      { extensionality a1. eapply propositional_extensionality. des. split.
        { i. eapply a2; eauto. }
        { i. eapply a2; eauto. }
      }
      subst. f_equal. eapply proof_irrelevance.
    Qed.

    Definition equiv_class_rel: equiv_class -> equiv_class -> Prop :=
      fun s0 s1 => exists a0 a1, (proj1_sig s0) a0 /\ (proj1_sig s1) a1 /\ lt (from_wf WF a0) (from_wf WF a1).

    Lemma to_equiv_class_preserve a0 a1 (LT: R a0 a1):
      equiv_class_rel (to_equiv_class a0) (to_equiv_class a1).
    Proof.
      exists a0, a1. ss. splits.
      - reflexivity.
      - reflexivity.
      - eapply from_wf_lt; auto.
    Qed.

    Lemma equiv_class_total:
      forall s0 s1, equiv_class_rel s0 s1 \/ s0 = s1 \/ equiv_class_rel s1 s0.
    Proof.
      i. hexploit (proj2_sig s0). i. des. hexploit (proj2_sig s1). i. des.
      destruct (trichotomy (from_wf WF a) (from_wf WF a0)) as [|[]].
      - left. unfold equiv_class_rel. esplits; eauto.
      - right. left. assert (proj1_sig s0 = proj1_sig s1).
        { extensionality x. eapply propositional_extensionality. split; i.
          - eapply H2; eauto. transitivity (from_wf WF a); eauto.
            + symmetry. auto.
            + eapply (H0 a x); auto.
          - eapply H0; eauto. transitivity (from_wf WF a0); eauto.
            eapply (H2 a0 x); auto.
        }
        destruct s0, s1. ss. subst. f_equal. eapply proof_irrelevance.
      - right. right. unfold equiv_class_rel. esplits; eauto.
    Qed.

    Lemma equiv_class_well_founded: well_founded equiv_class_rel.
    Proof.
      assert (forall (o: t), forall (s: equiv_class) a0 (IN: proj1_sig s a0) (LT: lt (from_wf WF a0) o), Acc equiv_class_rel s).
      { eapply (well_founded_induction lt_well_founded (fun o => forall (s: equiv_class) a0 (IN: proj1_sig s a0) (LT: lt (from_wf WF a0) o), Acc equiv_class_rel s)).
        i. econs. i. unfold equiv_class_rel in H0. des.
        hexploit (proj2 (proj2_sig s) a0 a2); auto. i. dup H1.
        eapply H3 in H4. clear H3. eapply (H (from_wf WF a0)); eauto.
        eapply lt_eq_lt; eauto.
      }
      ii. hexploit (proj2_sig a); eauto. i. des.
      hexploit (H (S (from_wf WF a0))); eauto. eapply S_lt.
    Qed.

    Lemma to_equiv_class_eq a:
      eq (from_wf WF a) (from_wf equiv_class_well_founded (to_equiv_class a)).
    Proof.
      assert (forall (o: t), forall a (LT: lt (from_wf WF a) o), eq (from_wf WF a) (from_wf equiv_class_well_founded (to_equiv_class a))).
      { eapply (well_founded_induction lt_well_founded (fun o => forall a (LT: lt (from_wf WF a) o), eq (from_wf WF a) (from_wf equiv_class_well_founded (to_equiv_class a)))).
        i. split.
        { eapply from_wf_supremum. i. dup LT0. eapply (from_wf_lt WF) in LT0; eauto.
          hexploit H; eauto. i. eapply le_lt_lt; [eapply H0|].
          eapply from_wf_lt. eapply to_equiv_class_preserve. auto.
        }
        { eapply from_wf_supremum. i. unfold equiv_class_rel in LT0. des. ss.
          hexploit (H _ LT a2).
          { eapply lt_eq_lt; eauto. } i.
          eapply lt_eq_lt; eauto. eapply le_lt_lt; eauto.
          etransitivity; [|eapply H0].
          eapply to_equiv_class_equiv in LT0. subst. reflexivity.
        }
      }
      eapply (H (S (from_wf WF a))). eapply S_lt.
    Qed.

    Lemma from_wf_set_equiv_class:
      eq (from_wf_set WF) (from_wf_set equiv_class_well_founded).
    Proof.
      split.
      { eapply build_spec. i. eapply eq_lt_lt.
        { eapply to_equiv_class_eq. }
        { eapply from_wf_set_upperbound. }
      }
      { eapply build_spec. i. hexploit (proj2_sig a). i. des.
        eapply to_equiv_class_equiv in H. subst.
        eapply eq_lt_lt.
        { symmetry. eapply to_equiv_class_eq. }
        { eapply from_wf_set_upperbound. }
      }
    Qed.
  End TOTALIFY.

  Definition to_total_set (o: t): MyT := equiv_class (to_set_well_founded o).
  Definition to_total_rel (o: t): (to_total_set o) -> (to_total_set o) -> Prop :=
    @equiv_class_rel _ _ (to_set_well_founded o).
  Arguments to_total_rel: clear implicits.

  Lemma to_total_well_founded (o: t): well_founded (to_total_rel o).
  Proof.
    eapply equiv_class_well_founded.
  Defined.
  Arguments to_total_well_founded: clear implicits.

  Lemma to_total_eq (o: t):
    eq o (from_wf_set (@to_total_well_founded o)).
  Proof.
    etransitivity.
    - eapply to_set_eq.
    - eapply (from_wf_set_equiv_class (@to_set_well_founded o)).
  Qed.

  Lemma to_total_total (o: t):
    forall (x0 x1: to_total_set o), to_total_rel o x0 x1 \/ x0 = x1 \/ to_total_rel o x1 x0.
  Proof.
    eapply equiv_class_total.
  Qed.

  Section CARDINALITY.
    Variant _cardinal_le (A B: Type): Prop :=
    | _cardinal_le_intro
        (f: A -> B)
        (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
    .

    Let _cardinal_eq (A B: Type): Prop := _cardinal_le A B /\ _cardinal_le B A.
    Let _cardinal_lt (A B: Type): Prop := _cardinal_le A B /\ ~ _cardinal_eq A B.

    Let _cardinal_total_le: forall (A B: Type), _cardinal_le A B \/ _cardinal_le B A.
    Proof.
      i. hexploit (set_comparable A B). i. des.
      - left. econs; eauto.
      - right. econs; eauto.
    Qed.

    Section CARDINAL.
      Variable A: MyT.

      Definition is_cardinal (c: t): Prop :=
        is_meet (fun o =>
                   exists (R: A -> A -> Prop) (WF: well_founded R),
                     (forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0) /\
                     eq (from_wf_set WF) o) c.

      Lemma is_cardinal_exists: exists c, is_cardinal c.
      Proof.
        eapply meet_exists.
        hexploit (@_well_ordering_theorem A); eauto. i. des.
        exists (from_wf_set H), R, H. splits; auto. reflexivity.
      Qed.

      Lemma cardinal_unique c0 c1 (CARD0: is_cardinal c0) (CARD1: is_cardinal c1):
        eq c0 c1.
      Proof.
        unfold is_cardinal, is_meet in *. des. split.
        - eapply CARD4; eauto.
        - eapply CARD2; eauto.
      Qed.

      Let X: MyT :=
        @sig
          (@sigT (A -> Prop) (fun s => sig s -> sig s-> Prop))
          (fun PR =>
             well_founded (projT2 PR) /\
             (forall a0 a1, projT2 PR a0 a1 \/ a0 = a1 \/ projT2 PR a1 a0) /\
             (forall (f: A -> sig (projT1 PR)),
                 exists a0 a1, f a0 = f a1 /\ a0 <> a1)).

      Let Y (x: X): t :=
        @from_wf_set (sig (projT1 (proj1_sig x))) _ (proj1 (proj2_sig x)).

      Definition cardinal := @build X Y.

      Lemma cardinal_lowerbound (R: A -> A -> Prop) (WF: well_founded R)
            (TOTAL: forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0):
        le cardinal (from_wf_set WF).
      Proof.
        eapply build_spec. i. unfold Y.
        destruct a as [[P0 R0] [WF0 [TOTAL0 SMALL]]]; ss.
        replace (proj1 (conj WF0 (conj TOTAL0 SMALL))) with WF0.
        2: { eapply well_founded_prop. }
        destruct (total (from_wf_set WF) (from_wf_set WF0)); auto.
        exfalso. exploit from_wf_set_embed; eauto. i. des.
        hexploit (SMALL f); eauto. i. des.
        destruct (TOTAL a0 a1) as [|[]]; ss.
        { eapply x0 in H2. rewrite H0 in *.
          eapply well_founded_irreflexive in H2; eauto. }
        { eapply x0 in H2. rewrite H0 in *.
          eapply well_founded_irreflexive in H2; eauto. }
      Qed.

      Lemma _cardinal_upperbound B (CARD: _cardinal_lt B A)
            (R: B -> B -> Prop) (WF: well_founded R)
        :
          lt (from_wf_set WF) cardinal.
      Proof.
        inv CARD.
        assert (CLT: ~ _cardinal_le A B).
        { ii. eapply H0. econs; eauto. } inv H.
        hexploit (from_wf_set_projected_rel_sig_eq WF _ INJ). i.
        hexploit (well_order_extendable (projected_rel_sig_well_founded WF f INJ)). i. des.
        hexploit (from_wf_set_le H2 (projected_rel_sig_well_founded WF f INJ) H1). i.
        eapply le_lt_lt.
        { etransitivity.
          { eapply H. }
          { eapply H4. }
        }
        assert ((fun (PR:(@sigT (A -> Prop) (fun s => sig s -> sig s-> Prop))) =>
                   well_founded (projT2 PR) /\
                   (forall a0 a1, projT2 PR a0 a1 \/ a0 = a1 \/ projT2 PR a1 a0) /\
                   (forall (f: A -> sig (projT1 PR)),
                       exists a0 a1, f a0 = f a1 /\ a0 <> a1)) (existT _ _ R1)).
        { ss. splits; auto. i. eapply NNPP. ii. eapply CLT.
          hexploit (choice (fun (a: A) (b: B) => proj1_sig (f0 a) = f b)).
          { i.  hexploit (proj2_sig (f0 x)). i. des. eauto. }
          i. des. eapply _cardinal_le_intro with (f:=f1). i.
          eapply NNPP. ii. eapply f_equal with (f:=f) in EQ.
          rewrite <- H6 in EQ. rewrite <- H6 in EQ.
          eapply H5; eauto. exists a0, a1. splits; auto.
          destruct (f0 a0), (f0 a1); auto. ss. subst. f_equal. eapply proof_irrelevance.
        }
        hexploit (@build_upperbound
                    X Y
                    (@exist
                       (@sigT (A -> Prop) (fun s => sig s -> sig s-> Prop))
                       (fun PR =>
                          well_founded (projT2 PR) /\
                          (forall a0 a1, projT2 PR a0 a1 \/ a0 = a1 \/ projT2 PR a1 a0) /\
                          (forall (f: A -> sig (projT1 PR)),
                              exists a0 a1, f a0 = f a1 /\ a0 <> a1))
                       (@existT (A -> Prop) (fun s => sig s -> sig s-> Prop) _ R1)
                       H5)).
        ss. unfold Y. ss. i.
        replace H1 with (proj1 H5); auto.
      Qed.

      Lemma _cardinal_supremum c
            (UPPER: forall (B: MyT) (CARD: _cardinal_lt B A)
                           (R: B -> B -> Prop) (WF: well_founded R),
                lt (from_wf_set WF) c)
        :
          le cardinal c.
      Proof.
        eapply build_spec. i.
        destruct a as [[P0 R0] [WF0 [TOTAL SMALL]]]; ss. unfold Y. ss.
        replace (proj1 (conj WF0 (conj TOTAL SMALL))) with WF0.
        2: { eapply well_founded_prop. } eapply UPPER.
        assert (NLE: ~ _cardinal_le A (sig P0)).
        { ii. inv H. hexploit (SMALL f); eauto. i. des.
          eapply INJ in H. ss. }
        destruct (_cardinal_total_le A (sig P0)); ss.
        econs; auto. ii. eapply NLE. eapply H0.
      Qed.

      Lemma cardinal_is_cardinal: is_cardinal cardinal.
      Proof.
        split.
        - hexploit is_cardinal_exists. i. des.
          unfold is_cardinal, is_meet in H. des.
          exists R, WF. splits; auto. split.
          2: { eapply cardinal_lowerbound; auto. }
          hexploit (to_total_exists cardinal); eauto. i. des.
          hexploit (_cardinal_total_le A A0). i.
          destruct (classic (_cardinal_le A A0)).
          { transitivity (from_wf_set WF0).
            2: { eapply H2. }
            transitivity c.
            { eapply H1. }
            inv H5.
            hexploit (projected_rel_rev_well_founded WF0 f); auto. i.
            hexploit (H0 (from_wf_set H5)).
            { eexists _, H5. splits; auto.
              - i. destruct (H3 (f a0) (f a1)) as [|[]]; auto.
              - reflexivity. }
            i. transitivity (from_wf_set H5); auto.
            eapply from_wf_set_inj; eauto.
          }
          { assert (CLT: _cardinal_lt A0 A).
            { des; ss. econs; eauto. ii. inv H6. ss. }
            hexploit (_cardinal_upperbound CLT WF0). i.
            exfalso. eapply lt_not_le.
            { eapply H6. }
            { eapply H2. }
          }
        - i. des. eapply build_spec. i. unfold Y.
          destruct a as [[P0 R0] [WF0 [TOTAL SMALL]]]; ss.
          replace (proj1 (conj WF0 (conj TOTAL SMALL))) with WF0.
          2: { eapply well_founded_prop. }
          eapply lt_eq_lt.
          { symmetry. eapply IN0. }
          destruct (total (from_wf_set WF) (from_wf_set WF0)); auto.
          exfalso. exploit from_wf_set_embed; eauto. i. des.
          hexploit (SMALL f); eauto. i. des.
          destruct (IN a0 a1) as [|[]]; ss.
          { eapply x0 in H2. rewrite H0 in *.
            eapply well_founded_irreflexive in H2; eauto. }
          { eapply x0 in H2. rewrite H0 in *.
            eapply well_founded_irreflexive in H2; eauto. }
      Qed.
    End CARDINAL.

    Lemma _cardinal_le_iff A B:
      _cardinal_le A B <-> le (cardinal A) (cardinal B).
    Proof.
      split. i.
      - hexploit (cardinal_is_cardinal B). i. destruct H0. des.
        transitivity (from_wf_set WF); auto.
        2: { eapply H2. }
        inv H. transitivity (from_wf_set (projected_rel_rev_well_founded WF f INJ)).
        { eapply cardinal_is_cardinal.
          exists (projected_rel_rev R f), (projected_rel_rev_well_founded WF f INJ). splits; auto.
          - i. destruct (H0 (f a0) (f a1)) as [|[]]; auto.
          - reflexivity.
        }
        { eapply from_wf_set_inj. instantiate (1:=f). i. apply LT. }
      - hexploit (cardinal_is_cardinal B). i. destruct H. des.
        i. eapply NNPP. ii. destruct (_cardinal_total_le A B); ss.
        hexploit (_cardinal_upperbound).
        { split; eauto. ii. inv H5; ss. }
        instantiate (1:=WF). i. eapply lt_not_le; eauto.
        transitivity (cardinal B); auto. apply H2.
    Qed.

    Lemma _cardinal_eq_iff A B:
      _cardinal_eq A B <-> eq (cardinal A) (cardinal B).
    Proof.
      split. i.
      - split.
        + eapply _cardinal_le_iff; auto. apply H.
        + eapply _cardinal_le_iff; auto. apply H.
      - split.
        + eapply _cardinal_le_iff; auto. apply H.
        + eapply _cardinal_le_iff; auto. apply H.
    Qed.

    Lemma _cardinal_lt_iff A B:
      _cardinal_lt A B <-> lt (cardinal A) (cardinal B).
    Proof.
      split; i.
      - inv H. eapply _cardinal_le_iff in H0.
        eapply le_eq_or_lt in H0. des; auto.
        exfalso. eapply H1. eapply _cardinal_eq_iff; eauto.
      - split.
        + eapply _cardinal_le_iff. eapply lt_le; eauto.
        + ii. eapply _cardinal_eq_iff in H0.
          eapply lt_not_le; eauto. eapply H0.
    Qed.

    Lemma cardinal_size_le A B (R: B -> B -> Prop) (WF: well_founded R)
          (TOTAL: forall b0 b1, R b0 b1 \/ b0 = b1 \/ R b1 b0)
          (LE: le (cardinal A) (from_wf_set WF)):
      le (cardinal A) (cardinal B).
    Proof.
      hexploit (cardinal_is_cardinal A); auto. i. inv H. des.
      hexploit (@from_wf_set_embed _ _ _ _ WF0 WF); auto.
      { transitivity (cardinal A); auto. apply H2. }
      i. des. eapply _cardinal_le_iff.
      eapply _cardinal_le_intro with (f:=f). i.
      destruct (H0 a0 a1) as [|[]]; auto.
      - eapply H in H3. rewrite EQ in *.
        exfalso. eapply (well_founded_irreflexive WF); eauto.
      - eapply H in H3. rewrite EQ in *.
        exfalso. eapply (well_founded_irreflexive WF); eauto.
    Qed.

    Lemma cardinal_size_eq A B (R: B -> B -> Prop) (WF: well_founded R)
          (TOTAL: forall b0 b1, R b0 b1 \/ b0 = b1 \/ R b1 b0)
          (EQ: eq (cardinal A) (from_wf_set WF)):
      eq (cardinal A) (cardinal B).
    Proof.
      split; i.
      - eapply cardinal_size_le; eauto. eapply EQ.
      - transitivity (from_wf_set WF).
        + eapply (cardinal_is_cardinal B). esplits; eauto. reflexivity.
        + eapply EQ.
    Qed.

    Lemma le_cardinal_le A B (RA: A -> A -> Prop) (RB: B -> B -> Prop) (WFA: well_founded RA) (WFB: well_founded RB)
          (TOTAL: forall a0 a1, RA a0 a1 \/ a0 = a1 \/ RA a1 a0)
          (LE: le (from_wf_set WFA) (from_wf_set WFB))
      :
        le (cardinal A) (cardinal B).
    Proof.
      hexploit (well_order_extendable WFB); eauto. i. des.
      hexploit (@from_wf_set_embed _ _ _ _ WFA H); eauto.
      { transitivity (from_wf_set WFB); auto.
        eapply from_wf_set_le; eauto. }
      i. des. eapply _cardinal_le_iff.
      eapply _cardinal_le_intro with (f:=f). i.
      destruct (TOTAL a0 a1) as [|[]]; auto.
      { eapply H2 in H3. rewrite EQ in *.
        exfalso. eapply (well_founded_irreflexive H); eauto. }
      { eapply H2 in H3. rewrite EQ in *.
        exfalso. eapply (well_founded_irreflexive H); eauto. }
    Qed.

    Lemma to_total_le o0 o1 (LE: le o0 o1):
      le (cardinal (to_total_set o0)) (cardinal (to_total_set o1)).
    Proof.
      eapply le_cardinal_le.
      { eapply to_total_total. }
      instantiate (1:=to_total_well_founded o1).
      instantiate (1:=to_total_well_founded o0).
      transitivity o0.
      { eapply to_total_eq. }
      transitivity o1; auto.
      { eapply to_total_eq. }
    Qed.

    Lemma cardinal_to_total_adjoint A:
      eq (cardinal A) (cardinal (to_total_set (cardinal A))).
    Proof.
      eapply cardinal_size_eq.
      { eapply to_total_total. }
      eapply to_total_eq.
    Qed.
  End CARDINALITY.

  Section ALEPH.
    Section NEXT.
      Variable A: MyT.
      Let X: MyT := @sig (A -> A -> Prop) (@well_founded _).

      Let Y (x: X): t := from_wf_set (proj2_sig x).

      Definition next_cardinal := @build X Y.

      Lemma next_cardinal_upperbound B (R: B -> B -> Prop) (WF: well_founded R)
            (CARD: le (cardinal B) (cardinal A))
        : lt (from_wf_set WF) next_cardinal.
      Proof.
        eapply _cardinal_le_iff in CARD. inv CARD.
        eapply (@le_lt_lt (from_wf_set (embed_projected_rel_well_founded WF f INJ))).
        { eapply from_wf_set_inj. instantiate (1:=f). i. econs; eauto. }
        eapply (@build_upperbound X Y (exist _ _ (embed_projected_rel_well_founded WF f INJ))).
      Qed.

      Lemma next_cardinal_supremum B (CARD: lt (cardinal A) (cardinal B)):
        le next_cardinal (cardinal B).
      Proof.
        eapply build_spec. i. destruct a as [R WF]. unfold Y. ss.
        destruct (total (cardinal B) (from_wf_set WF)); auto.
        hexploit (cardinal_is_cardinal B); eauto. i. inv H0. des.
        hexploit (well_order_extendable WF); eauto. i. des.
        hexploit (@from_wf_set_embed _ _ _ _ WF0 H3); auto.
        { transitivity (cardinal B); auto.
          { eapply H0. }
          transitivity (from_wf_set WF); auto.
          eapply from_wf_set_le; auto.
        }
        i. des. exfalso.
        eapply _cardinal_lt_iff in CARD. des.
        eapply CARD0. split; auto.
        eapply _cardinal_le_intro with (f:=f). i.
        destruct (H1 a0 a1) as [|[]]; auto.
        - eapply H6 in H7. rewrite EQ in *.
          exfalso. eapply (well_founded_irreflexive H3); eauto.
        - eapply H6 in H7. rewrite EQ in *.
          exfalso. eapply (well_founded_irreflexive H3); eauto.
      Qed.

      Lemma next_cardinal_is_cardinal:
        is_cardinal (to_total_set next_cardinal) next_cardinal.
      Proof.
        split.
        { exists (to_total_rel next_cardinal), (to_total_well_founded next_cardinal).
          splits; auto.
          - eapply to_total_total.
          - symmetry. apply to_total_eq.
        }
        i. des. eapply build_spec. i. destruct a as [R0 WF0]. unfold Y. ss.
        destruct (total o1 (from_wf_set WF0)); auto.
        assert (LE: le (from_wf_set WF) (from_wf_set WF0)).
        { transitivity o1; auto. eapply IN0. }
        eapply le_cardinal_le in LE; auto. exfalso.
        eapply (next_cardinal_upperbound (to_total_well_founded next_cardinal)) in LE.
        eapply lt_not_le.
        { eapply LE. }
        { eapply to_total_eq. }
      Qed.
    End NEXT.

    Definition aleph := orec (fun o => next_cardinal (to_total_set o)) omega.
  End ALEPH.

  Section INACCESSIBLE.
    Let SmallT: MyT := Type.
    Let X := @sig (@sigT SmallT (fun X => X -> X -> Prop))
                  (fun PR => well_founded (projT2 PR)).
    Let Y : X -> t := fun PRWF => from_wf_set (proj2_sig PRWF).

    Definition kappa := @build X Y.

    Section UNION.
      Variable A: SmallT.
      Variable Ts: A -> SmallT.
      Variable R: forall a, Ts a -> Ts a -> Prop.
      Arguments R: clear implicits.
      Hypothesis WF: forall a, well_founded (R a).
      Arguments WF: clear implicits.
      Let _union_set: SmallT := @sigT A (fun a => option (Ts a)).

      Inductive _union_rel:
        _union_set -> _union_set -> Prop :=
      | _union_rel_top
          a x
        :
          _union_rel (existT _ a (Some x)) (existT _ a None)
      | _union_rel_normal
          a x0 x1
          (LT: R a x0 x1)
        :
          _union_rel (existT _ a (Some x0)) (existT _ a (Some x1))
      .
      Hint Constructors union_rel.

      Let _union_rel_well_founded:
          well_founded _union_rel.
      Proof.
        assert (forall a x, Acc _union_rel (existT _ a (Some x))).
        { intros a. eapply (well_founded_induction (WF a)); auto.
          i. econs. i. dependent destruction H0. eapply H; eauto. }
        ii. destruct a as [a [x|]]; eauto.
        econs. i. inv H0; eauto.
      Qed.

      Let _from_wf_union (a: A) (x: Ts a)
        :
          eq (from_wf (WF a) x)
             (from_wf _union_rel_well_founded (existT _ a (Some x))).
      Proof.
        revert x. eapply (well_founded_induction (WF a)).
        i. split.
        { eapply from_wf_supremum. i. specialize (H _ LT). inv H.
          eapply le_lt_lt; eauto. eapply from_wf_lt. econs; eauto. }
        { eapply from_wf_supremum. i. dependent destruction LT.
          specialize (H _ LT). inv H.
          eapply le_lt_lt; eauto. eapply from_wf_lt. auto. }
      Qed.

      Let _from_wf_set_union:
        eq (@build A (fun a => from_wf_set (WF a)))
           (from_wf_set _union_rel_well_founded).
      Proof.
        split.
        { econs. i. exists (existT _ a0 None). eapply build_spec. i.
          eapply (@le_lt_lt (from_wf _union_rel_well_founded (existT _ a0 (Some a)))).
          { eapply _from_wf_union. }
          { eapply from_wf_lt. econs. }
        }
        { econs. i. destruct a0 as [a0 [x|]].
          { exists a0. transitivity (from_wf (WF a0) x).
            { eapply _from_wf_union. }
            { eapply lt_le. eapply from_wf_set_upperbound. }
          }
          { exists a0. eapply from_wf_supremum. i.
            dependent destruction LT.
            eapply (@le_lt_lt (from_wf (WF a0) x)).
            { eapply _from_wf_union. }
            { eapply from_wf_set_upperbound. }
          }
        }
      Qed.

      Lemma small_join_small:
        exists (U: SmallT) (RU: U -> U -> Prop) (WFU: well_founded RU),
          forall a, lt (from_wf_set (WF a)) (from_wf_set WFU).
      Proof.
        exists _union_set, _union_rel, _union_rel_well_founded. i.
        eapply lt_eq_lt.
        { symmetry. eapply _from_wf_set_union. }
        eapply (@build_upperbound _ (fun a0 => from_wf_set (WF a0)) a).
      Qed.
    End UNION.

    Lemma kappa_inaccessible_build (A: SmallT) (os: A -> t) (LT: forall a, lt (os a) kappa)
      :
      lt (build os) kappa.
    Proof.
      hexploit (choice (fun (a: A) (XRWF: @sig (@sigT SmallT (fun X => X -> X -> Prop)) (fun XR => well_founded (projT2 XR))) =>
                          le (os a) (from_wf_set (proj2_sig XRWF)))).
      { i. eapply NNPP. ii. eapply lt_not_le.
        { eapply (LT x). }
        eapply build_spec. i. destruct (total (os x) (Y a)); auto.
        exfalso. eapply H. exists a. auto.
      }
      i. des.
      hexploit (@small_join_small A (fun a => projT1 (proj1_sig (f a))) (fun a => projT2 (proj1_sig (f a))) (fun a => proj2_sig (f a))).
      i. des. eapply (@le_lt_lt (from_wf_set WFU)).
      { eapply build_spec; eauto. i. eapply (@le_lt_lt (from_wf_set (proj2_sig (f a)))).
        { eapply H. }
        { eapply H0. }
      }
      eapply (@build_upperbound X Y (exist _ (existT _ U RU) WFU)).
    Qed.

    Lemma kappa_inaccessible_is_join (A: SmallT) (os: A -> t) (LT: forall a, lt (os a) kappa)
          o (JOIN: is_join os o)
      :
      lt o kappa.
    Proof.
      eapply (@le_lt_lt (build os)).
      2: { eapply kappa_inaccessible_build; auto. }
      eapply is_join_supremum; eauto.
      i. eapply lt_le. eapply build_upperbound.
    Qed.

    Lemma kappa_inaccessible_join (A: SmallT) (os: A -> t) (LT: forall a, lt (os a) kappa):
      lt (join os) kappa.
    Proof.
      eapply kappa_inaccessible_is_join; eauto. eapply join_is_join.
    Qed.

    Let D: SmallT := unit.
    Let D_well_founded: @well_founded D (fun _ _ => False).
    Proof.
      ii. econs; ss.
    Qed.

    Lemma kappa_inaccesible_from_acc (A: SmallT) (R: A -> A -> Prop) a (ACC: Acc R a):
      lt (from_acc a ACC) kappa.
    Proof.
      dup ACC. revert ACC. induction ACC0. i.
      destruct ACC. ss.
      hexploit (@kappa_inaccessible_build (sig (fun a0 => R a0 x)) (fun a0p : {a0 : A | R a0 x} => from_acc (` a0p) (from_acc_obligation_1 (Acc_intro x a) a0p))); eauto.
      i. destruct a0. ss. eapply H0; eauto.
    Qed.

    Lemma kappa_inaccesible_from_wf (A: SmallT) (R: A -> A -> Prop) (WF: well_founded R) a:
      lt (from_wf WF a) kappa.
    Proof.
      eapply kappa_inaccesible_from_acc.
    Qed.

    Lemma kappa_inaccesible_from_wf_set (A: SmallT) (R: A -> A -> Prop) (WF: well_founded R):
      lt (from_wf_set WF) kappa.
    Proof.
      eapply kappa_inaccessible_build. i. eapply kappa_inaccesible_from_wf.
    Qed.

    Lemma kappa_inaccessible_is_O o (ZERO: is_O o):
      lt o kappa.
    Proof.
      eapply le_lt_lt.
      { eapply ZERO. }
      eapply (@build_upperbound X Y (exist _ (existT _ D (fun _ _ => False)) D_well_founded)).
    Qed.

    Lemma kappa_inaccessible_O:
      lt O kappa.
    Proof.
      eapply kappa_inaccessible_is_O. eapply O_is_O.
    Qed.

    Lemma kappa_inaccessible_is_S o s (SUCC: is_S o s) (LT: lt o kappa):
      lt s kappa.
    Proof.
      eapply (@le_lt_lt (@build D (fun _ => o))).
      { eapply SUCC. eapply (build_upperbound (fun _ : D => o) tt). }
      { eapply kappa_inaccessible_build; eauto. }
    Qed.

    Lemma kappa_inaccessible_S o (LT: lt o kappa):
      lt (S o) kappa.
    Proof.
      eapply kappa_inaccessible_is_S; eauto.
      eapply S_is_S.
    Qed.
  End INACCESSIBLE.

  Section FIXPOINT.
    Variable D: MyT.
    Variable dle: D -> D -> Prop.
    Variable djoin: forall (A: MyT) (ds: A -> D), D.
    Variable wf: D -> Prop.

    Let deq: D -> D -> Prop :=
      fun d0 d1 => dle d0 d1 /\ dle d1 d0.

    Variable next: D -> D.
    Variable base: D.

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

    Let deq_transitive: forall d1 d0 d2 (WF0: wf d0) (WF1: wf d1) (WF2: wf d2) (EQ0: deq d0 d1) (EQ1: deq d1 d2),
        deq d0 d2.
    Proof.
      i. inv EQ0. inv EQ1. split.
      - eapply (@dle_transitive d1); auto.
      - eapply (@dle_transitive d1); auto.
    Qed.

    Let deq_symmetric: forall d0 d1 (EQ: deq d0 d1), deq d1 d0.
    Proof.
      i. inv EQ. split; auto.
    Qed.

    Let _rec_wf: forall o, wf (rec djoin next base o).
    Proof.
      eapply rec_wf; eauto.
    Qed.

    Let _rec_next_wf: forall o, wf (next (rec djoin next base o)).
    Proof.
      i. eapply next_wf. eapply rec_wf; eauto.
    Qed.

    Let k := next_cardinal D.

    Inductive strictly_increasing: D -> D -> Prop :=
    | strictly_increasing_intro
        o0 o1
        (LT: lt o0 o1)
        (INCR: ~ dle (rec djoin next base o1) (rec djoin next base o0))
      :
        strictly_increasing (rec djoin next base o0) (rec djoin next base o1)
    .

    Lemma strictly_increasing_well_founded: well_founded strictly_increasing.
    Proof.
      assert (forall o, Acc strictly_increasing (rec djoin next base o)).
      { eapply (well_founded_induction lt_well_founded).
        i. econs. i. inv H0. eapply H.
        destruct (total x o0); auto. exfalso.
        eapply INCR. rewrite H3. eapply rec_le; eauto.
      }
      ii. econs. i. inv H0. eapply H.
    Qed.

    Definition not_fixed (o1: t): Prop :=
      forall o0 (LT: lt o0 o1), ~ dle (rec djoin next base o1) (rec djoin next base o0).

    Lemma fixed_point_after o0 (FIX: dle (next (rec djoin next base o0)) (rec djoin next base o0)):
      forall o1 (LE: le o0 o1),
        dle (rec djoin next base o1) (rec djoin next base o0).
    Proof.
      eapply (@ind (fun o1 => forall (LE: le o0 o1),
                        dle (rec djoin next base o1) (rec djoin next base o0))).
      { i. eapply rec_le; eauto. }
      { i. eapply le_eq_or_lt in LE. des.
        2: { eapply rec_le; eauto. eapply LE. }
        hexploit (rec_is_S dle djoin wf next base); auto.
        { eauto. } i.
        assert (deq (rec djoin next base s) (next (rec djoin next base o))).
        { des. split; auto. } clear H.
        assert (LE0: le o0 o).
        { destruct (total o0 o); auto. exfalso. eapply SUCC in H.
          eapply (@lt_not_le o0 s); eauto. }
        hexploit IH; auto. i.
        assert (deq (next (rec djoin next base o0)) (rec djoin next base o0)).
        { split; auto. } clear FIX.
        assert (deq (rec djoin next base o) (rec djoin next base o0)).
        { split; auto. eapply rec_le; eauto. }
        eapply (@deq_transitive (rec djoin next base o)); auto.
        eapply (@deq_transitive (next (rec djoin next base o))); auto.
        dup H2. eapply next_eq in H2; eauto.
      }
      { i. hexploit (rec_is_join dle djoin wf next base); eauto. i. des.
        assert (forall a0 a1 : A,
                   dle (rec djoin next base (os a0)) (rec djoin next base (os a1)) \/ dle (rec djoin next base (os a1)) (rec djoin next base (os a0))).
        { i. destruct (total_le (os a0) (os a1)).
          { left. eapply rec_le; eauto. }
          { right. eapply rec_le; eauto. }
        }
        assert (wf (djoin (fun a : A => rec djoin next base (os a)))); auto.
        eapply (@dle_transitive (djoin (fun a : A => rec djoin next base (os a)))); auto.
        eapply djoin_supremum; auto. i.
        destruct (total (os a) o0).
        { eapply rec_le; eauto. }
        hexploit (IH a); eauto.
        eapply lt_le. auto.
      }
    Qed.

    Let end_le_end o0 o1 (LE: le o0 o1) (NEND: not_fixed o1): not_fixed o0.
    Proof.
      ii. eapply NEND.
      { eapply (@lt_le_lt o0); eauto. }
      dup LT. eapply S_spec in LT0.
      hexploit (rec_S dle djoin wf next base); auto. i. des.
      hexploit (@fixed_point_after o2).
      { eapply (@dle_transitive (rec djoin next base (S o2))); auto.
        { eapply H1. }
        eapply (@dle_transitive (rec djoin next base o0)); auto.
        eapply rec_le; eauto. }
      { instantiate (1:=o1). transitivity o0; auto.
        eapply lt_le. apply LT. }
      auto.
    Qed.

    Let least_lt_incr_acc o1 (INCR: not_fixed o1):
      le o1 (from_wf strictly_increasing_well_founded (rec djoin next base o1)).
    Proof.
      revert o1 INCR.
      eapply (well_founded_induction lt_well_founded
                                     (fun o1 => forall (INCR: not_fixed o1),
                                          le o1 (from_wf strictly_increasing_well_founded (rec djoin next base o1)))).
      i. destruct (total x (from_wf strictly_increasing_well_founded (rec djoin next base x))); auto.
      destruct x. eapply build_spec. i.
      hexploit (build_upperbound os a). i.
      hexploit (H (os a)); eauto.
      { eapply end_le_end; eauto. eapply lt_le; auto. }
      i. eapply le_lt_lt.
      { eapply H2. }
      eapply from_wf_lt. econs; eauto.
    Qed.

    Let kappa_fixed: ~ not_fixed k.
    Proof.
      ii. eapply least_lt_incr_acc in H; eauto.
      eapply lt_not_le.
      2: { eapply H. }
      eapply le_lt_lt.
      { eapply lt_le. eapply from_wf_set_upperbound. }
      eapply next_cardinal_upperbound. reflexivity.
    Qed.

    Lemma _fixpoint_theorem:
      dle (next (rec djoin next base k)) (rec djoin next base k).
    Proof.
      eapply NNPP. ii. eapply kappa_fixed. eapply end_le_end.
      { eapply lt_le. eapply S_lt. }
      ii. eapply H.
      hexploit (rec_S dle djoin wf next base); auto.
      i. des. eapply (@dle_transitive (rec djoin next base (S k))) ; auto.
      { eapply H2. }
      eapply (@dle_transitive (rec djoin next base o0)); auto.
      eapply (rec_le dle djoin wf next base); eauto.
      destruct (total o0 k); auto.
      eapply S_spec in H3.
      exfalso. eapply lt_not_le.
      { eapply LT. }
      { eapply H3. }
    Qed.
  End FIXPOINT.
End TYPE.
End Ordinal.

Theorem well_ordering_theorem (X: Type)
  :
    exists (R: X -> X -> Prop),
      well_founded R /\
      (forall x0 x1, R x0 x1 \/ x0 = x1 \/ R x1 x0).
Proof.
  eapply Ordinal._well_ordering_theorem.
Qed.

Section ZORNLT.
  Variable B: Type.
  Variable R: B -> B -> Prop.
  Hypothesis antisym: forall b0 b1 (LT0: R b0 b1) (LT1: R b1 b0), False.
  Hypothesis transitive: forall b0 b1 b2 (LT0: R b0 b1) (LT1: R b1 b2), R b0 b2.
  Hypothesis upperbound_exists:
    forall (c: B -> Prop) (CHAIN: forall b0 b1 (IN0: c b0) (IN1: c b1), R b0 b1 \/ b0 = b1 \/ R b1 b0),
    exists b_u, forall b (IN: c b), R b b_u \/ b = b_u.

  Theorem zorn_lemma_lt:
    exists b_m, forall b, ~ R b_m b.
  Proof.
    eapply Ordinal._zorn_lemma_lt; eauto.
  Qed.
End ZORNLT.

Section ZORNANTISYM.
  Variable B: Type.
  Variable R: B -> B -> Prop.
  Hypothesis le_PreOrder: PreOrder R.
  Hypothesis antisym: forall b0 b1 (LE0: R b0 b1) (LE1: R b1 b0), b0 = b1.
  Hypothesis upperbound_exists:
    forall (c: B -> Prop) (CHAIN: forall b0 b1 (IN0: c b0) (IN1: c b1), R b0 b1 \/ R b1 b0),
    exists b_u, forall b (IN: c b), R b b_u.

  Theorem zorn_lemma_antisym:
    exists b_m, forall b (LE: R b_m b), b = b_m.
  Proof.
    eapply Ordinal._zorn_lemma_antisym; eauto.
  Qed.
End ZORNANTISYM.

Section ZORN.
  Variable B: Type.
  Variable R: B -> B -> Prop.
  Hypothesis le_PreOrder: PreOrder R.
  Hypothesis upperbound_exists:
    forall (c: B -> Prop) (CHAIN: forall b0 b1 (IN0: c b0) (IN1: c b1), R b0 b1 \/ R b1 b0),
    exists b_u, forall b (IN: c b), R b b_u.

  Theorem zorn_lemma:
    exists b_m, forall b (LE: R b_m b), R b b_m.
  Proof.
    eapply Ordinal._zorn_lemma; eauto.
  Qed.
End ZORN.

Section ZORNWEAK.
  Variable B: Type.
  Hypothesis INHABITED: inhabited B.
  Variable R: B -> B -> Prop.
  Hypothesis le_PreOrder: PreOrder R.
  Hypothesis upperbound_exists:
    forall (c: B -> Prop) (INHABITED: exists b, c b)
           (CHAIN: forall b0 b1 (IN0: c b0) (IN1: c b1), R b0 b1 \/ R b1 b0),
    exists b_u, forall b (IN: c b), R b b_u.

  Theorem zorn_lemma_weak:
    exists b_m, forall b (LE: R b_m b), R b b_m.
  Proof.
    eapply Ordinal._zorn_lemma_weak; eauto.
  Qed.
End ZORNWEAK.


Module Cardinal.
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

  Lemma total_le A B: le A B \/ le B A.
  Proof.
    hexploit (Ordinal.set_comparable A B). i. des.
    - left. econs; eauto.
    - right. econs; eauto.
  Qed.

  Lemma total A B: le A B \/ lt B A.
  Proof.
    destruct (classic (le A B)); auto.
    destruct (total_le A B); auto.
    right. split; auto. ii. eapply H. eapply H1.
  Qed.

  Lemma trichotomy A B: lt A B \/ eq A B \/ lt B A.
  Proof.
    destruct (total A B); auto. eapply le_eq_or_lt in H. des; auto.
  Qed.

  Section CARDINAL.
    Let le_iff A B: le A B <-> Ordinal._cardinal_le A B.
    Proof.
      split; i.
      - inv H. econs; eauto.
      - inv H. econs; eauto.
    Qed.

    Let eq_iff A B: eq A B <-> Ordinal._cardinal_le A B /\ Ordinal._cardinal_le B A.
    Proof.
      split; i.
      - inv H. split; eapply le_iff; auto.
      - inv H. split; eapply le_iff; auto.
    Qed.

    Let lt_iff A B: lt A B <-> Ordinal._cardinal_le A B /\ ~ (Ordinal._cardinal_le A B /\ Ordinal._cardinal_le B A).
    Proof.
      split; i.
      - inv H. split.
        + eapply le_iff; auto.
        + erewrite <- eq_iff. auto.
      - des. split.
        + eapply le_iff; eauto.
        + erewrite eq_iff; eauto.
    Qed.

    Lemma cardinal_upperbound A B (CARD: lt B A)
          (R: B -> B -> Prop) (WF: well_founded R)
      :
        Ordinal.lt (Ordinal.from_wf_set WF) (Ordinal.cardinal A).
    Proof.
      eapply Ordinal._cardinal_upperbound. eapply lt_iff; auto.
    Qed.

    Lemma cardinal_supremum A c
          (UPPER: forall B (CARD: lt B A)
                         (R: B -> B -> Prop) (WF: well_founded R),
              Ordinal.lt (Ordinal.from_wf_set WF) c)
      :
        Ordinal.le (Ordinal.cardinal A) c.
    Proof.
      eapply Ordinal._cardinal_supremum. i. eapply UPPER. des. split.
      - inv CARD. econs; eauto.
      - ii. eapply CARD0. inv H. split.
        + inv H0. econs; eauto.
        + inv H1. econs; eauto.
    Qed.

    Lemma cardinal_le_iff A B:
      le A B <-> Ordinal.le (Ordinal.cardinal A) (Ordinal.cardinal B).
    Proof.
      rewrite <- Ordinal._cardinal_le_iff. auto.
    Qed.

    Lemma cardinal_eq_iff A B:
      eq A B <-> Ordinal.eq (Ordinal.cardinal A) (Ordinal.cardinal B).
    Proof.
      rewrite <- Ordinal._cardinal_eq_iff. auto.
    Qed.

    Lemma cardinal_lt_iff A B:
      lt A B <-> Ordinal.lt (Ordinal.cardinal A) (Ordinal.cardinal B).
    Proof.
      rewrite <- Ordinal._cardinal_lt_iff. auto.
    Qed.

  End CARDINAL.

  Lemma cardinal_to_total_adjoint A:
    eq A (Ordinal.to_total_set (Ordinal.cardinal A)).
  Proof.
    eapply cardinal_eq_iff.
    eapply Ordinal.cardinal_to_total_adjoint.
  Qed.

  Lemma lt_well_founded: well_founded lt.
  Proof.
    assert (forall (o: Ordinal.t) A (EQ: Ordinal.eq o (Ordinal.cardinal A)), Acc lt A).
    { eapply (well_founded_induction Ordinal.lt_well_founded (fun o => forall A (EQ: Ordinal.eq o (Ordinal.cardinal A)), Acc lt A)).
      i. econs. i. eapply cardinal_lt_iff in H0.
      eapply H.
      { eapply Ordinal.lt_eq_lt.
        { eapply EQ. }
        { eapply H0. }
      }
      { reflexivity. }
    }
    ii. eapply (H (Ordinal.cardinal a)). reflexivity.
  Qed.
End Cardinal.


Section FIXPOINT.
  Variable D: Type.
  Variable dle: D -> D -> Prop.
  Variable djoin: forall (A: Type) (ds: A -> D), D.
  Variable wf: D -> Prop.

  Let deq: D -> D -> Prop :=
    fun d0 d1 => dle d0 d1 /\ dle d1 d0.

  Variable next: D -> D.
  Variable base: D.

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

  Let k := Ordinal.next_cardinal D.

  Theorem fixpoint_theorem:
    dle (next (Ordinal.rec djoin next base k)) (Ordinal.rec djoin next base k).
  Proof.
    eapply (Ordinal._fixpoint_theorem dle djoin wf next base); eauto.
  Qed.
End FIXPOINT.

Module Kleene.
  Section FIXPOINT.
    Variable A: Type.
    Definition kappa := Ordinal.next_cardinal (A -> Prop).
    Definition le: (A -> Prop) -> (A -> Prop) -> Prop :=
      fun P0 P1 => forall a (IN0: P0 a), P1 a.
    Definition ge: (A -> Prop) -> (A -> Prop) -> Prop :=
      fun P0 P1 => forall a (IN0: P1 a), P0 a.
    Definition join (X: Type) (Ps: X -> A -> Prop): A -> Prop :=
      fun a => exists x, Ps x a.
    Definition meet (X: Type) (Ps: X -> A -> Prop): A -> Prop :=
      fun a => forall x, Ps x a.
    Definition bot: A -> Prop := fun _ => False.
    Definition top: A -> Prop := fun _ => True.

    Variable f: (A -> Prop) -> (A -> Prop).

    Hypothesis mon: forall (P0 P1: A -> Prop) (LE: le P0 P1), le (f P0) (f P1).
    Let mon_rev: forall (P0 P1: A -> Prop) (LE: ge P0 P1), ge (f P0) (f P1).
    Proof.
      ii. eapply mon; eauto.
    Qed.

    Definition mu := Ordinal.rec join f bot kappa.
    Definition nu := Ordinal.rec meet f top kappa.

    Theorem mu_fixpoint:
      le mu (f mu) /\ le (f mu) mu.
    Proof.
      split.
      { hexploit (Ordinal.rec_wf le join (fun P => le P (f P))); eauto.
        { ii. ss. }
        { ii. eapply LE1; eauto. }
        { ii. exists a. auto. }
        { ii. inv IN0. eapply LE; eauto. }
        { ii. inv IN0. eapply WF in H.
          eapply mon; eauto. ii. exists x. auto. }
        { ii. ss. }
        { ii. des. split; apply mon; auto. }
      }
      { hexploit (fixpoint_theorem le join (fun P => le P (f P)) f bot); eauto.
        { ii. ss. }
        { ii. eapply LE1; eauto. }
        { ii. exists a. auto. }
        { ii. inv IN0. eapply LE; eauto. }
        { ii. inv IN0. eapply WF in H.
          eapply mon; eauto. ii. exists x. auto. }
        { ii. ss. }
        { ii. des. split; apply mon; auto. }
      }
    Qed.

    Theorem mu_least P (LE: le (f P) P): le mu P.
    Proof.
      eapply (Ordinal.rec_wf le join (fun P0 => le P0 (f P0) /\ le P0 P) f bot); eauto.
      { ii. ss. }
      { ii. eapply LE1; eauto. }
      { ii. exists a. auto. }
      { ii. inv IN0. eapply LE0; eauto. }
      { ii. split; auto.
        - ii. inv IN0. destruct (WF x). eapply H0 in H.
          eapply mon; eauto. ii. exists x. auto.
        - ii. inv IN0. destruct (WF x). eapply H1 in H; auto. }
      { split; ss. }
      { i. des. splits; auto. ii. eapply LE. eapply mon; eauto. }
      { i. des. auto. }
      { i. des. splits; auto. }
    Qed.

    Theorem nu_fixpoint:
      le nu (f nu) /\ le (f nu) nu.
    Proof.
      split.
      { hexploit (fixpoint_theorem ge meet (fun P => le (f P) P) f top); eauto.
        { ii. ss. }
        { ii. eapply LE0; eauto. }
        { ii. eapply IN0; eauto. }
        { ii. eapply LE. auto. }
        { ii. eapply WF. eapply mon_rev in IN0; eauto.
          ii. eapply IN1; auto. }
        { ii. ss. }
        { ii. des. split; apply mon_rev; auto. }
      }
      { hexploit (Ordinal.rec_wf ge meet (fun P => le (f P) P) f top); eauto.
        { ii. ss. }
        { ii. eapply LE0; eauto. }
        { ii. eapply IN0; eauto. }
        { ii. eapply LE. auto. }
        { ii. eapply WF. eapply mon_rev in IN0; eauto.
          ii. eapply IN1; auto. }
        { ii. ss. }
        { ii. des. split; apply mon_rev; auto. }
      }
    Qed.

    Theorem nu_greatest P (LE: le P (f P)): le P nu.
    Proof.
      eapply (Ordinal.rec_wf ge meet (fun P0 => le (f P0) P0 /\ le P P0) f top); eauto.
      { ii. ss. }
      { ii. eapply LE0; eauto. }
      { ii. eapply IN0; eauto. }
      { ii. eapply LE0. auto. }
      { ii. split.
        - ii. edestruct (WF x). eapply H. eapply mon_rev in IN0; eauto.
          ii. eapply IN1; auto.
        - ii. eapply WF. auto. }
      { ii. ss. }
      { ii. des. splits; auto. ii. eapply LE in IN0. eapply mon; eauto. }
      { ii. des. auto. }
      { i. des. splits; auto. }
    Qed.
  End FIXPOINT.
End Kleene.

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

  Definition next_o (P: t) (o: Ordinal.t): t := Ordinal.rec meet next P o.

  (* Lemma next_o_le (P: t) (o0 o1: Ordinal.t) (LE: Ordinal.le o0 o1): *)
  (*   le (next_o P o1) (next_o P o0). *)
  (* Proof. *)
  (*   eapply (@Ordinal.rec_le t ge meet P next); auto. *)
  (*   - eapply flip_PreOrder. eapply le_PreOrder. *)
  (*   - i. eapply meet_lowerbound. *)
  (*   - i. eapply meet_infimum. auto. *)
  (*   - i. eapply next_mon; auto. *)
  (* Qed. *)

  (* Lemma next_o_eq (P: t) (o0 o1: Ordinal.t) (EQ: Ordinal.eq o0 o1): *)
  (*   next_o P o1 = next_o P o0. *)
  (* Proof. *)
  (*   eapply le_Antisymmetric. *)
  (*   - eapply next_o_le. eapply EQ. *)
  (*   - eapply next_o_le. eapply EQ. *)
  (* Qed. *)

  (* Lemma next_o_mon P0 P1 (LE: le P0 P1) o: le (next_o P0 o) (next_o P1 o). *)
  (* Proof. *)
  (*   revert o P0 P1 LE. induction o. i. ss. *)
  (*   eapply meet_infimum. i. etransitivity; [eapply (meet_lowerbound a)|]. *)
  (*   destruct a; auto. *)
  (*   eapply meet_infimum. i. etransitivity; [eapply (meet_lowerbound a)|]. *)
  (*   eapply next_mon. eauto. *)
  (* Qed. *)
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
