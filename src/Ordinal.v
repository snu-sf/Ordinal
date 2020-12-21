Require Import sflib.

Require Import Coq.Classes.RelationClasses Coq.Relations.Relation_Operators Coq.Classes.Morphisms ChoiceFacts. (* TODO: Use Morphisms *)

Set Implicit Arguments.
Set Primitive Projections.

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

  Fixpoint le2 (o0 o1: t): Prop :=
    match o0, o1 with
    | @build A0 os0, @build A1 os1 =>
      forall (a0: A0), exists (a1: A1), le2 (os0 a0) (os1 a1)
    end
  .

  Lemma le_le2 o0 o1:
    le o0 o1 <-> le2 o0 o1.
  Proof.
    split; i.
    - revert o0 o1 H. eapply le_induction. i. ss.
      i. exploit LE; eauto. i. des. eauto.
    - revert o0 H. induction o1. i. destruct o0. ss.
      econs. i. exploit H0; eauto. i. des. exists a1. eauto.
  Qed.

  Lemma le_inv A0 A1 os0 os1 (a0: A0) (LE: le (@build A0 os0) (@build A1 os1)):
    exists (a1: A1), le (os0 a0) (os1 a1).
  Proof.
    i. eapply le_le2 in LE. ss. specialize (LE a0). des.
    apply le_le2 in LE. eauto.
  Qed.

  Lemma le_equivalent A0 A1 os0 os1:
    le (@build A0 os0) (@build A1 os1) <->
    (forall (a0: A0), exists (a1: A1), le (os0 a0) (os1 a1)).
  Proof.
    split; i.
    - eapply le_inv. auto.
    - econs; eauto.
  Qed.

  Variant lt: t -> t -> Prop :=
  | lt_intro
      o A os (a: A)
      (LE: le o (os a))
    :
      lt o (build os)
  .
  Hint Constructors le.

  Definition lt2 (o0 o1: t): Prop :=
    match o1 with
    | @build A os =>
      exists (a: A), le o0 (os a)
    end
  .

  Lemma lt_lt2 o0 o1:
    lt o0 o1 <-> lt2 o0 o1.
  Proof.
    split; i.
    - inv H. ss. eauto.
    - destruct o1. ss. des. econs; eauto.
  Qed.

  Lemma lt_inv o0 A1 os1 (LT: lt o0 (@build A1 os1)):
    exists (a: A1), le o0 (os1 a).
  Proof.
    i. eapply lt_lt2 in LT. ss.
  Qed.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. induction x. econs; eauto.
  Qed.
  Next Obligation.
  Proof.
    ii. revert x y H H0. induction z. i. destruct x, y.
    rewrite le_equivalent in H0. rewrite le_equivalent in H1.
    econs. i. hexploit (H0 a0); eauto. i. des.
    hexploit (H1 a1); eauto. i. des. eauto.
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

  Global Program Instance lt_StrictOrder: StrictOrder lt.
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
    - eapply (le_inv tt) in H. des. destruct a1. ss.
  Qed.

  Lemma S_lt_mon o0 o1:
    lt o0 o1 <-> lt (S o0) (S o1).
  Proof.
    split ;i.
    - eapply lt_intro with (a:=tt). ss. destruct o1. econs.
      i. destruct a0. ss. eapply lt_inv in H. auto.
    - eapply lt_inv in H. des. destruct a. ss.
      destruct o1. eapply (le_inv tt) in H. des.
      eapply lt_intro with (a:=a1). ss.
  Qed.

  Lemma S_eq_mon o0 o1:
    eq o0 o1 <-> eq (S o0) (S o1).
  Proof.
    split; i.
    - split.
      + rewrite <- S_le_mon. apply H.
      + rewrite <- S_le_mon. apply H.
    - split.
      + rewrite S_le_mon. apply H.
      + rewrite S_le_mon. apply H.
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
    - assert (EQ0: eq (S o0) s).
      { eapply is_S_eq.
        - eapply S_is_S.
        - eauto.
      }
      assert (EQ1: eq (S o1) s).
      { eapply is_S_eq.
        - eapply S_is_S.
        - eauto.
      }
      eapply S_eq_mon.
      transitivity s; auto. symmetry. auto.
  Qed.

  Lemma S_eq o0 o1 (EQ: eq o0 o1):
    eq (S o0) (S o1).
  Proof.
    inv EQ. split.
    - rewrite <- S_le_mon. auto.
    - rewrite <- S_le_mon. auto.
  Qed.

  Lemma S_le o:
    le o (S o).
  Proof.
    eapply lt_le. eapply S_lt.
  Qed.

  Section JOIN.
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
      ii. unfold join. subst X Y.
      destruct (os a) eqn:EQ. econs. i.
      set (s:= @eq_rect_r t (build os0) (fun x => match x with
                                               | @build B _ => B
                                               end) a0 (os a) EQ).
      exists (existT _ a s).
      ss. unfold s. rewrite EQ. reflexivity.
    Qed.

    Lemma join_supremum o (LE: forall a, le (os a) o):
      le join o.
    Proof.
      destruct o. econs. i. destruct a0; ss.
      specialize (LE x).
      subst X Y. ss. destruct (os x) eqn:EQ.
      eapply (le_inv y) in LE. eauto.
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

  Lemma join_le_same A (os0 os1: A -> t) (LE: forall a, le (os0 a) (os1 a)):
    le (join os0) (join os1).
  Proof.
    eapply join_le. i. exists a0. auto.
  Qed.

  Lemma join_eq A (os0 os1: A -> t) (LE: forall a, eq (os0 a) (os1 a)):
    eq (join os0) (join os1).
  Proof.
    split; apply join_le_same; i; eapply LE.
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
    eapply is_join_eq.
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
    eapply is_join_eq.
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

  Lemma union_le o0 o1 (LE: le o0 o1): eq (union o0 o1) o1.
  Proof.
    split.
    - eapply union_spec.
      + auto.
      + reflexivity.
    - eapply union_r.
  Qed.

  Lemma union_le_mon o0 o1 o2 o3 (LE0: le o0 o1) (LE1: le o2 o3):
    le (union o0 o2) (union o1 o3).
  Proof.
    eapply union_spec.
    - transitivity o1; auto. eapply union_l.
    - transitivity o3; auto. eapply union_r.
  Qed.

  Lemma union_eq_mon o0 o1 o2 o3 (EQ0: eq o0 o1) (EQ1: eq o2 o3):
    eq (union o0 o2) (union o1 o3).
  Proof.
    split.
    - eapply union_le_mon.
      + eapply EQ0.
      + eapply EQ1.
    - eapply union_le_mon.
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
      eapply next_mon; eauto. eapply rec_le; auto.
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
      - eapply (@dle_transitive (djoin (fun x => next (rec (unit_rect (fun _ : unit => t) o x))))); auto.
        { eapply djoin_wf; auto. }
        + eapply (djoin_upperbound (fun x : unit => next (rec (unit_rect (fun _ : unit => t) o x))) tt); auto.
        + eapply (@djoin_upperbound _ (fun b: bool => if b then base else djoin (fun x => next (rec (unit_rect (fun _ : unit => t) o x)))) false); auto.
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
              destruct a. destruct (os x) eqn:EQ; auto.
              eapply (@dle_transitive (rec (build os0))); auto.
              { eapply (@dle_transitive (rec (S (os0 y)))); auto.
                { eapply rec_S. }
                { eapply rec_le. eapply S_spec. eapply build_upperbound. }
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
            i. eapply rec_le. eapply join_upperbound. }
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
      hexploit (@rec_eq (join os) o).
      { eapply is_join_eq; eauto. eapply join_is_join; auto. }
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
      hexploit (@rec_eq (join os) o).
      { eapply is_join_eq; eauto. eapply join_is_join; auto. }
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

    Lemma orec_le (o0 o1: t) (LE: le o0 o1): le (orec o0) (orec o1).
    Proof.
      unfold orec. eapply rec_le with (wf:=wf); auto.
    Qed.

    Lemma orec_eq (o0 o1: t) (EQ: eq o0 o1): eq (orec o0) (orec o1).
    Proof.
      unfold orec. eapply rec_eq with (wf:=wf); auto.
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

  Let flip A B C (f: A -> B -> C): B -> A -> C := fun b a => f a b.

  Section ARITHMETIC.

    Lemma orec_of_S: forall o, eq o (orec O S o).
    Proof.
      induction o; ss. split.
      { eapply build_spec. i. eapply lt_le_lt.
        2: { eapply (@join_upperbound _ (fun b : bool => if b then O else join (fun x : A => S (orec O S (os x)))) false). }
        eapply eq_lt_lt.
        { eapply H. }
        eapply lt_le_lt.
        { eapply S_lt. }
        { eapply (@join_upperbound _ (fun x : A => S (orec O S (os x))) a). }
      }
      { eapply join_supremum. i. destruct a; ss.
        eapply join_supremum. i.
        eapply S_spec. eapply eq_lt_lt.
        { symmetry. eapply H. }
        { eapply build_upperbound. }
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

      Let _S_le_mon o0 o1 (LE: le o0 o1): le (S o0) (S o1).
      Proof.
        rewrite <- S_le_mon. auto.
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

      Lemma add_le_r o0 o1 o2 (LE: le o1 o2)
        :
          le (add o0 o1) (add o0 o2).
      Proof.
        eapply orec_le; auto.
      Qed.

      Lemma add_lt_r o0 o1 o2 (LT: lt o1 o2)
        :
          lt (add o0 o1) (add o0 o2).
      Proof.
        eapply S_spec in LT.
        eapply lt_le_lt.
        2: { eapply add_le_r. eapply LT. }
        eapply lt_eq_lt.
        { eapply add_S. }
        eapply S_lt.
      Qed.

      Lemma add_eq_r o0 o1 o2 (EQ: eq o1 o2)
        :
          eq (add o0 o1) (add o0 o2).
      Proof.
        split.
        - eapply add_le_r; eauto. eapply EQ.
        - eapply add_le_r; eauto. eapply EQ.
      Qed.

      Lemma add_le_l o0 o1 o2 (LE: le o0 o1)
        :
          le (add o0 o2) (add o1 o2).
      Proof.
        eapply (@orec_mon o0 S o1 S); auto.
      Qed.

      Lemma add_eq_l o0 o1 o2 (EQ: eq o0 o1)
        :
          eq (add o0 o2) (add o1 o2).
      Proof.
        split.
        - eapply add_le_l; eauto. eapply EQ.
        - eapply add_le_l; eauto. eapply EQ.
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
          eapply add_eq_r; auto.
          { symmetry. eapply add_build. }
        }
        etransitivity.
        2: { symmetry. eapply add_union; auto. }
        split.
        { eapply union_spec.
          { eapply union_l. }
          { eapply join_supremum. i. etransitivity.
            { erewrite <- S_le_mon. eapply H. }
            etransitivity.
            2: { eapply union_r. }
            etransitivity.
            2: {
              eapply add_le_r.
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
          eapply join_le. i. exists a0.
          etransitivity.
          { eapply add_S. }
          { erewrite <- S_le_mon. eapply H. }
        }
      Qed.
    End ADD.


    Section MULT.
      Definition mult (o0: t): forall (o1: t), t := orec O (flip add o0).

      Let mult_gen_le o0 o1: le o1 (flip add o0 o1).
      Proof.
        eapply add_base_l.
      Qed.

      Let mult_gen_mon o o0 o1 (LE: le o0 o1): le (flip add o o0) (flip add o o1).
      Proof.
        eapply add_le_l. auto.
      Qed.

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
        { eapply union_le. eapply O_bot. }
      Qed.

      Lemma mult_build o A (os: A -> t)
        :
          eq (mult o (build os)) (join (fun a => add (mult o (os a)) o)).
      Proof.
        transitivity (union O (join (fun a => add (mult o (os a)) o))).
        { eapply (@orec_build O (flip add _)); eauto. }
        { eapply union_le. eapply O_bot. }
      Qed.

      Lemma mult_union o0 o1 o2
        :
          eq (mult o0 (union o1 o2)) (union (mult o0 o1) (mult o0 o2)).
      Proof.
        eapply orec_union; auto.
      Qed.

      Lemma mult_le_r o0 o1 o2 (LE: le o1 o2)
        :
          le (mult o0 o1) (mult o0 o2).
      Proof.
        eapply orec_le; auto.
      Qed.

      Lemma mult_eq_r o0 o1 o2 (EQ: eq o1 o2)
        :
          eq (mult o0 o1) (mult o0 o2).
      Proof.
        split.
        - eapply mult_le_r; eauto. eapply EQ.
        - eapply mult_le_r; eauto. eapply EQ.
      Qed.

      Lemma mult_le_l o0 o1 o2 (LE: le o0 o1)
        :
          le (mult o0 o2) (mult o1 o2).
      Proof.
        eapply (@orec_mon O (flip add o0) O (flip add o1)); auto.
        { reflexivity. }
        { i. unfold flip. transitivity (add o4 o0).
          { eapply add_le_l; auto. }
          { eapply add_le_r; auto. }
        }
      Qed.

      Lemma mult_eq_l o0 o1 o2 (EQ: eq o0 o1)
        :
          eq (mult o0 o2) (mult o1 o2).
      Proof.
        split.
        - eapply mult_le_l; eauto. eapply EQ.
        - eapply mult_le_l; eauto. eapply EQ.
      Qed.

      Lemma mult_lt_r o0 o1 o2 (LT: lt o1 o2) (NZERO: lt O o0)
        :
          lt (mult o0 o1) (mult o0 o2).
      Proof.
        eapply S_spec in LT.
        eapply lt_le_lt.
        2: { eapply mult_le_r. eapply LT. }
        eapply lt_eq_lt.
        { eapply mult_S. }
        eapply S_spec in NZERO.
        eapply lt_le_lt.
        2: { eapply add_le_r. eapply NZERO. }
        eapply lt_eq_lt.
        { eapply add_S. }
        eapply lt_eq_lt.
        { erewrite <- S_eq_mon. eapply add_O_r. }
        eapply S_lt.
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

      Lemma mult_1_r o: eq (mult o (from_nat 1)) o.
      Proof.
        unfold from_nat. etransitivity.
        { eapply mult_S. }
        etransitivity.
        { eapply add_eq_l. eapply mult_O_r. }
        eapply add_O_l.
      Qed.

      Lemma mult_1_l o: eq (mult (from_nat 1) o) o.
      Proof.
        unfold from_nat. transitivity (orec O S o).
        2: { symmetry. eapply orec_of_S. }
        split.
        { eapply orec_mon.
          { reflexivity. }
          { i. unfold flip. etransitivity.
            { eapply add_S. }
            { rewrite <- S_le_mon. transitivity o0; auto.
              eapply add_O_r.
            }
          }
        }
        { eapply orec_mon.
          { reflexivity. }
          { i. unfold flip. etransitivity.
            { rewrite <- S_le_mon. eapply LE. }
            transitivity (S (add o1 O)); auto.
            { rewrite <- S_le_mon. eapply add_O_r. }
            { eapply add_S. }
          }
        }
      Qed.

      Lemma mult_dist o0 o1 o2: eq (mult o0 (add o1 o2)) (add (mult o0 o1) (mult o0 o2)).
      Proof.
        revert o0 o1. induction o2. i. etransitivity.
        { eapply mult_eq_r. eapply add_build. }
        etransitivity.
        2: { eapply add_eq_r. symmetry. eapply mult_build. }
        etransitivity.
        { eapply mult_union. }
        etransitivity.
        { eapply union_eq_mon.
          { reflexivity. }
          { eapply mult_join. }
        }
        etransitivity.
        2: { symmetry. eapply add_join. }
        eapply union_eq_mon.
        { reflexivity. } split.
        { eapply join_le. i. exists a0.
          etransitivity.
          { eapply mult_S. }
          etransitivity.
          { eapply add_eq_l. symmetry. eapply H. }
          eapply add_assoc.
        }
        { eapply join_le. i. exists a0.
          etransitivity.
          { eapply add_assoc. }
          etransitivity.
          { eapply add_eq_l. eapply H. }
          eapply mult_S.
        }
      Qed.

      Lemma mult_assoc o0 o1 o2: eq (mult (mult o0 o1) o2) (mult o0 (mult o1 o2)).
      Proof.
        revert o0 o1. induction o2. i. etransitivity.
        { eapply mult_build. } etransitivity.
        2: {
          eapply mult_eq_r; auto.
          { symmetry. eapply mult_build. }
        }
        etransitivity.
        2: { symmetry. eapply mult_join. }
        split.
        { eapply join_le. i. exists a0.
          etransitivity.
          { eapply add_le_l. eapply H. }
          { eapply mult_dist. }
        }
        { eapply join_le. i. exists a0.
          etransitivity.
          { eapply mult_dist. }
          { eapply add_le_l. eapply H. }
        }
      Qed.
    End MULT.

    Definition expn (o0: t): forall (o1: t), t := orec (S O) (flip mult o0).
  End ARITHMETIC.

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
        { eapply (@rec_eq _ base next djoin dle wf); auto.
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

  Section KAPPA.
    Let U := Type.
    Variable X: U.

    Record inaccessible (base: t) (next: t -> t) (k: t): Prop :=
      mk_inaccessible
        { inaccessible_base: lt base k;
          inaccessible_next: forall o (LT: lt o k), lt (next o) k;
          inaccessible_join: forall (os: X -> t) (LT: forall a, lt (os a) k),
              lt (join os) k;
          inaccessible_union: forall o0 o1 (LT0: lt o0 k) (LT1: lt o1 k),
              lt (union o0 o1) k;
        }.

    Lemma inaccessible_mon base0 base1 next0 next1 k
          (BASE: lt base0 k)
          (NEXT: forall o (LT: lt o k), le (next0 o) (next1 o))
          (INACCESSIBLE: inaccessible base1 next1 k)
      :
        inaccessible base0 next0 k.
    Proof.
      econs.
      { des; auto. }
      { i. eapply le_lt_lt; eauto.
        eapply INACCESSIBLE.(inaccessible_next). auto. }
      { eapply INACCESSIBLE.(inaccessible_join). }
      { eapply INACCESSIBLE. }
    Qed.

    Definition S_inaccessible (k: t): Prop := inaccessible O S k.

    Inductive tree: U :=
    | tree_O
    | tree_S (tr: tree)
    | tree_join (trs: X -> tree)
    | tree_union (tr0 tr1: tree)
    .

    Definition tree_lt (tr0 tr1: tree): Prop :=
      match tr1 with
      | tree_O => False
      | tree_S tr => tr0 = tr
      | tree_join trs => exists x, tr0 = trs x
      | tree_union trl trr => tr0 = trl \/ tr0 = trr
      end.

    Lemma tree_lt_well_founded: well_founded tree_lt.
    Proof.
      ii. induction a.
      { econs. ii. ss. }
      { econs. i. ss. subst. auto. }
      { econs. i. ss. des. subst. auto. }
      { econs. i. ss. des; subst; auto. }
    Qed.

    Lemma tree_O_O: eq (from_wf tree_lt_well_founded tree_O) O.
    Proof.
      split.
      { unfold from_wf. destruct (tree_lt_well_founded tree_O).
        ss. econs. i. destruct a0. ss. }
      { eapply O_bot. }
    Qed.

    Lemma tree_S_S tr:
      eq (from_wf tree_lt_well_founded (tree_S tr)) (S (from_wf tree_lt_well_founded tr)).
    Proof.
      split.
      { unfold from_wf at 1. destruct (tree_lt_well_founded (tree_S tr)).
        ss. econs. i. destruct a0. ss. subst. exists tt.
        ss. eapply same_acc_le.
      }
      { eapply S_spec. eapply from_wf_lt. ss. }
    Qed.

    Lemma tree_join_build (trs: X -> tree):
      eq (from_wf tree_lt_well_founded (tree_join trs)) (build (fun x => from_wf tree_lt_well_founded (trs x))).
    Proof.
      split.
      { unfold from_wf at 1. destruct (tree_lt_well_founded (tree_join trs)).
        ss. econs. i. destruct a0. des. ss. subst. exists x0.
        ss. eapply same_acc_le.
      }
      { eapply build_spec. i. eapply from_wf_lt. ss. eauto. }
    Qed.

    Lemma tree_union_union_le (tr0 tr1: tree):
      le (from_wf tree_lt_well_founded (tree_union tr0 tr1)) (S (union (from_wf tree_lt_well_founded tr0) (from_wf tree_lt_well_founded tr1))).
    Proof.
      unfold from_wf at 1. destruct (tree_lt_well_founded (tree_union tr0 tr1)).
      ss. econs. i. destruct a0. ss. exists tt. ss. des; subst.
      { transitivity (from_wf tree_lt_well_founded tr0).
        { eapply same_acc_le. }
        { eapply union_l. }
      }
      { transitivity (from_wf tree_lt_well_founded tr1).
        { eapply same_acc_le. }
        { eapply union_r. }
      }
    Qed.

    Lemma tree_union_union_le_rev (tr0 tr1: tree):
      le (union (from_wf tree_lt_well_founded tr0) (from_wf tree_lt_well_founded tr1)) (from_wf tree_lt_well_founded (tree_union tr0 tr1)).
    Proof.
      eapply union_spec.
      { eapply lt_le. eapply from_wf_lt. ss. auto. }
      { eapply lt_le. eapply from_wf_lt. ss. auto. }
    Qed.

    Definition kappa := from_wf_set tree_lt_well_founded.

    Lemma inaccessible_rec_inaccessible (base0: t) (next: t -> t)
          (NEXTLE: forall o, le o (next o))
          (NEXTMON: forall o0 o1 (LE: le o0 o1), le (next o0) (next o1))
          (INACCESSIBLE: inaccessible base0 next kappa)
          base1
          (BASE1: lt base1 kappa)
      :
        inaccessible base0 (orec base1 next) kappa.
    Proof.
      econs; eauto.
      { eapply INACCESSIBLE. }
      2: { eapply INACCESSIBLE. }
      2: { eapply INACCESSIBLE. }
      assert (RECS: forall tr, lt (orec base1 next (from_wf tree_lt_well_founded tr)) kappa).
      { induction tr.
        { eapply (@eq_lt_lt _ _ base1); auto.
          transitivity (orec base1 next O).
          { eapply orec_eq; auto. eapply tree_O_O. }
          { eapply orec_O; auto. }
        }
        { eapply (@eq_lt_lt _ _ (next (orec base1 next (from_wf tree_lt_well_founded tr)))).
          { transitivity (orec base1 next (S (from_wf tree_lt_well_founded tr))).
            { eapply orec_eq; auto. eapply tree_S_S. }
            { eapply orec_S; auto. }
          }
          { eapply INACCESSIBLE. auto. }
        }
        { eapply (@eq_lt_lt _ _ _).
          { etransitivity.
            { eapply orec_eq; auto. eapply tree_join_build. }
            { eapply orec_build. }
          }
          { eapply INACCESSIBLE; auto. eapply INACCESSIBLE. i.
            eapply INACCESSIBLE. auto. }
        }
        { eapply le_lt_lt.
          { eapply orec_le.
            { auto. }
            { eapply tree_union_union_le. }
          }
          eapply eq_lt_lt.
          { eapply orec_S; auto. }
          eapply INACCESSIBLE.
          eapply eq_lt_lt.
          { eapply orec_union; auto. }
          { eapply INACCESSIBLE; auto. }
        }
      }
      i. eapply lt_inv in LT. des. eapply (@le_lt_lt (orec base1 next (from_wf tree_lt_well_founded a))); auto.
      eapply orec_le; auto.
    Qed.

    Lemma kappa_O
      :
        lt O kappa.
    Proof.
      econs. instantiate (1:=tree_O). eapply O_bot.
    Qed.

    Lemma kappa_S o (LT: lt o kappa)
      :
        lt (S o) kappa.
    Proof.
      i. eapply lt_inv in LT. des.
      econs. instantiate (1:=tree_S a).
      eapply S_spec. eapply le_lt_lt; eauto.
      eapply from_wf_lt. ss.
    Qed.

    Lemma kappa_union o0 o1 (LT0: lt o0 kappa) (LT1: lt o1 kappa)
      :
        lt (union o0 o1) kappa.
    Proof.
      eapply lt_inv in LT0. eapply lt_inv in LT1. des.
      econs. instantiate (1:=tree_union a0 a). eapply union_spec.
      { etransitivity; eauto. eapply lt_le. eapply from_wf_lt. ss. auto. }
      { etransitivity; eauto. eapply lt_le. eapply from_wf_lt. ss. auto. }
    Qed.

    Hypothesis CHOICE: FunctionalChoice_on X tree.

    Lemma kappa_join (os: X -> t) (LT: forall x, lt (os x) kappa)
      :
        lt (join os) kappa.
    Proof.
      i. hexploit (CHOICE (fun (x: X) (tr: tree) => le (os x) (from_wf tree_lt_well_founded tr))).
      { i. specialize (LT x). eapply lt_inv in LT. eauto. }
      i. des.
      econs. instantiate (1:=tree_join f).
      eapply join_supremum. i. etransitivity; eauto.
      eapply lt_le. eapply from_wf_lt. ss. eauto.
    Qed.

    Lemma kappa_S_inaccessible
      :
        S_inaccessible kappa.
    Proof.
      econs.
      { eapply kappa_O. }
      { eapply kappa_S. }
      { eapply kappa_join. }
      { eapply kappa_union. }
    Qed.

    Lemma kappa_add_inaccessible
          o (LT: lt o kappa)
      :
        inaccessible O (add o) kappa.
    Proof.
      eapply inaccessible_rec_inaccessible; eauto.
      { i. eapply S_le. }
      { i. rewrite <- S_le_mon. auto. }
      { eapply kappa_S_inaccessible. }
    Qed.

    Lemma kappa_add o0 o1 (LT0: lt o0 kappa) (LT1: lt o1 kappa)
      :
        lt (add o0 o1) kappa.
    Proof.
      eapply kappa_add_inaccessible; auto.
    Qed.

    Lemma kappa_flip_add_inaccessible
          o (LT: lt o kappa)
      :
        inaccessible O (flip add o) kappa.
    Proof.
      hexploit kappa_add_inaccessible; eauto. i.
      econs; auto.
      { eapply le_lt_lt; eauto. eapply O_bot. }
      { i. eapply (@kappa_add_inaccessible _ LT0).(inaccessible_next). auto. }
      { i. eapply H. auto. }
      { i. eapply H; auto. }
    Qed.

    Lemma kappa_mult_inaccessible
          o (LT: lt o kappa)
      :
        inaccessible O (mult o) kappa.
    Proof.
      eapply inaccessible_rec_inaccessible; eauto.
      { i. eapply add_base_l. }
      { i. eapply add_le_l; auto. }
      { eapply kappa_flip_add_inaccessible. auto. }
      { eapply le_lt_lt; eauto. eapply O_bot. }
    Qed.

    Lemma kappa_mult o0 o1 (LT0: lt o0 kappa) (LT1: lt o1 kappa)
      :
        lt (mult o0 o1) kappa.
    Proof.
      eapply kappa_mult_inaccessible; auto.
    Qed.

    Lemma kappa_flip_mult_inaccessible
          o (LT: lt o kappa)
      :
        inaccessible O (flip mult o) kappa.
    Proof.
      hexploit kappa_mult_inaccessible; eauto. i.
      econs; auto.
      { eapply le_lt_lt; eauto. eapply O_bot. }
      { i. eapply (@kappa_mult_inaccessible _ LT0).(inaccessible_next). auto. }
      { i. eapply H. auto. }
      { i. eapply H; auto. }
    Qed.
  End KAPPA.
End TYPE.
End Ordinal.
