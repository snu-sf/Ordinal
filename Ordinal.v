From Paco Require Import paco.
From sflib Require Import sflib.

Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms. (* TODO: Use Morphisms *)
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.
Require Import Program.

Set Implicit Arguments.
Set Primitive Projections.

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

  Lemma lt_eq_or_le o0 o1:
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
    @build (sigT (fun a0 => R a0 a1)) (fun a0p =>
                                      @from_acc _ R (projT1 a0p) _).
  Next Obligation.
    inv ACC. eapply H; eauto.
  Defined.

  Arguments from_acc [A R] a1 ACC.

  Lemma from_acc_lt A (R: A -> A -> Prop) (a0 a1: A) (LT: R a0 a1)
        (ACC1: Acc R a1) (ACC0: Acc R a0)
    :
      lt (from_acc a0 ACC0) (from_acc a1 ACC1).
  Proof.
    destruct ACC1. ss.
    set (existT (fun a0 => R a0 a1) a0 LT).
    replace ACC0 with (from_acc_obligation_1 (Acc_intro a1 a) s).
    2: { eapply proof_irrelevance. }
    eapply (build_upperbound (fun a0p => from_acc (projT1 a0p) (from_acc_obligation_1 (Acc_intro a1 a) a0p)) s).
  Qed.

  Definition from_wf A (R: A -> A -> Prop) (WF: well_founded R) (a1: A): t :=
    from_acc a1 (WF a1).

  Lemma from_wf_lt A (R: A -> A -> Prop) (WF: well_founded R) (a0 a1: A) (LT: R a0 a1)
    :
      lt (from_wf WF a0) (from_wf WF a1).
  Proof.
    eapply from_acc_lt; eauto.
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
    Lemma le_lemma o0 B1 (os1: B1 -> t)
          (LE: forall B0 os0 (b0: B0)
                      (EQ: o0 = @build B0 os0),
              exists b1, le (os0 b0) (os1 b1))
    :
      le o0 (build os1).
    Proof.
      destruct o0. econs. i. exploit LE; eauto.
    Defined.

    Definition T:= Type.
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
      assert (os0 b0 = match os a as t0 return (match t0 with
                                                | @build B _ => B
                                                end -> t) with
                       | @build A0 os1 => fun y : A0 => os1 y
                       end s).
      2: { rewrite H. reflexivity. }
      unfold s. rewrite EQ. ss.
    Qed.

    Lemma build_fst_eq A0 A1 os0 os1 (EQ: @build A0 os0 = @build A1 os1):
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
    - i. eapply lt_le. econs. reflexivity.
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

    Variable base: D.
    Variable next: D -> D.

    Context `{dle_PreOrder: PreOrder _ dle}.
    Hypothesis djoin_upperbound: forall A (ds: A -> D) (a: A), dle (ds a) (djoin ds).
    Hypothesis djoin_supremum: forall A (ds: A -> D) (d: D) (LE: forall a, dle (ds a) d), dle (djoin ds) d.
    Hypothesis djoin_wf: forall A (ds: A -> D) (WF: forall a, wf (ds a)), wf (djoin ds).

    Hypothesis base_wf: wf base.
    Hypothesis next_wf: forall d (WF: wf d), wf (next d).

    Hypothesis next_le: forall d (WF: wf d), dle d (next d).
    Hypothesis next_mon: forall d0 d1 (LE: dle d0 d1), dle (next d0) (next d1).

    Let deq: D -> D -> Prop :=
      fun d0 d1 => dle d0 d1 /\ dle d1 d0.

    Global Program Instance deq_Equivalence: Equivalence deq.
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

    Let dunion (d0 d1: D): D := djoin (fun b: bool => if b then d0 else d1).

    Lemma dunion_l d0 d1: dle d0 (dunion d0 d1).
    Proof.
      eapply (djoin_upperbound (fun b: bool => if b then d0 else d1) true).
    Qed.

    Lemma dunion_r d0 d1: dle d1 (dunion d0 d1).
    Proof.
      eapply (djoin_upperbound (fun b: bool => if b then d0 else d1) false).
    Qed.

    Lemma dunion_spec d0 d1 d (LEFT: dle d0 d) (RIGHT: dle d1 d): dle (dunion d0 d1) d.
    Proof.
      eapply djoin_supremum. i. destruct a; auto.
    Qed.

    Lemma djoin_le A0 A1 (ds0: A0 -> D) (ds1: A1 -> D)
          (LE: forall a0, exists a1, dle (ds0 a0) (ds1 a1))
      :
        dle (djoin ds0) (djoin ds1).
    Proof.
      eapply djoin_supremum. i. specialize (LE a). des.
      etransitivity; eauto.
    Qed.

    Fixpoint rec (o: t): D :=
      match o with
      | @build X xs =>
        dunion base (djoin (fun x => next (rec (xs x))))
      end.

    Lemma rec_wf o: wf (rec o).
    Proof.
      induction o. ss. eapply djoin_wf. i. destruct a.
      - eapply base_wf.
      - eapply djoin_wf. i. eapply next_wf. auto.
    Qed.

    Lemma le_rec (o0 o1: t) (LE: le o0 o1): dle (rec o0) (rec o1).
    Proof.
      revert o0 LE. induction o1. i. dependent destruction LE. ss.
      eapply dunion_spec.
      { eapply dunion_l. }
      etransitivity; [|eapply dunion_r].
      eapply djoin_le. i. specialize (LE a0). des. exists a1.
      exploit H; eauto.
    Qed.

    Lemma eq_rec (o0 o1: t) (EQ: eq o0 o1): deq (rec o0) (rec o1).
    Proof.
      split.
      - eapply le_rec. eapply EQ.
      - eapply le_rec. eapply EQ.
    Qed.

    Lemma rec_O: deq (rec O) base.
    Proof.
      ss. split.
      - eapply dunion_spec.
        + reflexivity.
        + eapply djoin_supremum. ss.
      - eapply dunion_l.
    Qed.

    Lemma rec_is_O o (ZERO: is_O o): deq (rec o) base.
    Proof.
      transitivity (rec O).
      - eapply eq_rec. eapply is_O_eq; auto. eapply O_is_O.
      - eapply rec_O.
    Qed.

    Lemma rec_le_base o: dle base (rec o).
    Proof.
      transitivity (rec O).
      - eapply rec_O.
      - eapply le_rec. eapply O_bot.
    Qed.

    Lemma rec_S o: deq (rec (S o)) (next (rec o)).
    Proof.
      ss. split.
      - eapply dunion_spec.
        + transitivity (rec o).
          * eapply rec_le_base.
          * eapply next_le. eapply rec_wf.
        + eapply djoin_supremum. i.
          destruct a. ss. reflexivity.
      - etransitivity; [|eapply dunion_r].
        etransitivity; [|eapply djoin_upperbound].
        instantiate (1:=tt). ss. reflexivity.
    Qed.

    Lemma rec_is_S o s (SUCC: is_S o s): deq (rec s) (next (rec o)).
    Proof.
      transitivity (rec (S o)).
      - eapply eq_rec. eapply is_S_eq; eauto. eapply S_is_S.
      - eapply rec_S.
    Qed.

    Lemma rec_build A (os: A -> t)
          (INHABITED: inhabited A) (OPEN: open os)
      : deq (rec (build os)) (djoin (fun a => rec (os a))).
    Proof.
      split.
      - ss. eapply dunion_spec.
        + destruct INHABITED. transitivity (rec (os X)).
          * eapply rec_le_base.
          * eapply (djoin_upperbound (fun a => rec (os a)) X).
        + eapply djoin_le. i. specialize (OPEN a0). des. exists a1.
          transitivity (rec (S (os a0))).
          * eapply rec_S.
          * eapply le_rec. eapply S_spec. auto.
      - ss. etransitivity; [|eapply dunion_r].
        eapply djoin_le. i. exists a0. eapply next_le. eapply rec_wf.
    Qed.

    Lemma rec_is_join A (os: A -> t) o
          (INHABITED: inhabited A) (OPEN: open os) (JOIN: is_join os o)
      : deq (rec o) (djoin (fun a => rec (os a))).
    Proof.
      transitivity (rec (build os)).
      - eapply eq_rec. eapply is_join_eq.
        + eauto.
        + eapply build_is_join. auto.
      - eapply rec_build; auto.
    Qed.

    Lemma rec_join A (os: A -> t)
          (INHABITED: inhabited A) (OPEN: open os)
      : deq (rec (join os)) (djoin (fun a => rec (os a))).
    Proof.
      eapply rec_is_join; auto. eapply join_is_join.
    Qed.
  End REC.

  Section OREC.
    Variable base: t.
    Variable next: t -> t.

    Definition orec: t -> t := rec join base next.

    Hypothesis next_le: forall o, le o (next o).
    Hypothesis next_mon: forall o0 o1 (LE: le o0 o1), le (next o0) (next o1).

    Let le_PreOrder := le_PreOrder.
    Let join_upperbound := join_upperbound.
    Let join_supremum := join_supremum.

    Lemma le_orec (o0 o1: t) (LE: le o0 o1): le (orec o0) (orec o1).
    Proof.
      unfold orec. eapply le_rec; eauto.
    Qed.

    Lemma eq_orec (o0 o1: t) (EQ: eq o0 o1): eq (orec o0) (orec o1).
    Proof.
      unfold orec. eapply eq_rec; eauto.
    Qed.

    Lemma orec_is_O (o: t) (ZERO: is_O o): eq (orec o) base.
    Proof.
      unfold orec. eapply rec_is_O; eauto.
    Qed.

    Lemma orec_is_S o s (SUCC: is_S o s): eq (orec s) (next (orec o)).
    Proof.
      unfold orec. eapply rec_is_S; eauto.
      - instantiate (1:=fun _ => True). i. ss.
      - ss.
      - ss.
    Qed.

    Lemma orec_is_join A (os: A -> t) o
          (INHABITED: inhabited A) (OPEN: open os) (JOIN: is_join os o)
      : eq (orec o) (join (fun a => orec (os a))).
    Proof.
      unfold orec. eapply rec_is_join; eauto.
      - instantiate (1:=fun _ => True). i. ss.
      - ss.
      - ss.
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
