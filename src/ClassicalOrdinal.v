From Ordinal Require Import sflib Basics WfRel Totalness.
From Ordinal Require Export Ordinal.

Require Import ClassicalChoice.

Set Implicit Arguments.
Set Primitive Projections.

Module ClassicOrd.
  Lemma trichotomy o0 o1: Ord.lt o0 o1 \/ Ord.eq o0 o1 \/ Ord.lt o1 o0.
  Proof.
    eapply excluded_middle_imply_totalness. eapply classic.
  Qed.

  Lemma total o0 o1: Ord.le o0 o1 \/ Ord.lt o1 o0.
  Proof.
    destruct (trichotomy o0 o1) as [|[]]; auto.
    { left. apply Ord.lt_le. auto. }
    { left. apply H. }
  Qed.

  Lemma total_le o0 o1: Ord.le o0 o1 \/ Ord.le o1 o0.
  Proof.
    destruct (total o0 o1); auto. right. eapply Ord.lt_le. auto.
  Qed.

  Lemma le_eq_or_lt o0 o1:
    Ord.le o0 o1 <-> (Ord.lt o0 o1 \/ Ord.eq o0 o1).
  Proof.
    split; i.
    - destruct (total o1 o0).
      + right. split; auto.
      + left. auto.
    - destruct H.
      + eapply Ord.lt_le; auto.
      + destruct H. auto.
  Qed.

  Lemma from_acc_complete A (R: A -> A -> Prop) a1 (ACC1: Acc R a1)
        o (LT: Ord.lt o (Ord.from_acc ACC1))
    :
      exists a0 (ACC0: Acc R a0), Ord.eq o (Ord.from_acc ACC0).
  Proof.
    dup ACC1. revert o LT. induction ACC0. i. destruct ACC1.
    ss. eapply Ord.lt_inv in LT. des. destruct a0 as [a0 p0]. ss.
    eapply le_eq_or_lt in LT. des; eauto.
  Qed.

  Lemma from_wf_complete A (R: A -> A -> Prop) (WF: well_founded R) a1
        o (LT: Ord.lt o (Ord.from_wf WF a1))
    :
      exists a0, Ord.eq o (Ord.from_wf WF a0).
  Proof.
    eapply from_acc_complete in LT. des. exists a0.
    unfold Ord.from_wf. etransitivity.
    { eapply LT. }
    { eapply Ord.same_acc_eq. }
  Qed.

  Lemma from_wf_set_complete A (R: A -> A -> Prop) (WF: well_founded R)
        o (LT: Ord.lt o (Ord.from_wf_set WF))
    :
      exists a, Ord.eq o (Ord.from_wf WF a).
  Proof.
    eapply Ord.lt_inv in LT. des. eapply le_eq_or_lt in LT. des; eauto.
    eapply from_wf_complete in LT. eauto.
  Qed.

  Lemma from_wf_set_lt A (R0 R1: A -> A -> Prop) (INCL: forall a0 a1 (LE: R0 a0 a1), R1 a0 a1)
        (WF0: well_founded R0) (WF1: well_founded R1)
        (TOP: exists a2 x, R1 x a2 /\ forall a0 a1 (LT: R0 a0 a1), R1 a1 a2)
    :
      Ord.lt (Ord.from_wf_set WF0) (Ord.from_wf_set WF1).
  Proof.
    des. eapply Ord.lt_intro with (a:=a2).
    unfold Ord.from_wf. destruct (WF1 a2). ss. econs. intros a1.
    destruct (classic (exists a0, R0 a0 a1)).
    - des. exists (exist _ a1 (TOP0 _ _ H)). ss.
      unfold Ord.from_wf. eapply from_acc_mon; auto.
    - exists (exist _ x TOP). ss.
      unfold Ord.from_wf. destruct (WF0 a1), (a x TOP). econs. i.
      exfalso. destruct a4. eapply H; eauto.
  Qed.

  Definition is_meet (P: Ord.t -> Prop) (o0: Ord.t): Prop :=
    P o0 /\ forall o1 (IN: P o1), Ord.le o0 o1.

  Lemma meet_exists (P: Ord.t -> Prop) (INHABITED: exists o, P o):
    exists o0, is_meet P o0.
  Proof.
    apply NNPP. ii. des.
    hexploit (well_founded_induction Ord.lt_well_founded (fun o => ~ P o)); eauto.
    ii. eapply not_ex_all_not in H. instantiate (1:=x) in H.
    apply not_and_or in H. des; ss. eapply H. i.
    destruct (total x o1); auto. eapply H0 in H2. ss.
  Qed.

  Lemma limit_or_S o:
    (exists o0, Ord.is_S o0 o) \/
    (exists A (os: A -> Ord.t), Ord.is_join os o /\ Ord.open os).
  Proof.
    destruct o. destruct (classic (forall a0, exists a1, Ord.lt (os a0) (os a1))).
    - right. exists A, os. split; auto. split.
      + i. eapply Ord.lt_le. eapply Ord.build_upperbound.
      + i. eapply Ord.build_supremum. i. specialize (H a). des.
        eapply Ord.lt_le_lt; eauto.
    - left. eapply not_all_ex_not in H. des.
      exists (os n). split.
      + eapply Ord.build_upperbound.
      + i. eapply Ord.build_supremum. i. destruct (total (os a) (os n)); auto.
        * eapply Ord.le_lt_lt; eauto.
        * exfalso. eapply H; eauto.
  Qed.

  Lemma ind
        (P: Ord.t -> Prop)
        (ZERO: forall o (ZERO: Ord.is_O o)
                      (HELPER: forall o' (LT: Ord.lt o' o), P o'), P o)
        (SUCC: forall o s (SUCC: Ord.is_S o s) (IH: P o)
                      (HELPER: forall o' (LT: Ord.lt o' s), P o'), P s)
        (LIMIT: forall A (os: A -> Ord.t) o (JOIN: Ord.is_join os o)
                       (INHABITED: inhabited A) (OPEN: Ord.open os)
                       (IH: forall a, P (os a))
                       (HELPER: forall o' (LT: Ord.lt o' o), P o'), P o)
    :
      forall o, P o.
  Proof.
    eapply well_founded_induction.
    { eapply Ord.lt_well_founded. }
    i. destruct (limit_or_S x).
    - des. eapply SUCC; eauto. eapply H. eapply H0.
    - des. destruct (classic (inhabited A)).
      + eapply LIMIT; eauto. i. eapply H.
        specialize (H1 a). des. eapply Ord.lt_le_lt; eauto. eapply H0.
      + eapply ZERO; eauto. ii. eapply H0.
        i. exfalso. eapply H2. eauto.
  Qed.

  Section REC.
    Variable D: Type.
    Variable base: D.
    Variable next: D -> D.
    Variable djoin: forall (A: Type) (ds: A -> D), D.

    Variable dle: D -> D -> Prop.
    Variable wf: D -> Prop.

    Let deq: D -> D -> Prop :=
      fun d0 d1 => dle d0 d1 /\ dle d1 d0.

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

    Let rec := Ord.rec base next djoin.

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

    Let rec_all (o1: Ord.t):
      (forall o0 (LE: Ord.le o0 o1), dle (rec o0) (rec o1)) /\
      (forall o0 (LT: Ord.lt o0 o1), dle (next (rec o0)) (rec o1)) /\
      (wf (rec o1)) /\
      (dle base (rec o1))
    .
    Proof.
      revert o1.
      eapply (well_founded_induction Ord.lt_well_founded); auto.
      intros o1 IH. destruct o1. ss.

      assert (IHS0:
                forall
                  A0 (os0: A0 -> Ord.t)
                  (LE: forall a0, exists a, Ord.le (os0 a0) (os a))
                  a0,
                  (forall o0 (LE: Ord.le o0 (os0 a0)), dle (rec o0) (rec (os0 a0))) /\
                  (forall o0 (LT: Ord.lt o0 (os0 a0)), dle (next (rec o0)) (rec (os0 a0))) /\
                  wf (rec (os0 a0)) /\ dle base (rec (os0 a0))).
      { i. eapply IH. hexploit (LE a0); eauto. i. des. econs; eauto. }
      assert (CHAIN0:
                forall
                  A0 (os0: A0 -> Ord.t)
                  (LE: forall a0, exists a, Ord.le (os0 a0) (os a))
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
                  A0 (os0: A0 -> Ord.t)
                  (LE: forall a0, exists a, Ord.le (os0 a0) (os a))
                  a,
                  wf (next (rec (os0 a)))).
      { i. eapply next_wf. eapply IHS0; eauto. }
      assert (CHAINU0:
                forall
                  A0 (os0: A0 -> Ord.t)
                  (LE: forall a0, exists a, Ord.le (os0 a0) (os a))
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
                  A0 (os0: A0 -> Ord.t)
                  (LE: forall a0, exists a, Ord.le (os0 a0) (os a))
                  (b: bool),
                  wf (if b then base else djoin (fun x => next (rec (os0 x))))).
      { i. destruct b; auto. }
      assert (REFL: forall a0, exists a1, Ord.le (os a0) (os a1)).
      { i. exists a0. reflexivity. }

      assert ((forall o0 (LE: Ord.le o0 (Ord.build os)), dle (rec o0) (dunion base (djoin (fun x => next (rec (os x)))))) /\
              wf (dunion base (djoin (fun x => next (rec (os x))))) /\ dle base (dunion base (djoin (fun x => next (rec (os x)))))).
      { splits.
        - i. destruct o0. erewrite Ord.le_equivalent in LE.
          eapply djoin_supremum; eauto.
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
      destruct (classic (exists o1, Ord.lt o0 o1 /\ Ord.lt o1 (Ord.build os))).
      { des. hexploit (IH o1); eauto. i. des. eapply H2 in H.
        eapply (@dle_transitive (rec o1)); auto.
        { eapply IH in LT. des. auto. }
        eapply RECLE. eapply Ord.lt_le. auto.
      }
      { assert (exists a, Ord.eq o0 (os a)).
        { eapply NNPP. ii. eapply Ord.lt_not_le.
          { eapply LT. }
          eapply Ord.build_supremum. i.
          destruct (trichotomy (os a) o0) as [|[|]]; auto.
          { exfalso. eapply H0. exists a. symmetry. auto. }
          { exfalso. eapply H. esplits; eauto. eapply Ord.build_upperbound. }
        }
        des.
        assert (deq (rec o0) (rec (os a))).
        { inv H0. econs.
          { eapply IH; eauto. eapply Ord.le_lt_lt; eauto. }
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
        { eapply IH; eauto. eapply Ord.le_lt_lt; eauto. eapply H0. }
      }
    Qed.

    Lemma le_rec (o0 o1: Ord.t) (LE: Ord.le o0 o1): dle (rec o0) (rec o1).
    Proof.
      eapply rec_all; auto.
    Qed.

    Lemma eq_rec (o0 o1: Ord.t) (EQ: Ord.eq o0 o1): deq (rec o0) (rec o1).
    Proof.
      split.
      - eapply le_rec. eapply EQ.
      - eapply le_rec. eapply EQ.
    Qed.

    Lemma lt_rec (o0 o1: Ord.t) (LT: Ord.lt o0 o1): dle (next (rec o0)) (rec o1).
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

    Lemma rec_next_le (o0 o1: Ord.t) (LE: Ord.le o0 o1): dle (next (rec o0)) (next (rec o1)).
    Proof.
      eapply le_eq_or_lt in LE. des.
      - eapply lt_rec in LE. eapply (@dle_transitive (rec o1)); eauto.
      - eapply eq_rec in LE. eapply next_eq in LE; eauto. eapply LE.
    Qed.

    Let chain_helper: forall o0 o1, dle (rec o0) (rec o1) \/ dle (rec o1) (rec o0).
    Proof.
      i. destruct (total_le o0 o1).
      { left. apply le_rec. auto. }
      { right. apply le_rec. auto. }
    Qed.

    Let chain_next_helper
      :
        forall o0 o1, dle (next (rec o0)) (next (rec o1)) \/
                      dle (next (rec o1)) (next (rec o0)).
    Proof.
      i. destruct (total o0 o1).
      - left. eapply rec_next_le. auto.
      - right. eapply Ord.lt_le in H. eapply rec_next_le. auto.
    Qed.

    Let wf_helper X (xs: X -> Ord.t)
      :
        forall x, wf (next (rec (xs x))).
    Proof.
      i. auto.
    Qed.

    Let chainu_helper X (xs: X -> Ord.t)
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

    Let wfu_helper X (xs: X -> Ord.t)
      :
        forall (b: bool),
          wf (if b then base else djoin (fun x => next (rec (xs x)))).
    Proof.
      i. destruct b; auto.
    Qed.

    Lemma rec_O: deq (rec Ord.O) base.
    Proof.
      ss. split.
      - eapply djoin_supremum; auto. i. destruct a; auto.
        eapply djoin_supremum; auto. ss.
      - eapply (@djoin_upperbound _ (fun b: bool => if b then base else djoin (fun x => next _)) true); auto.
    Qed.

    Lemma rec_is_O o (ZERO: Ord.is_O o): deq (rec o) base.
    Proof.
      hexploit (@eq_rec Ord.O o).
      { eapply Ord.is_O_unique; auto. eapply Ord.O_is_O. }
      i. inv H. split.
      - eapply (@dle_transitive (rec Ord.O)); auto. eapply rec_O.
      - eapply (@dle_transitive (rec Ord.O)); auto. eapply rec_O.
    Qed.

    Lemma rec_S o: deq (rec (Ord.S o)) (next (rec o)).
    Proof.
      ss. split.
      - eapply djoin_supremum; auto. i. destruct a.
        + eapply (@dle_transitive (rec o)); auto. eapply rec_le_base.
        + eapply djoin_supremum; auto. i. destruct a. ss.
          eapply rec_next_le. reflexivity.
      - eapply (@dle_transitive (djoin (fun x => next (rec (unit_rect (fun _ : unit => Ord.t) o x))))); auto.
        + eapply (djoin_upperbound (fun x : unit => next (rec (unit_rect (fun _ : unit => Ord.t) o x))) tt); auto.
        + eapply (@djoin_upperbound _ (fun b: bool => if b then base else djoin (fun x => next (rec (unit_rect (fun _ : unit => Ord.t) o x)))) false); auto.
    Qed.

    Lemma rec_is_S o s (SUCC: Ord.is_S o s): deq (rec s) (next (rec o)).
    Proof.
      hexploit (@eq_rec (Ord.S o) s).
      { eapply Ord.is_S_unique; eauto. eapply Ord.S_is_S. }
      i. inv H. split.
      - eapply (@dle_transitive (rec (Ord.S o))); auto. eapply rec_S.
      - eapply (@dle_transitive (rec (Ord.S o))); auto. eapply rec_S.
    Qed.

    Lemma rec_build A (os: A -> Ord.t)
          (INHABITED: inhabited A) (OPEN: Ord.open os)
      : deq (rec (Ord.build os)) (djoin (fun a => rec (os a))).
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
      - eapply djoin_supremum; auto. i.
        eapply (@dle_transitive (djoin (fun x : A => next (rec (os x))))); auto.
        eapply (@dle_transitive (next (rec (os a)))); auto.
        + eapply (@djoin_upperbound _ (fun a : A => next (rec (os a))) a); auto.
        + eapply (@djoin_upperbound _ (fun b: bool => if b then base else (djoin (fun a : A => next (rec (os a))))) false); auto.
    Qed.

    Let dunion_wf: forall (d0 d1: D) (CHAIN: dle d0 d1 \/ dle d1 d0) (WF0: wf d0) (WF1: wf d1),
        wf (dunion d0 d1).
    Proof.
      i. eapply djoin_wf; auto.
      { i. destruct a0, a1; auto. des; auto. }
      { i. destruct a; auto. }
    Qed.

    Let dunion_supremum: forall (d0 d1: D) (d: D) (CHAIN: dle d0 d1 \/ dle d1 d0) (WF0: wf d0) (WF1: wf d1) (WFD: wf d) (LE0: dle d0 d) (LE1: dle d1 d), dle (dunion d0 d1) d.
    Proof.
      i. eapply djoin_supremum; auto.
      { i. destruct a0, a1; auto. des; auto. }
      { i. destruct a; auto. }
      { i. destruct a; auto. }
    Qed.

    Let dunion_l: forall (d0 d1: D) (CHAIN: dle d0 d1 \/ dle d1 d0) (WF0: wf d0) (WF1: wf d1),
        dle d0 (dunion d0 d1).
    Proof.
      i. eapply (djoin_upperbound (fun b: bool => if b then d0 else d1) true).
      { i. destruct a0, a1; auto. des; auto. }
      { i. destruct a; auto. }
    Qed.

    Let dunion_r: forall (d0 d1: D) (CHAIN: dle d0 d1 \/ dle d1 d0) (WF0: wf d0) (WF1: wf d1),
        dle d1 (dunion d0 d1).
    Proof.
      i. eapply (djoin_upperbound (fun b: bool => if b then d0 else d1) false).
      { i. destruct a0, a1; auto. des; auto. }
      { i. destruct a; auto. }
    Qed.

    Let BASEJOIN: forall A (os: A -> Ord.t),
        dle base (djoin (fun a : A => rec (os a))) \/
        dle (djoin (fun a : A => rec (os a))) base.
    Proof.
      i. destruct (classic (inhabited A)).
      { inv H. left.
        eapply (@dle_transitive (rec (os X))); auto.
        { eapply rec_le_base. }
        { eapply (djoin_upperbound (fun a => rec (os a)) X); auto. }
      }
      { right. eapply djoin_supremum; auto.
        i. exfalso. eapply H. econs; eauto. }
    Qed.

    Let BASENEXTJOIN: forall A (os: A -> Ord.t),
        dle base (djoin (fun a : A => next (rec (os a)))) \/
        dle (djoin (fun a : A => next (rec (os a)))) base.
    Proof.
      i. destruct (classic (inhabited A)).
      { inv H. left.
        eapply (@dle_transitive (rec (os X))); auto.
        { eapply rec_le_base. }
        eapply (@dle_transitive (next (rec (os X)))); auto.
        { eapply (djoin_upperbound (fun a => next (rec (os a))) X); auto. }
      }
      { right. eapply djoin_supremum; auto.
        i. exfalso. eapply H. econs; eauto. }
    Qed.

    Lemma rec_join A (os: A -> Ord.t)
      : deq (rec (Ord.join os)) (dunion base (djoin (fun a => rec (os a)))).
    Proof.
      split.
      - ss. eapply djoin_supremum; auto.
        i. destruct a; auto. eapply djoin_supremum; auto.
        i. eapply (@dle_transitive (rec (os (projT1 a)))); auto.
        { apply lt_rec. eapply Ord.lt_proj_rev.
          eexists. reflexivity. }
        eapply (@dle_transitive (djoin (fun a0 => rec (os a0)))); auto.
        eapply (djoin_upperbound (fun a0 => rec (os a0)) (projT1 a)); auto.
      - eapply dunion_supremum; auto.
        { eapply rec_le_base. }
        eapply djoin_supremum; auto. i.
        eapply le_rec; auto. eapply Ord.join_upperbound.
    Qed.

    Lemma rec_is_join A (os: A -> Ord.t) o
          (JOIN: Ord.is_join os o)
      : deq (rec o) (dunion base (djoin (fun a => rec (os a)))).
    Proof.
      eapply (@deq_transitive (rec (Ord.join os))); auto.
      { eapply eq_rec; auto.
        eapply Ord.is_join_unique; eauto. eapply Ord.join_is_join. }
      { eapply rec_join. }
    Qed.

    Lemma rec_join_inhabited A (os: A -> Ord.t)
          (INHABITED: inhabited A)
      : deq (rec (Ord.join os)) (djoin (fun a => rec (os a))).
    Proof.
      eapply (@deq_transitive (dunion base (djoin (fun a => rec (os a))))); auto.
      { eapply rec_join. }
      split.
      { inv INHABITED. eapply dunion_supremum; auto.
        eapply (@dle_transitive (rec (os X))); auto.
        { eapply rec_le_base. }
        { eapply (djoin_upperbound (fun a => rec (os a)) X); auto. }
      }
      { eapply dunion_r; auto. }
    Qed.

    Lemma rec_is_join_inhabited A (os: A -> Ord.t) o
          (INHABITED: inhabited A) (JOIN: Ord.is_join os o)
      : deq (rec o) (djoin (fun a => rec (os a))).
    Proof.
      eapply (@deq_transitive (rec (Ord.join os))); auto.
      { eapply eq_rec; auto.
        eapply Ord.is_join_unique; eauto. eapply Ord.join_is_join. }
      { eapply rec_join_inhabited. auto. }
    Qed.

    Lemma rec_union o0 o1
      : deq (rec (Ord.union o0 o1)) (dunion (rec o0) (rec o1)).
    Proof.
      assert (INHABITED: inhabited bool).
      { constructor. exact true. }
      split.
      { eapply (@dle_transitive (djoin (fun a : bool => rec ((fun b : bool => if b then o0 else o1) a)))); auto.
        { eapply rec_join_inhabited; auto. }
        { eapply djoin_supremum; auto. i. destruct a; auto. }
      }
      { eapply (@dle_transitive (djoin (fun a : bool => rec ((fun b : bool => if b then o0 else o1) a)))); auto.
        { eapply djoin_supremum; auto.
          { i. destruct a0, a1; auto. }
          { i. destruct a; auto. }
          { i. destruct a; auto.
            { eapply (@djoin_upperbound _ (fun b: bool => rec (if b then o0 else o1)) true); auto. }
            { eapply (@djoin_upperbound _ (fun b: bool => rec (if b then o0 else o1)) false); auto. }
          }
        }
        { eapply rec_join_inhabited; auto. }
      }
    Qed.

    Lemma rec_unique (f: Ord.t -> D)
          (ZERO: forall o (ZERO: Ord.is_O o), deq (f o) base)
          (SUCC: forall o s (SUCC: Ord.is_S o s), deq (f s) (next (f o)))
          (LIMIT: forall A (os: A -> Ord.t) o (JOIN: Ord.is_join os o)
                         (INHABITED: inhabited A) (OPEN: Ord.open os),
              deq (f o) (djoin (fun a => f (os a))))
          (WF: forall o, wf (f o))
      :
        forall o, deq (f o) (rec o).
    Proof.
      eapply ind.
      { i. eapply (@deq_transitive base); auto.
        eapply deq_symmetric. eapply rec_is_O; auto. }
      { i. eapply (@deq_transitive (next (f o))); auto.
        eapply (@deq_transitive (next (rec o))); auto.
        eapply deq_symmetric. eapply rec_is_S; auto. }
      { i. assert (CHAIN: forall a0 a1, dle (f (os a0)) (f (os a1)) \/ dle (f (os a1)) (f (os a0))).
        { i. destruct (chain_helper (os a0) (os a1)).
          { left. eapply (@dle_transitive (rec (os a0))); auto.
            { eapply IH. }
            eapply (@dle_transitive (rec (os a1))); auto.
            { eapply IH. }
          }
          { right. eapply (@dle_transitive (rec (os a1))); auto.
            { eapply IH. }
            eapply (@dle_transitive (rec (os a0))); auto.
            { eapply IH. }
          }
        }
        eapply (@deq_transitive (djoin (fun a => f (os a)))); auto.
        eapply (@deq_transitive (djoin (fun a => rec (os a)))); auto.
        { split.
          { eapply djoin_supremum; auto. i.
            eapply (@dle_transitive (rec (os a))); auto.
            { eapply IH. }
            { eapply (djoin_upperbound (fun a0 => rec (os a0)) a); auto. }
          }
          { eapply djoin_supremum; auto. i.
            eapply (@dle_transitive (f (os a))); auto.
            { eapply IH. }
            { eapply (djoin_upperbound (fun a0 => f (os a0)) a); auto. }
          }
        }
        { eapply deq_symmetric. eapply rec_is_join_inhabited; auto. }
      }
    Qed.

    Lemma rec_unique2 (f: Ord.t -> D)
          (RED: forall A (os: A -> Ord.t),
              deq (f (Ord.build os)) (dunion base (djoin (fun a => next (f (os a))))))
          (WF: forall o, wf (f o))
      :
        forall o, deq (f o) (rec o).
    Proof.
      induction o.
      assert (NEXTLE: forall a0 a1 (LE: Ord.le (os a0) (os a1)),
                 dle (next (f (os a0))) (next (f (os a1)))).
      { i. eapply (@dle_transitive (next (rec (os a0)))); auto.
        { eapply next_eq; auto. }
        eapply (@dle_transitive (next (rec (os a1)))); auto.
        { eapply rec_next_le. auto. }
        { eapply next_eq; auto. }
      }
      assert (NEXTCHAIN:  forall a0 a1 : A,
                 dle (next (f (os a0))) (next (f (os a1))) \/
                 dle (next (f (os a1))) (next (f (os a0)))).
      { i. destruct (total_le (os a0) (os a1)); auto. }
      assert (BASE: dle base (djoin (fun a : A => next (f (os a)))) \/
                    dle (djoin (fun a : A => next (f (os a)))) base).
      { i. destruct (classic (inhabited A)).
        { inv H0. left.
          eapply (@dle_transitive (f (os X))); auto.
          { eapply (@dle_transitive (rec (os X))); auto.
            { eapply rec_le_base. }
            { eapply H. }
          }
          { eapply (@dle_transitive (next (f (os X)))); auto.
            eapply (djoin_upperbound (fun a => next (f (os a))) X); auto.
          }
        }
        { right. eapply djoin_supremum; auto.
          i. exfalso. eapply H0. econs; eauto. }
      }
      assert (WFU0: wf (dunion base (djoin (fun a : A => next (f (os a)))))).
      { eapply dunion_wf; auto. }
      assert (WFU1: wf (dunion base (djoin (fun a : A => next (rec (os a)))))).
      { eapply djoin_wf; auto. }
      split.
      - apply (@dle_transitive (dunion base (djoin (fun a => next (f (os a)))))); auto; auto.
        + apply RED.
        + ss. apply djoin_supremum; auto.
          { i. destruct a0, a1; auto. destruct BASE; auto. }
          { i. destruct a; auto. }
          i. destruct a; auto.
          { eapply (@djoin_upperbound _ (fun b: bool => if b then base else (djoin (fun a : A => next (rec (os a))))) true).
            { i. destruct a0, a1; auto. destruct (BASENEXTJOIN os); auto. }
            { i. destruct a; auto. }
          }
          apply (@dle_transitive (djoin (fun a => next (rec (os a))))); auto.
          { apply djoin_supremum; auto. i.
            apply (@dle_transitive (next (rec (os a)))); auto.
            { eapply next_eq; auto. }
            { apply (djoin_upperbound (fun a0 => next (rec (os a0))) a); auto. }
          }
          { eapply (@djoin_upperbound _ (fun b: bool => if b then base else (djoin (fun a : A => next (rec (os a))))) false).
            { i. destruct a0, a1; auto. destruct (BASENEXTJOIN os); auto. }
            { i. destruct a; auto. }
          }
      - apply (@dle_transitive (dunion base (djoin (fun a => next (f (os a)))))); auto; auto.
        + ss. apply djoin_supremum; auto.
          i. destruct a; auto.
          apply (@dle_transitive (djoin (fun a => next (f (os a))))); auto.
          { apply djoin_supremum; auto. i.
            apply (@dle_transitive (next (f (os a)))); auto.
            { eapply next_eq; auto. }
            { apply (djoin_upperbound (fun a0 => next (f (os a0))) a); auto. }
          }
        + apply RED.
    Qed.


    Let _rec_wf: forall o, wf (rec o).
    Proof.
      eapply rec_wf; eauto.
    Qed.

    Let _rec_next_wf: forall o, wf (next (rec o)).
    Proof.
      i. eapply next_wf. eapply rec_wf; eauto.
    Qed.

    Inductive strictly_increasing: D -> D -> Prop :=
    | strictly_increasing_intro
        o0 o1
        (LT: Ord.lt o0 o1)
        (INCR: ~ dle (rec o1) (rec o0))
      :
        strictly_increasing (rec o0) (rec o1)
    .

    Lemma strictly_increasing_well_founded: well_founded strictly_increasing.
    Proof.
      assert (forall o, Acc strictly_increasing (rec o)).
      { eapply (well_founded_induction Ord.lt_well_founded).
        i. econs. i. inv H0. eapply H.
        destruct (total x o0); auto. exfalso.
        eapply INCR. rewrite H3. eapply le_rec; eauto.
      }
      ii. econs. i. inv H0. eapply H.
    Qed.

    Definition not_fixed (o1: Ord.t): Prop :=
      forall o0 (LT: Ord.lt o0 o1), ~ dle (rec o1) (rec o0).

    Lemma fixed_point_after o0 (FIX: dle (next (rec o0)) (rec o0)):
      forall o1 (LE: Ord.le o0 o1),
        dle (rec o1) (rec o0).
    Proof.
      eapply (@ind (fun o1 => forall (LE: Ord.le o0 o1),
                        dle (rec o1) (rec o0))).
      { i. eapply le_rec; eauto. }
      { i. eapply le_eq_or_lt in LE. des.
        2: { eapply le_rec; eauto. eapply LE. }
        hexploit rec_is_S; auto.
        { eauto. } i.
        assert (LE0: Ord.le o0 o).
        { destruct (total o0 o); auto. exfalso. eapply SUCC in H0.
          eapply (@Ord.lt_not_le o0 s); eauto. }
        hexploit IH; auto. i.
        assert (deq (next (rec o0)) (rec o0)).
        { split; auto. } clear FIX.
        assert (deq (rec o) (rec o0)).
        { split; auto. eapply le_rec; eauto. }
        eapply (@dle_transitive (next (rec o))); auto.
        { eapply H. }
        eapply (@dle_transitive (next (rec o0))); auto.
        2: { eapply H1. }
        eapply next_eq; auto.
      }
      { i. hexploit rec_is_join_inhabited; try eassumption. i.
        assert (forall a0 a1 : A,
                   dle (rec (os a0)) (rec (os a1)) \/ dle (rec (os a1)) (rec (os a0))).
        { i. destruct (total_le (os a0) (os a1)).
          { left. eapply le_rec; eauto. }
          { right. eapply le_rec; eauto. }
        }
        assert (wf (djoin (fun a : A => rec (os a)))); auto.
        eapply (@dle_transitive (djoin (fun a : A => rec (os a)))); auto.
        { eapply H. }
        eapply djoin_supremum; auto. i.
        destruct (total (os a) o0).
        { eapply le_rec; eauto. }
        hexploit (IH a); eauto.
        eapply Ord.lt_le. auto.
      }
    Qed.

    Let end_le_end o0 o1 (LE: Ord.le o0 o1) (NEND: not_fixed o1): not_fixed o0.
    Proof.
      ii. eapply NEND.
      { eapply (@Ord.lt_le_lt o0); eauto. }
      dup LT. eapply Ord.S_supremum in LT0.
      hexploit rec_S; auto. i. inv H0.
      hexploit (@fixed_point_after o2).
      { eapply (@dle_transitive (rec (Ord.S o2))); auto.
        { eapply H2. }
        eapply (@dle_transitive (rec o0)); auto.
        eapply le_rec; eauto. }
      { instantiate (1:=o1). transitivity o0; auto.
        eapply Ord.lt_le. apply LT. }
      auto.
    Qed.

    Let least_lt_incr_acc o1 (INCR: not_fixed o1):
      Ord.le o1 (Ord.from_wf strictly_increasing_well_founded (rec o1)).
    Proof.
      revert o1 INCR.
      eapply (well_founded_induction Ord.lt_well_founded
                                     (fun o1 => forall (INCR: not_fixed o1),
                                          Ord.le o1 (Ord.from_wf strictly_increasing_well_founded (rec o1)))).
      i. destruct (total x (Ord.from_wf strictly_increasing_well_founded (rec x))); auto.
      destruct x. eapply Ord.build_supremum. i.
      hexploit (Ord.build_upperbound os a). i.
      hexploit (H (os a)); eauto.
      { eapply end_le_end; eauto. eapply Ord.lt_le; auto. }
      i. eapply Ord.le_lt_lt.
      { eapply H2. }
      eapply Ord.from_wf_lt. econs; eauto.
    Qed.

    Let hartogs_fixed: ~ not_fixed (Ord.hartogs D).
    Proof.
      ii. eapply least_lt_incr_acc in H; eauto.
      eapply Ord.lt_not_le.
      2: { eapply H. }
      eapply Ord.le_lt_lt.
      { eapply Ord.lt_le. eapply Ord.from_wf_set_upperbound. }
      eapply (Ord.build_upperbound (fun RWF => Ord.from_wf_set (proj2_sig RWF)) (exist _ _ strictly_increasing_well_founded)).
    Qed.

    Lemma _fixpoint_theorem:
      dle (next (rec (Ord.hartogs D))) (rec (Ord.hartogs D)).
    Proof.
      eapply NNPP. ii. eapply hartogs_fixed. eapply end_le_end.
      { eapply Ord.lt_le. eapply Ord.S_lt. }
      ii. eapply H.
      hexploit rec_S; auto.
      i. des. eapply (@dle_transitive (rec (Ord.S (Ord.hartogs D)))); auto.
      { eapply H1. }
      eapply (@dle_transitive (rec o0)); auto.
      eapply le_rec; eauto.
      destruct (total o0 (Ord.hartogs D)); auto.
      eapply Ord.S_supremum in H2.
      exfalso. eapply Ord.lt_not_le.
      { eapply LT. }
      { eapply H2. }
    Qed.
  End REC.
End ClassicOrd.
