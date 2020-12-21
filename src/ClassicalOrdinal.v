Require Import sflib.

Require Import Coq.Classes.RelationClasses Coq.Relations.Relation_Operators Coq.Classes.Morphisms. (* TODO: Use Morphisms *)
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.
Require Import Program.

Require Import Ordinal.

Set Implicit Arguments.
Set Primitive Projections.

Theorem cantor_theorem A (f: A -> (A -> Prop)):
  exists P, forall a, f a <> P.
Proof.
  exists (fun a => ~ (f a) a). ii.
  eapply equal_f with (x:=a) in H.
  cut (~ f a a).
  { ii. eapply H0. rewrite H. auto. }
  { ii. dup H0. rewrite H in H0. apply H0. apply H1. }
Qed.

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

Module ClassicalOrdinal.
  Lemma total o0 o1: Ordinal.le o0 o1 \/ Ordinal.lt o1 o0.
  Proof.
    cut ((Ordinal.le o0 o1 \/ Ordinal.lt o1 o0) /\ (Ordinal.le o1 o0 \/ Ordinal.lt o0 o1)).
    { i. des; auto. }
    ginduction o0. i. split.
    { destruct (classic (exists (a: A), Ordinal.le o1 (os a))).
      { des. right. econs; eauto. }
      assert (forall a, Ordinal.lt (os a) o1).
      { i. eapply not_ex_all_not in H0. instantiate (1:=a) in H0.
        destruct (H a o1). clear H1. des; ss. } clear H0.
      left. destruct o1. econs. i.
      specialize (H1 a0). eapply Ordinal.lt_inv in H1. eauto.
    }
    { destruct o1.
      destruct (classic (forall (a0: A0), exists (a: A), Ordinal.le (os0 a0) (os a))).
      { left. econs; eauto. }
      eapply not_all_ex_not in H0. des.
      assert (forall a, Ordinal.lt (os a) (os0 n)).
      { i. eapply not_ex_all_not in H0. instantiate (1:=a) in H0.
        destruct (H a (os0 n)). clear H1. des; ss. } clear H0.
      right. econs. instantiate (1:=n).
      destruct (os0 n). econs. i. specialize (H1 a0).
      eapply Ordinal.lt_inv in H1. eauto.
    }
  Qed.

  Lemma total_le o0 o1: Ordinal.le o0 o1 \/ Ordinal.le o1 o0.
  Proof.
    destruct (total o0 o1); auto. right. eapply Ordinal.lt_le. auto.
  Qed.

  Lemma le_eq_or_lt o0 o1:
    Ordinal.le o0 o1 <-> (Ordinal.lt o0 o1 \/ Ordinal.eq o0 o1).
  Proof.
    split; i.
    - destruct (total o1 o0).
      + right. split; auto.
      + left. auto.
    - destruct H.
      + eapply Ordinal.lt_le; auto.
      + destruct H. auto.
  Qed.

  Lemma trichotomy o0 o1: Ordinal.lt o0 o1 \/ Ordinal.eq o0 o1 \/ Ordinal.lt o1 o0.
  Proof.
    destruct (total o0 o1); auto. eapply le_eq_or_lt in H. des; auto.
  Qed.

  Lemma from_acc_complete A (R: A -> A -> Prop) a1 (ACC1: Acc R a1)
        o (LT: Ordinal.lt o (Ordinal.from_acc ACC1))
    :
      exists a0 (ACC0: Acc R a0), Ordinal.eq o (Ordinal.from_acc ACC0).
  Proof.
    dup ACC1. revert o LT. induction ACC0. i. destruct ACC1.
    ss. eapply Ordinal.lt_inv in LT. des. destruct a0 as [a0 p0]. ss.
    eapply le_eq_or_lt in LT. des; eauto.
  Qed.

  Lemma from_wf_complete A (R: A -> A -> Prop) (WF: well_founded R) a1
        o (LT: Ordinal.lt o (Ordinal.from_wf WF a1))
    :
      exists a0, Ordinal.eq o (Ordinal.from_wf WF a0).
  Proof.
    eapply from_acc_complete in LT. des. exists a0.
    unfold Ordinal.from_wf. etransitivity.
    { eapply LT. }
    { eapply Ordinal.same_acc_eq. }
  Qed.

  Lemma from_wf_set_complete A (R: A -> A -> Prop) (WF: well_founded R)
        o (LT: Ordinal.lt o (Ordinal.from_wf_set WF))
    :
      exists a, Ordinal.eq o (Ordinal.from_wf WF a).
  Proof.
    eapply Ordinal.lt_inv in LT. des. eapply le_eq_or_lt in LT. des; eauto.
    eapply from_wf_complete in LT. eauto.
  Qed.

  Lemma from_wf_set_lt A (R0 R1: A -> A -> Prop) (INCL: forall a0 a1 (LE: R0 a0 a1), R1 a0 a1)
        (WF0: well_founded R0) (WF1: well_founded R1)
        (TOP: exists a2 x, R1 x a2 /\ forall a0 a1 (LT: R0 a0 a1), R1 a1 a2)
    :
      Ordinal.lt (Ordinal.from_wf_set WF0) (Ordinal.from_wf_set WF1).
  Proof.
    des. eapply Ordinal.lt_intro with (a:=a2).
    unfold Ordinal.from_wf. destruct (WF1 a2). ss. econs. intros a1.
    destruct (classic (exists a0, R0 a0 a1)).
    - des. exists (exist _ a1 (TOP0 _ _ H)). ss.
      unfold Ordinal.from_wf. eapply Ordinal.from_acc_mon; auto.
    - exists (exist _ x TOP). ss.
      unfold Ordinal.from_wf. destruct (WF0 a1), (a x TOP). econs. i.
      exfalso. destruct a4. eapply H; eauto.
  Qed.

  Definition is_meet (P: Ordinal.t -> Prop) (o0: Ordinal.t): Prop :=
    P o0 /\ forall o1 (IN: P o1), Ordinal.le o0 o1.

  Lemma meet_exists (P: Ordinal.t -> Prop) (INHABITED: exists o, P o):
    exists o0, is_meet P o0.
  Proof.
    apply NNPP. ii. des.
    hexploit (well_founded_induction Ordinal.lt_well_founded (fun o => ~ P o)); eauto.
    ii. eapply not_ex_all_not in H. instantiate (1:=x) in H.
    apply not_and_or in H. des; ss. eapply H. i.
    destruct (total x o1); auto. eapply H0 in H2. ss.
  Qed.

  Lemma limit_or_S o:
    (exists o0, Ordinal.is_S o0 o) \/
    (exists A (os: A -> Ordinal.t), Ordinal.is_join os o /\ Ordinal.open os).
  Proof.
    destruct o. destruct (classic (forall a0, exists a1, Ordinal.lt (os a0) (os a1))).
    - right. exists A, os. split; auto. split.
      + i. eapply Ordinal.lt_le. eapply Ordinal.build_upperbound.
      + i. eapply Ordinal.build_spec. i. specialize (H a). des.
        eapply Ordinal.lt_le_lt; eauto.
    - left. eapply not_all_ex_not in H. des.
      exists (os n). split.
      + eapply Ordinal.build_upperbound.
      + i. eapply Ordinal.build_spec. i. destruct (total (os a) (os n)); auto.
        * eapply Ordinal.le_lt_lt; eauto.
        * exfalso. eapply H; eauto.
  Qed.

  Lemma limit_S_disjoint o o0 A (os: A -> Ordinal.t)
        (SUCC: Ordinal.is_S o0 o)
        (JOIN: Ordinal.is_join os o)
        (OPEN: Ordinal.open os)
    :
      False.
  Proof.
    hexploit (JOIN.(Ordinal.is_join_supremum)).
    { instantiate (1:=o0).
      i. destruct (total (os a) o0); auto.
      eapply SUCC.(Ordinal.is_S_spec) in H.
      specialize (OPEN a). des.
      exfalso. eapply (@Ordinal.lt_not_le (os a) o); auto.
      eapply Ordinal.lt_le_lt; eauto. eapply JOIN.(Ordinal.is_join_upperbound). }
    i. eapply (@Ordinal.lt_not_le o0 o); auto. eapply SUCC.(Ordinal.is_S_lt).
  Qed.

  Lemma build_is_join A (os: A -> Ordinal.t) (OPEN: Ordinal.open os): Ordinal.is_join os (Ordinal.build os).
  Proof.
    econs.
    - i. eapply Ordinal.lt_le. eapply Ordinal.build_upperbound.
    - i. eapply Ordinal.build_spec. i. specialize (OPEN a). des.
      eapply Ordinal.lt_le_lt; eauto.
  Qed.

  Lemma ind
        (P: Ordinal.t -> Prop)
        (ZERO: forall o (ZERO: Ordinal.is_O o)
                      (HELPER: forall o' (LT: Ordinal.lt o' o), P o'), P o)
        (SUCC: forall o s (SUCC: Ordinal.is_S o s) (IH: P o)
                      (HELPER: forall o' (LT: Ordinal.lt o' s), P o'), P s)
        (LIMIT: forall A (os: A -> Ordinal.t) o (JOIN: Ordinal.is_join os o)
                       (INHABITED: inhabited A) (OPEN: Ordinal.open os)
                       (IH: forall a, P (os a))
                       (HELPER: forall o' (LT: Ordinal.lt o' o), P o'), P o)
    :
      forall o, P o.
  Proof.
    eapply well_founded_induction.
    { eapply Ordinal.lt_well_founded. }
    i. destruct (limit_or_S x).
    - des. eapply SUCC; eauto. eapply H. eapply H0.
    - des. destruct (classic (inhabited A)).
      + eapply LIMIT; eauto. i. eapply H.
        specialize (H1 a). des. eapply Ordinal.lt_le_lt; eauto. eapply H0.
      + eapply ZERO; eauto. ii. eapply H0.
        i. exfalso. eapply H2. eauto.
  Qed.

  Definition next_cardinal (A: Type) := @Ordinal.build (@sig (A -> A -> Prop) (@well_founded _)) (fun RWF => Ordinal.from_wf_set (proj2_sig RWF)).

  Definition is_hartogs A (h: Ordinal.t): Prop :=
    is_meet (fun o => forall (R: A -> A -> Prop) (WF: well_founded R),
                 ~ Ordinal.le o (Ordinal.from_wf_set WF)) h.

  Lemma hartogs_exists A:
    exists h, is_hartogs A h.
  Proof.
    eapply meet_exists.
    exists (next_cardinal A).
    ii. eapply Ordinal.lt_StrictOrder. eapply Ordinal.lt_le_lt; [|eauto].
    eapply (@Ordinal.build_upperbound _ (fun rwf => Ordinal.from_wf_set (proj2_sig rwf)) (@exist _ _ R WF)).
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

    Let rec := Ordinal.rec base next djoin.

    Let rec_all (o1: Ordinal.t):
      (forall o0 (LE: Ordinal.le o0 o1), dle (rec o0) (rec o1)) /\
      (forall o0 (LT: Ordinal.lt o0 o1), dle (next (rec o0)) (rec o1)) /\
      (wf (rec o1)) /\
      (dle base (rec o1))
    .
    Proof.
      revert o1.
      eapply (well_founded_induction Ordinal.lt_well_founded); auto.
      intros o1 IH. destruct o1. ss.

      assert (IHS0:
                forall
                  A0 (os0: A0 -> Ordinal.t)
                  (LE: forall a0, exists a, Ordinal.le (os0 a0) (os a))
                  a0,
                  (forall o0 (LE: Ordinal.le o0 (os0 a0)), dle (rec o0) (rec (os0 a0))) /\
                  (forall o0 (LT: Ordinal.lt o0 (os0 a0)), dle (next (rec o0)) (rec (os0 a0))) /\
                  wf (rec (os0 a0)) /\ dle base (rec (os0 a0))).
      { i. eapply IH. hexploit (LE a0); eauto. i. des. econs; eauto. }
      assert (CHAIN0:
                forall
                  A0 (os0: A0 -> Ordinal.t)
                  (LE: forall a0, exists a, Ordinal.le (os0 a0) (os a))
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
                  A0 (os0: A0 -> Ordinal.t)
                  (LE: forall a0, exists a, Ordinal.le (os0 a0) (os a))
                  a,
                  wf (next (rec (os0 a)))).
      { i. eapply next_wf. eapply IHS0; eauto. }
      assert (CHAINU0:
                forall
                  A0 (os0: A0 -> Ordinal.t)
                  (LE: forall a0, exists a, Ordinal.le (os0 a0) (os a))
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
                  A0 (os0: A0 -> Ordinal.t)
                  (LE: forall a0, exists a, Ordinal.le (os0 a0) (os a))
                  (b: bool),
                  wf (if b then base else djoin (fun x => next (rec (os0 x))))).
      { i. destruct b; auto. }
      assert (REFL: forall a0, exists a1, Ordinal.le (os a0) (os a1)).
      { i. exists a0. reflexivity. }

      assert ((forall o0 (LE: Ordinal.le o0 (Ordinal.build os)), dle (rec o0) (dunion base (djoin (fun x => next (rec (os x)))))) /\
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
      destruct (classic (exists o1, Ordinal.lt o0 o1 /\ Ordinal.lt o1 (Ordinal.build os))).
      { des. hexploit (IH o1); eauto. i. des. eapply H2 in H.
        eapply (@dle_transitive (rec o1)); auto.
        { eapply IH in LT. des. auto. }
        eapply RECLE. eapply Ordinal.lt_le. auto.
      }
      { assert (exists a, Ordinal.eq o0 (os a)).
        { eapply NNPP. ii. eapply Ordinal.lt_not_le.
          { eapply LT. }
          eapply Ordinal.build_spec. i.
          destruct (trichotomy (os a) o0) as [|[|]]; auto.
          { exfalso. eapply H0. exists a. symmetry. auto. }
          { exfalso. eapply H. esplits; eauto. eapply Ordinal.build_upperbound. }
        }
        des.
        assert (deq (rec o0) (rec (os a))).
        { inv H0. econs.
          { eapply IH; eauto. eapply Ordinal.le_lt_lt; eauto. }
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
        { eapply IH; eauto. eapply Ordinal.le_lt_lt; eauto. eapply H0. }
      }
    Qed.

    Lemma rec_le (o0 o1: Ordinal.t) (LE: Ordinal.le o0 o1): dle (rec o0) (rec o1).
    Proof.
      eapply rec_all; auto.
    Qed.

    Lemma rec_eq (o0 o1: Ordinal.t) (EQ: Ordinal.eq o0 o1): deq (rec o0) (rec o1).
    Proof.
      split.
      - eapply rec_le. eapply EQ.
      - eapply rec_le. eapply EQ.
    Qed.

    Lemma rec_lt (o0 o1: Ordinal.t) (LT: Ordinal.lt o0 o1): dle (next (rec o0)) (rec o1).
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

    Lemma rec_next_le (o0 o1: Ordinal.t) (LE: Ordinal.le o0 o1): dle (next (rec o0)) (next (rec o1)).
    Proof.
      eapply le_eq_or_lt in LE. des.
      - eapply rec_lt in LE. eapply (@dle_transitive (rec o1)); eauto.
      - eapply rec_eq in LE. eapply next_eq in LE; eauto. eapply LE.
    Qed.

    Let chain_helper X (xs: X -> Ordinal.t)
      :
        forall x0 x1, dle (next (rec (xs x0))) (next (rec (xs x1))) \/
                      dle (next (rec (xs x1))) (next (rec (xs x0))).
    Proof.
      i. destruct (total (xs x0) (xs x1)).
      - left. eapply rec_next_le. auto.
      - right. eapply Ordinal.lt_le in H. eapply rec_next_le. auto.
    Qed.

    Let wf_helper X (xs: X -> Ordinal.t)
      :
        forall x, wf (next (rec (xs x))).
    Proof.
      i. auto.
    Qed.

    Let chainu_helper X (xs: X -> Ordinal.t)
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

    Let wfu_helper X (xs: X -> Ordinal.t)
      :
        forall (b: bool),
          wf (if b then base else djoin (fun x => next (rec (xs x)))).
    Proof.
      i. destruct b; auto.
    Qed.

    Lemma rec_O: deq (rec Ordinal.O) base.
    Proof.
      ss. split.
      - eapply djoin_supremum; auto. i. destruct a; auto.
        eapply djoin_supremum; auto. ss.
      - eapply (@djoin_upperbound _ (fun b: bool => if b then base else djoin (fun x => next (rec !))) true); auto.
    Qed.

    Lemma rec_is_O o (ZERO: Ordinal.is_O o): deq (rec o) base.
    Proof.
      hexploit (@rec_eq Ordinal.O o).
      { eapply Ordinal.is_O_eq; auto. eapply Ordinal.O_is_O. }
      i. inv H. split.
      - eapply (@dle_transitive (rec Ordinal.O)); auto. eapply rec_O.
      - eapply (@dle_transitive (rec Ordinal.O)); auto. eapply rec_O.
    Qed.

    Lemma rec_S o: deq (rec (Ordinal.S o)) (next (rec o)).
    Proof.
      ss. split.
      - eapply djoin_supremum; auto. i. destruct a.
        + eapply (@dle_transitive (rec o)); auto. eapply rec_le_base.
        + eapply djoin_supremum; auto. i. destruct a. ss.
          eapply rec_next_le. reflexivity.
      - eapply (@dle_transitive (djoin (fun x => next (rec (unit_rect (fun _ : () => Ordinal.t) o x))))); auto.
        + eapply (djoin_upperbound (fun x : () => next (rec (unit_rect (fun _ : () => Ordinal.t) o x))) tt); auto.
        + eapply (@djoin_upperbound _ (fun b: bool => if b then base else djoin (fun x => next (rec (unit_rect (fun _ : () => Ordinal.t) o x)))) false); auto.
    Qed.

    Lemma rec_is_S o s (SUCC: Ordinal.is_S o s): deq (rec s) (next (rec o)).
    Proof.
      hexploit (@rec_eq (Ordinal.S o) s).
      { eapply Ordinal.is_S_eq; eauto. eapply Ordinal.S_is_S. }
      i. inv H. split.
      - eapply (@dle_transitive (rec (Ordinal.S o))); auto. eapply rec_S.
      - eapply (@dle_transitive (rec (Ordinal.S o))); auto. eapply rec_S.
    Qed.

    Lemma rec_build A (os: A -> Ordinal.t)
          (INHABITED: inhabited A) (OPEN: Ordinal.open os)
      : deq (rec (Ordinal.build os)) (djoin (fun a => rec (os a))).
    Proof.
      assert (CHAINJOIN: forall a0 a1 : A, dle (rec (os a0)) (rec (os a1)) \/ dle (rec (os a1)) (rec (os a0))).
      { i. destruct (total (os a0) (os a1)).
        - left. eapply rec_le; auto.
        - right. eapply Ordinal.lt_le in H. eapply rec_le; auto.
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
      - eapply djoin_supremum; auto. i.
        eapply (@dle_transitive (djoin (fun x : A => next (rec (os x))))); auto.
        eapply (@dle_transitive (next (rec (os a)))); auto.
        + eapply (@djoin_upperbound _ (fun a : A => next (rec (os a))) a); auto.
        + eapply (@djoin_upperbound _ (fun b: bool => if b then base else (djoin (fun a : A => next (rec (os a))))) false); auto.
    Qed.
    Lemma rec_is_join A (os: A -> Ordinal.t) o
          (INHABITED: inhabited A) (OPEN: Ordinal.open os) (JOIN: Ordinal.is_join os o)
      : deq (rec o) (djoin (fun a => rec (os a))).
    Proof.
      assert (CHAINJOIN: forall a0 a1 : A, dle (rec (os a0)) (rec (os a1)) \/ dle (rec (os a1)) (rec (os a0))).
      { i. destruct (total (os a0) (os a1)).
        - left. eapply rec_le; auto.
        - right. eapply Ordinal.lt_le in H. eapply rec_le; auto.
      }
      hexploit (@rec_eq (Ordinal.build os) o).
      { eapply Ordinal.is_join_eq; eauto. eapply build_is_join; auto. }
      i. inv H. split.
      - eapply (@dle_transitive (rec (Ordinal.build os))); auto.
        eapply rec_build; auto.
      - eapply (@dle_transitive (rec (Ordinal.build os))); auto.
        eapply rec_build; auto.
    Qed.

    Lemma rec_join A (os: A -> Ordinal.t)
          (INHABITED: inhabited A) (OPEN: Ordinal.open os)
      : deq (rec (Ordinal.join os)) (djoin (fun a => rec (os a))).
    Proof.
      eapply rec_is_join; auto. eapply Ordinal.join_is_join.
    Qed.

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
        (LT: Ordinal.lt o0 o1)
        (INCR: ~ dle (rec o1) (rec o0))
      :
        strictly_increasing (rec o0) (rec o1)
    .

    Lemma strictly_increasing_well_founded: well_founded strictly_increasing.
    Proof.
      assert (forall o, Acc strictly_increasing (rec o)).
      { eapply (well_founded_induction Ordinal.lt_well_founded).
        i. econs. i. inv H0. eapply H.
        destruct (total x o0); auto. exfalso.
        eapply INCR. rewrite H3. eapply rec_le; eauto.
      }
      ii. econs. i. inv H0. eapply H.
    Qed.

    Definition not_fixed (o1: Ordinal.t): Prop :=
      forall o0 (LT: Ordinal.lt o0 o1), ~ dle (rec o1) (rec o0).

    Lemma fixed_point_after o0 (FIX: dle (next (rec o0)) (rec o0)):
      forall o1 (LE: Ordinal.le o0 o1),
        dle (rec o1) (rec o0).
    Proof.
      eapply (@ind (fun o1 => forall (LE: Ordinal.le o0 o1),
                        dle (rec o1) (rec o0))).
      { i. eapply rec_le; eauto. }
      { i. eapply le_eq_or_lt in LE. des.
        2: { eapply rec_le; eauto. eapply LE. }
        hexploit rec_is_S; auto.
        { eauto. } i.
        assert (LE0: Ordinal.le o0 o).
        { destruct (total o0 o); auto. exfalso. eapply SUCC in H0.
          eapply (@Ordinal.lt_not_le o0 s); eauto. }
        hexploit IH; auto. i.
        assert (deq (next (rec o0)) (rec o0)).
        { split; auto. } clear FIX.
        assert (deq (rec o) (rec o0)).
        { split; auto. eapply rec_le; eauto. }
        eapply (@dle_transitive (next (rec o))); auto.
        { eapply H. }
        eapply (@dle_transitive (next (rec o0))); auto.
        2: { eapply H1. }
        eapply next_eq; auto.
      }
      { i. hexploit rec_is_join; try eassumption. i.
        assert (forall a0 a1 : A,
                   dle (rec (os a0)) (rec (os a1)) \/ dle (rec (os a1)) (rec (os a0))).
        { i. destruct (total_le (os a0) (os a1)).
          { left. eapply rec_le; eauto. }
          { right. eapply rec_le; eauto. }
        }
        assert (wf (djoin (fun a : A => rec (os a)))); auto.
        eapply (@dle_transitive (djoin (fun a : A => rec (os a)))); auto.
        { eapply H. }
        eapply djoin_supremum; auto. i.
        destruct (total (os a) o0).
        { eapply rec_le; eauto. }
        hexploit (IH a); eauto.
        eapply Ordinal.lt_le. auto.
      }
    Qed.

    Let end_le_end o0 o1 (LE: Ordinal.le o0 o1) (NEND: not_fixed o1): not_fixed o0.
    Proof.
      ii. eapply NEND.
      { eapply (@Ordinal.lt_le_lt o0); eauto. }
      dup LT. eapply Ordinal.S_spec in LT0.
      hexploit rec_S; auto. i. inv H0.
      hexploit (@fixed_point_after o2).
      { eapply (@dle_transitive (rec (Ordinal.S o2))); auto.
        { eapply H2. }
        eapply (@dle_transitive (rec o0)); auto.
        eapply rec_le; eauto. }
      { instantiate (1:=o1). transitivity o0; auto.
        eapply Ordinal.lt_le. apply LT. }
      auto.
    Qed.

    Let least_lt_incr_acc o1 (INCR: not_fixed o1):
      Ordinal.le o1 (Ordinal.from_wf strictly_increasing_well_founded (rec o1)).
    Proof.
      revert o1 INCR.
      eapply (well_founded_induction Ordinal.lt_well_founded
                                     (fun o1 => forall (INCR: not_fixed o1),
                                          Ordinal.le o1 (Ordinal.from_wf strictly_increasing_well_founded (rec o1)))).
      i. destruct (total x (Ordinal.from_wf strictly_increasing_well_founded (rec x))); auto.
      destruct x. eapply Ordinal.build_spec. i.
      hexploit (Ordinal.build_upperbound os a). i.
      hexploit (H (os a)); eauto.
      { eapply end_le_end; eauto. eapply Ordinal.lt_le; auto. }
      i. eapply Ordinal.le_lt_lt.
      { eapply H2. }
      eapply Ordinal.from_wf_lt. econs; eauto.
    Qed.

    Let next_cardinal_fixed: ~ not_fixed (next_cardinal D).
    Proof.
      ii. eapply least_lt_incr_acc in H; eauto.
      eapply Ordinal.lt_not_le.
      2: { eapply H. }
      eapply Ordinal.le_lt_lt.
      { eapply Ordinal.lt_le. eapply Ordinal.from_wf_set_upperbound. }
      eapply (Ordinal.build_upperbound (fun RWF => Ordinal.from_wf_set (proj2_sig RWF)) (exist _ _ strictly_increasing_well_founded)).
    Qed.

    Lemma _fixpoint_theorem:
      dle (next (rec (next_cardinal D))) (rec (next_cardinal D)).
    Proof.
      eapply NNPP. ii. eapply next_cardinal_fixed. eapply end_le_end.
      { eapply Ordinal.lt_le. eapply Ordinal.S_lt. }
      ii. eapply H.
      hexploit rec_S; auto.
      i. des. eapply (@dle_transitive (rec (Ordinal.S (next_cardinal D)))); auto.
      { eapply H1. }
      eapply (@dle_transitive (rec o0)); auto.
      eapply rec_le; eauto.
      destruct (total o0 (next_cardinal D)); auto.
      eapply Ordinal.S_spec in H2.
      exfalso. eapply Ordinal.lt_not_le.
      { eapply LT. }
      { eapply H2. }
    Qed.
  End REC.

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

      Let eventually_exhausted
        :
          exists o, forall x, (Ordinal.rec base next joinX o).(P) x.
      Proof.
        hexploit (_fixpoint_theorem base next joinX leX wfX); auto. i.
        exists (next_cardinal subos).
        hexploit next_exhausted.
        { eapply (rec_wf base next joinX leX wfX); eauto. }
        i. des; eauto. exfalso. eapply H1. eapply H. auto.
      Qed.

      Lemma choice_then_well_ordering_theorem
        :
          exists (R: X -> X -> Prop),
            well_founded R /\
            (forall x0 x1, R x0 x1 \/ x0 = x1 \/ R x1 x0).
      Proof.
        hexploit eventually_exhausted. i. des.
        assert (WF: wfX (Ordinal.rec base next joinX o)).
        { hexploit (@rec_wf _ base next joinX leX wfX); eauto. }
        exists (Ordinal.rec base next joinX o).(R). splits; auto.
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
    Variable B: Type.
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

    Let chain_join (A: Type) (cs: A -> chain): chain := fun b => exists a, cs a b.

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

      Lemma eventually_maximal: False.
      Proof.
        hexploit (_fixpoint_theorem base next chain_join chain_le wf); auto.
        i. inv H.
        hexploit (H0 (f (Ordinal.rec base next chain_join (next_cardinal chain)))); auto.
        { right. auto. }
        i. eapply (@antisym (f (Ordinal.rec base next chain_join (next_cardinal chain))) (f (Ordinal.rec base next chain_join (next_cardinal chain)))).
        { eapply INCR; auto.
          eapply (rec_wf base next chain_join chain_le wf); auto. }
        { eapply INCR; auto.
          eapply (rec_wf base next chain_join chain_le wf); auto. }
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
    Variable B: Type.
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
    Variable B: Type.
    Variable R: B -> B -> Prop.
    Hypothesis le_PreOrder: PreOrder R.
    Local Existing Instance le_PreOrder.

    Hypothesis upperbound_exists:
      forall (c: B -> Prop) (CHAIN: forall b0 b1 (IN0: c b0) (IN1: c b1), R b0 b1 \/ R b1 b0),
      exists b_u, forall b (IN: c b), R b b_u.

    Let equiv_class: Type :=
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
    Variable B: Type.
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
      Ordinal.lt (Ordinal.from_wf WF a0) (Ordinal.from_wf WF a1) \/
      (Ordinal.eq (Ordinal.from_wf WF a0) (Ordinal.from_wf WF a1) /\ RT a0 a1)
    .

    Lemma extended_total:
      forall a0 a1, extended a0 a1 \/ a0 = a1 \/ extended a1 a0.
    Proof.
      i. destruct (trichotomy (Ordinal.from_wf WF a0) (Ordinal.from_wf WF a1)) as [|[]].
      - left. left. auto.
      - destruct (@TOTAL a0 a1) as [|[]]; auto.
        + left. right. auto.
        + right. right. right. split; auto. symmetry. auto.
      - right. right. left. auto.
    Qed.

    Lemma extended_well_founded: well_founded extended.
    Proof.
      ii. hexploit (well_founded_induction
                      Ordinal.lt_well_founded
                      (fun o => forall a (LE: Ordinal.le (Ordinal.from_wf WF a) o), Acc extended a)); eauto.
      { clear a. intros o IH.
        assert (LTS: forall a (LT: Ordinal.lt (Ordinal.from_wf WF a) o), Acc extended a).
        { i. econs. i.
          hexploit (IH _ LT).
          { reflexivity. }
          i. inv H0. eauto.
        }
        i. eapply le_eq_or_lt in LE. des; auto.
        eapply (well_founded_induction
                  WFT (fun a => Ordinal.eq (Ordinal.from_wf WF a) o -> Acc extended a)); eauto.
        clear a LE. i. econs. i. inv H1.
        { eapply (IH (Ordinal.from_wf WF y)).
          { eapply Ordinal.lt_eq_lt; eauto. symmetry. auto. }
          { reflexivity. }
        }
        { des. eapply H; eauto. transitivity (Ordinal.from_wf WF x); auto. }
      }
      { eapply Ordinal.lt_le. eapply Ordinal.from_wf_set_upperbound. }
    Qed.

    Lemma extended_incl:
      forall a0 a1 (LT: R a0 a1), extended a0 a1.
    Proof.
      i. left. eapply Ordinal.from_wf_lt; auto.
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
        (LE: Ordinal.le (Ordinal.from_wf_set WFA) (Ordinal.from_wf_set WFB))
        (TOTALB: forall b0 b1, RB b0 b1 \/ b0 = b1 \/ RB b1 b0)
    :
      exists (f: A -> B), forall a0 a1 (LT: RA a0 a1), RB (f a0) (f a1).
  Proof.
    exploit (choice (fun a b => Ordinal.eq (Ordinal.from_wf WFA a) (Ordinal.from_wf WFB b))).
    { intros a. eapply from_wf_set_complete.
      eapply Ordinal.lt_le_lt; eauto. eapply Ordinal.from_wf_set_upperbound. }
    i. des. exists f. i. eapply Ordinal.from_wf_lt with (WF:=WFA) in LT.
    assert (Ordinal.lt (Ordinal.from_wf WFB (f a0)) (Ordinal.from_wf WFB (f a1))).
    { eapply (@Ordinal.le_lt_lt (Ordinal.from_wf WFA a0)); eauto.
      - eapply x0.
      - eapply (@Ordinal.lt_le_lt (Ordinal.from_wf WFA a1)); auto. eapply x0. }
    destruct (TOTALB (f a0) (f a1)) as [|[]].
    - auto.
    - rewrite H0 in *. eapply Ordinal.lt_not_le in H; ss. reflexivity.
    - eapply Ordinal.from_wf_lt with (WF:=WFB) in H0; eauto.
      exfalso. eapply Ordinal.lt_not_le in H; ss. eapply Ordinal.lt_le; auto.
  Qed.

  Lemma from_wf_set_comparable A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
        (WFA: well_founded RA) (WFB: well_founded RB)
        (TOTALA: forall a0 a1, RA a0 a1 \/ a0 = a1 \/ RA a1 a0)
        (TOTALB: forall b0 b1, RB b0 b1 \/ b0 = b1 \/ RB b1 b0)
    :
      (exists (f: A -> B), forall a0 a1 (LT: RA a0 a1), RB (f a0) (f a1)) \/
      (exists (f: B -> A), forall b0 b1 (LT: RB b0 b1), RA (f b0) (f b1)).
  Proof.
    destruct (total_le (Ordinal.from_wf_set WFA) (Ordinal.from_wf_set WFB)).
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
    eapply Ordinal.wf_mon.
    { eapply inj_projected_rel_incl. eapply INJ. }
    { eauto. }
  Qed.

  Lemma from_wf_projected_rel_eq A B (RA: A -> A -> Prop)
        (WFA: well_founded RA)
        (f: A -> B)
        (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
    :
      forall a, Ordinal.eq (Ordinal.from_wf WFA a) (Ordinal.from_wf (embed_projected_rel_well_founded WFA f INJ) (f a)).
  Proof.
    eapply (well_founded_induction WFA). i. split.
    - eapply Ordinal.from_wf_supremum. i. exploit H; eauto. i.
      eapply Ordinal.eq_lt_lt; eauto. eapply Ordinal.from_wf_lt.
      econs; eauto.
    - eapply Ordinal.from_wf_supremum. i. inv LT.
      eapply INJ in H2. subst. exploit H; eauto. i.
      symmetry in x0. eapply Ordinal.eq_lt_lt; eauto.
      eapply Ordinal.from_wf_lt; eauto.
  Qed.

  Lemma from_wf_set_projected_rel_le A B (RA: A -> A -> Prop)
        (WFA: well_founded RA)
        (f: A -> B)
        (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
    :
      Ordinal.le (Ordinal.from_wf_set WFA) (Ordinal.from_wf_set (embed_projected_rel_well_founded WFA f INJ)).
  Proof.
    eapply Ordinal.build_spec. i. eapply Ordinal.eq_lt_lt.
    { eapply from_wf_projected_rel_eq. }
    eapply Ordinal.build_upperbound.
  Qed.

  Lemma from_wf_set_projected_rel_eq A B (RA: A -> A -> Prop)
        (INHABITED: inhabited A)
        (WFA: well_founded RA)
        (f: A -> B)
        (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
    :
      Ordinal.eq (Ordinal.from_wf_set WFA) (Ordinal.from_wf_set (embed_projected_rel_well_founded WFA f INJ)).
  Proof.
    split.
    - eapply from_wf_set_projected_rel_le.
    - eapply Ordinal.build_spec. i.
      destruct (classic (exists a', f a' = a)).
      { des. subst. eapply Ordinal.eq_lt_lt.
        { symmetry. eapply from_wf_projected_rel_eq. }
        { eapply Ordinal.build_upperbound. }
      }
      { destruct INHABITED. eapply Ordinal.le_lt_lt.
        2: { eapply (Ordinal.build_upperbound _ X). }
        eapply Ordinal.from_wf_supremum. i. inv LT.
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
      forall a, Ordinal.eq (Ordinal.from_wf WFA a) (Ordinal.from_wf (projected_rel_sig_well_founded WFA f INJ) (to_projected_sig f a)).
  Proof.
    eapply (well_founded_induction WFA). i. split.
    - eapply Ordinal.from_wf_supremum. i. exploit H; eauto. i.
      eapply Ordinal.eq_lt_lt; eauto. eapply Ordinal.from_wf_lt.
      econs; eauto.
    - eapply Ordinal.from_wf_supremum. i. inv LT.
      eapply INJ in H2. subst. exploit H; eauto. i.
      symmetry in x0. eapply Ordinal.eq_lt_lt; eauto.
      eapply Ordinal.from_wf_lt; eauto.
  Qed.

  Lemma from_wf_set_projected_rel_sig_le A B (RA: A -> A -> Prop)
        (WFA: well_founded RA)
        (f: A -> B)
        (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
    :
      Ordinal.le (Ordinal.from_wf_set WFA) (Ordinal.from_wf_set (projected_rel_sig_well_founded WFA f INJ)).
  Proof.
    eapply Ordinal.build_spec. i. eapply Ordinal.eq_lt_lt.
    { eapply from_wf_projected_rel_sig_eq. }
    eapply Ordinal.build_upperbound.
  Qed.

  Lemma from_wf_set_projected_rel_sig_eq A B (RA: A -> A -> Prop)
        (WFA: well_founded RA)
        (f: A -> B)
        (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
    :
      Ordinal.eq (Ordinal.from_wf_set WFA) (Ordinal.from_wf_set (projected_rel_sig_well_founded WFA f INJ)).
  Proof.
    split.
    - eapply from_wf_set_projected_rel_sig_le.
    - eapply Ordinal.build_spec. i. destruct a. des. subst. eapply Ordinal.eq_lt_lt.
      { symmetry. eapply from_wf_projected_rel_sig_eq. }
      { eapply Ordinal.build_upperbound. }
  Qed.

  Definition union_set (A: Type) (Ts: A -> Type): Type := @sigT A (fun a => option (Ts a)).

  Inductive union_rel (A: Type)
            (Ts: A -> Type) (R: forall a, Ts a -> Ts a -> Prop):
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

  Lemma union_rel_well_founded (A: Type) (Ts: A -> Type)
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

  Lemma from_wf_union (A: Type) (Ts: A -> Type)
        (R: forall a, Ts a -> Ts a -> Prop)
        (WF: forall a, well_founded (R a))
        (a: A) (x: Ts a)
    :
      Ordinal.eq (Ordinal.from_wf (WF a) x)
                 (Ordinal.from_wf (union_rel_well_founded R WF) (existT _ a (Some x))).
  Proof.
    revert x. eapply (well_founded_induction (WF a)).
    i. split.
    { eapply Ordinal.from_wf_supremum. i. specialize (H _ LT). inv H.
      eapply Ordinal.le_lt_lt; eauto. eapply Ordinal.from_wf_lt. econs; eauto. }
    { eapply Ordinal.from_wf_supremum. i. dependent destruction LT.
      specialize (H _ LT). inv H.
      eapply Ordinal.le_lt_lt; eauto. eapply Ordinal.from_wf_lt. auto. }
  Qed.

  Lemma from_wf_set_union (A: Type) (Ts: A -> Type)
        (R: forall a, Ts a -> Ts a -> Prop)
        (WF: forall a, well_founded (R a))
    :
      Ordinal.eq (@Ordinal.build A (fun a => Ordinal.from_wf_set (WF a)))
                 (Ordinal.from_wf_set (union_rel_well_founded R WF)).
  Proof.
    split.
    { econs. i. exists (existT _ a0 None). eapply Ordinal.build_spec. i.
      eapply (@Ordinal.le_lt_lt (Ordinal.from_wf (union_rel_well_founded R WF) (existT _ a0 (Some a)))).
      { eapply from_wf_union. }
      { eapply Ordinal.from_wf_lt. econs. }
    }
    { econs. i. destruct a0 as [a0 [x|]].
      { exists a0. transitivity (Ordinal.from_wf (WF a0) x).
        { eapply from_wf_union. }
        { eapply Ordinal.lt_le. eapply Ordinal.from_wf_set_upperbound. }
      }
      { exists a0. eapply Ordinal.from_wf_supremum. i.
        dependent destruction LT.
        eapply (@Ordinal.le_lt_lt (Ordinal.from_wf (WF a0) x)).
        { eapply from_wf_union. }
        { eapply Ordinal.from_wf_set_upperbound. }
      }
    }
  Qed.

  Fixpoint to_set (o: Ordinal.t): @sigT Type (fun A => A -> A -> Prop) :=
    match o with
    | @Ordinal.build A os => existT
                               _
                               (union_set (fun a => projT1 (to_set (os a))))
                               (union_rel (fun a => projT2 (to_set (os a))))
    end.

  Lemma to_set_well_founded: forall o, well_founded (projT2 (to_set o)).
  Proof.
    induction o. ss. eapply union_rel_well_founded; auto.
  Defined.

  Lemma to_set_eq o:
    Ordinal.eq o (Ordinal.from_wf_set (to_set_well_founded o)).
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
      Ordinal.eq (Ordinal.from_wf WF a0) (Ordinal.from_wf (cut_rel_well_founded WF a1) (exist _ a0 LT)).
  Proof.
    eapply (well_founded_induction
              WF
              (fun a0 => forall (LT: R a0 a1), Ordinal.eq (Ordinal.from_wf WF a0) (Ordinal.from_wf (cut_rel_well_founded WF a1) (exist _ a0 LT)))).
    intros a0 IH. i. split.
    { eapply Ordinal.from_wf_supremum. i.
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
      eapply (@Ordinal.le_lt_lt (Ordinal.from_wf (cut_rel_well_founded WF a1)
                                                 (exist _ a2 LT1))).
      { eapply IH; auto. }
      { eapply Ordinal.from_wf_lt. ss. }
    }
    { eapply Ordinal.from_wf_supremum. i. destruct a2 as [a2 LT1].
      unfold cut_rel in LT0. ss.
      eapply (@Ordinal.le_lt_lt (Ordinal.from_wf WF a2)).
      { eapply IH; auto. }
      { eapply Ordinal.from_wf_lt. ss. }
    }
  Qed.

  Lemma from_wf_set_cut A (R: A -> A -> Prop) (WF: well_founded R)
        (TOTAL: forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0)
        (a1: A):
      Ordinal.eq (Ordinal.from_wf WF a1) (Ordinal.from_wf_set (cut_rel_well_founded WF a1)).
  Proof.
    split.
    { eapply Ordinal.from_wf_supremum. i.
      eapply Ordinal.lt_intro with (a:=exist _ a0 LT).
      eapply from_wf_cut; eauto. }
    { eapply Ordinal.build_spec. intros [a0 r].
      eapply (@Ordinal.le_lt_lt (Ordinal.from_wf WF a0)).
      { eapply from_wf_cut; eauto. }
      { eapply Ordinal.from_wf_lt; eauto. }
    }
  Qed.

  Lemma to_total_exists (o: Ordinal.t):
    exists (A: Type) (R: A -> A -> Prop) (WF: well_founded R),
      Ordinal.eq o (Ordinal.from_wf_set WF) /\
      (forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0).
  Proof.
    hexploit (to_set_eq o). intros EQ.
    hexploit (well_order_extendable (to_set_well_founded o)). i. des.
    assert (Ordinal.le o (Ordinal.from_wf_set H)).
    { transitivity (Ordinal.from_wf_set (to_set_well_founded o)); auto.
      { eapply EQ. }
      { eapply Ordinal.from_wf_set_le; auto. }
    }
    eapply le_eq_or_lt in H2. des.
    { eapply from_wf_set_complete in H2. des.
      hexploit (from_wf_set_cut H H1 a). i.
      eexists _, _, (cut_rel_well_founded H a). splits.
      { transitivity (Ordinal.from_wf H a); auto. }
      { eapply cut_rel_total; eauto. }
    }
    { esplits; eauto. }
  Qed.

  Section TOTALIFY.
    (* propositional extensionality is used in this section *)
    Variable A: Type.
    Variable R: A -> A -> Prop.
    Hypothesis WF: well_founded R.

    Definition equiv_class: Type :=
      @sig (A -> Prop) (fun s => (exists a, s a) /\
                                 (forall a0 a1 (IN0: s a0), s a1 <-> Ordinal.eq (Ordinal.from_wf WF a0) (Ordinal.from_wf WF a1))).

    Program Definition to_equiv_class (a0: A): equiv_class :=
      exist _ (fun a1 => Ordinal.eq (Ordinal.from_wf WF a0) (Ordinal.from_wf WF a1)) _.
    Next Obligation.
      split.
      { exists a0. reflexivity. }
      { i. split; i.
        - transitivity (Ordinal.from_wf WF a0); eauto. symmetry. auto.
        - transitivity (Ordinal.from_wf WF a1); eauto.
      }
    Qed.

    Let to_equiv_class_equiv a (s: equiv_class) (IN: proj1_sig s a):
      s = to_equiv_class a.
    Proof.
      destruct s. ss. unfold to_equiv_class.
      assert (x = (fun a1 : A => Ordinal.eq (Ordinal.from_wf WF a) (Ordinal.from_wf WF a1))).
      { extensionality a1. eapply propositional_extensionality. des. split.
        { i. eapply a2; eauto. }
        { i. eapply a2; eauto. }
      }
      subst. f_equal. eapply proof_irrelevance.
    Qed.

    Definition equiv_class_rel: equiv_class -> equiv_class -> Prop :=
      fun s0 s1 => exists a0 a1, (proj1_sig s0) a0 /\ (proj1_sig s1) a1 /\ Ordinal.lt (Ordinal.from_wf WF a0) (Ordinal.from_wf WF a1).

    Lemma to_equiv_class_preserve a0 a1 (LT: R a0 a1):
      equiv_class_rel (to_equiv_class a0) (to_equiv_class a1).
    Proof.
      exists a0, a1. ss. splits.
      - reflexivity.
      - reflexivity.
      - eapply Ordinal.from_wf_lt; auto.
    Qed.

    Lemma equiv_class_total:
      forall s0 s1, equiv_class_rel s0 s1 \/ s0 = s1 \/ equiv_class_rel s1 s0.
    Proof.
      i. hexploit (proj2_sig s0). i. des. hexploit (proj2_sig s1). i. des.
      destruct (trichotomy (Ordinal.from_wf WF a) (Ordinal.from_wf WF a0)) as [|[]].
      - left. unfold equiv_class_rel. esplits; eauto.
      - right. left. assert (proj1_sig s0 = proj1_sig s1).
        { extensionality x. eapply propositional_extensionality. split; i.
          - eapply H2; eauto. transitivity (Ordinal.from_wf WF a); eauto.
            + symmetry. auto.
            + eapply (H0 a x); auto.
          - eapply H0; eauto. transitivity (Ordinal.from_wf WF a0); eauto.
            eapply (H2 a0 x); auto.
        }
        destruct s0, s1. ss. subst. f_equal. eapply proof_irrelevance.
      - right. right. unfold equiv_class_rel. esplits; eauto.
    Qed.

    Lemma equiv_class_well_founded: well_founded equiv_class_rel.
    Proof.
      assert (forall (o: Ordinal.t), forall (s: equiv_class) a0 (IN: proj1_sig s a0) (LT: Ordinal.lt (Ordinal.from_wf WF a0) o), Acc equiv_class_rel s).
      { eapply (well_founded_induction Ordinal.lt_well_founded (fun o => forall (s: equiv_class) a0 (IN: proj1_sig s a0) (LT: Ordinal.lt (Ordinal.from_wf WF a0) o), Acc equiv_class_rel s)).
        i. econs. i. unfold equiv_class_rel in H0. des.
        hexploit (proj2 (proj2_sig s) a0 a2); auto. i. dup H1.
        eapply H3 in H4. clear H3. eapply (H (Ordinal.from_wf WF a0)); eauto.
        eapply Ordinal.lt_eq_lt; eauto.
      }
      ii. hexploit (proj2_sig a); eauto. i. des.
      hexploit (H (Ordinal.S (Ordinal.from_wf WF a0))); eauto. eapply Ordinal.S_lt.
    Qed.

    Lemma to_equiv_class_eq a:
      Ordinal.eq (Ordinal.from_wf WF a) (Ordinal.from_wf equiv_class_well_founded (to_equiv_class a)).
    Proof.
      assert (forall (o: Ordinal.t), forall a (LT: Ordinal.lt (Ordinal.from_wf WF a) o), Ordinal.eq (Ordinal.from_wf WF a) (Ordinal.from_wf equiv_class_well_founded (to_equiv_class a))).
      { eapply (well_founded_induction Ordinal.lt_well_founded (fun o => forall a (LT: Ordinal.lt (Ordinal.from_wf WF a) o), Ordinal.eq (Ordinal.from_wf WF a) (Ordinal.from_wf equiv_class_well_founded (to_equiv_class a)))).
        i. split.
        { eapply Ordinal.from_wf_supremum. i. dup LT0. eapply (Ordinal.from_wf_lt WF) in LT0; eauto.
          hexploit H; eauto. i. eapply Ordinal.le_lt_lt; [eapply H0|].
          eapply Ordinal.from_wf_lt. eapply to_equiv_class_preserve. auto.
        }
        { eapply Ordinal.from_wf_supremum. i. unfold equiv_class_rel in LT0. des. ss.
          hexploit (H _ LT a2).
          { eapply Ordinal.lt_eq_lt; eauto. } i.
          eapply Ordinal.lt_eq_lt; eauto. eapply Ordinal.le_lt_lt; eauto.
          etransitivity; [|eapply H0].
          eapply to_equiv_class_equiv in LT0. subst. reflexivity.
        }
      }
      eapply (H (Ordinal.S (Ordinal.from_wf WF a))). eapply Ordinal.S_lt.
    Qed.

    Lemma from_wf_set_equiv_class:
      Ordinal.eq (Ordinal.from_wf_set WF) (Ordinal.from_wf_set equiv_class_well_founded).
    Proof.
      split.
      { eapply Ordinal.build_spec. i. eapply Ordinal.eq_lt_lt.
        { eapply to_equiv_class_eq. }
        { eapply Ordinal.from_wf_set_upperbound. }
      }
      { eapply Ordinal.build_spec. i. hexploit (proj2_sig a). i. des.
        eapply to_equiv_class_equiv in H. subst.
        eapply Ordinal.eq_lt_lt.
        { symmetry. eapply to_equiv_class_eq. }
        { eapply Ordinal.from_wf_set_upperbound. }
      }
    Qed.
  End TOTALIFY.

  Definition to_total_set (o: Ordinal.t): Type := equiv_class (to_set_well_founded o).
  Definition to_total_rel (o: Ordinal.t): (to_total_set o) -> (to_total_set o) -> Prop :=
    @equiv_class_rel _ _ (to_set_well_founded o).
  Arguments to_total_rel: clear implicits.

  Lemma to_total_well_founded (o: Ordinal.t): well_founded (to_total_rel o).
  Proof.
    eapply equiv_class_well_founded.
  Defined.
  Arguments to_total_well_founded: clear implicits.

  Lemma to_total_eq (o: Ordinal.t):
    Ordinal.eq o (Ordinal.from_wf_set (@to_total_well_founded o)).
  Proof.
    etransitivity.
    - eapply to_set_eq.
    - eapply (from_wf_set_equiv_class (@to_set_well_founded o)).
  Qed.

  Lemma to_total_total (o: Ordinal.t):
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
    Let _cardinal_lt (A B: Type): Prop := _cardinal_le A B /\ ~ _cardinal_le B A.

    Let _cardinal_total_le: forall (A B: Type), _cardinal_le A B \/ _cardinal_le B A.
    Proof.
      i. hexploit (set_comparable A B). i. des.
      - left. econs; eauto.
      - right. econs; eauto.
    Qed.

    Section CARDINAL.
      Variable A: Type.

      Definition is_cardinal (c: Ordinal.t): Prop :=
        is_meet (fun o =>
                   exists (R: A -> A -> Prop) (WF: well_founded R),
                     (forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0) /\
                     Ordinal.eq (Ordinal.from_wf_set WF) o) c.

      Lemma is_cardinal_exists: exists c, is_cardinal c.
      Proof.
        eapply meet_exists.
        hexploit (@_well_ordering_theorem A); eauto. i. des.
        exists (Ordinal.from_wf_set H), R, H. splits; auto. reflexivity.
      Qed.

      Lemma cardinal_unique c0 c1 (CARD0: is_cardinal c0) (CARD1: is_cardinal c1):
        Ordinal.eq c0 c1.
      Proof.
        unfold is_cardinal, is_meet in *. des. split.
        - eapply CARD4; eauto.
        - eapply CARD2; eauto.
      Qed.

      Lemma eq_is_cardinal c0 c1 (EQ: Ordinal.eq c0 c1) (CARD0: is_cardinal c0):
        is_cardinal c1.
      Proof.
        unfold is_cardinal, is_meet in *. des. split.
        - exists R, WF. splits; auto. transitivity c0; auto.
        - i. transitivity c0; auto. eapply EQ.
      Qed.

      Let X: Type :=
        @sig
          (@sigT (A -> Prop) (fun s => sig s -> sig s-> Prop))
          (fun PR =>
             well_founded (projT2 PR) /\
             (forall a0 a1, projT2 PR a0 a1 \/ a0 = a1 \/ projT2 PR a1 a0) /\
             (forall (f: A -> sig (projT1 PR)),
                 exists a0 a1, f a0 = f a1 /\ a0 <> a1)).

      Let Y (x: X): Ordinal.t :=
        @Ordinal.from_wf_set (sig (projT1 (proj1_sig x))) _ (proj1 (proj2_sig x)).

      Definition cardinal := @Ordinal.build X Y.

      Lemma cardinal_lowerbound (R: A -> A -> Prop) (WF: well_founded R)
            (TOTAL: forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0):
        Ordinal.le cardinal (Ordinal.from_wf_set WF).
      Proof.
        eapply Ordinal.build_spec. i. unfold Y.
        destruct a as [[P0 R0] [WF0 [TOTAL0 SMALL]]]; ss.
        eapply (@Ordinal.le_lt_lt (Ordinal.from_wf_set WF0)).
        { eapply Ordinal.same_wf_set_le. }
        destruct (total (Ordinal.from_wf_set WF) (Ordinal.from_wf_set WF0)); auto.
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
          Ordinal.lt (Ordinal.from_wf_set WF) cardinal.
      Proof.
        inv CARD.
        assert (CLT: ~ _cardinal_le A B).
        { ii. eapply H0. eauto. } inv H.
        hexploit (from_wf_set_projected_rel_sig_eq WF _ INJ). i.
        hexploit (well_order_extendable (projected_rel_sig_well_founded WF f INJ)). i. des.
        hexploit (Ordinal.from_wf_set_le H2 (projected_rel_sig_well_founded WF f INJ) H1). i.
        eapply Ordinal.le_lt_lt.
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
        hexploit (@Ordinal.build_upperbound
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
        eapply Ordinal.le_lt_lt; [|eapply H6].
        eapply Ordinal.same_wf_set_le.
      Qed.

      Lemma _cardinal_supremum c
            (UPPER: forall (B: Type) (CARD: _cardinal_lt B A)
                           (R: B -> B -> Prop) (WF: well_founded R),
                Ordinal.lt (Ordinal.from_wf_set WF) c)
        :
          Ordinal.le cardinal c.
      Proof.
        eapply Ordinal.build_spec. i.
        destruct a as [[P0 R0] [WF0 [TOTAL SMALL]]]; ss. unfold Y. ss.
        eapply (@Ordinal.le_lt_lt (Ordinal.from_wf_set WF0)).
        { eapply Ordinal.same_wf_set_le. }
        eapply UPPER.
        assert (NLE: ~ _cardinal_le A (sig P0)).
        { ii. inv H. hexploit (SMALL f); eauto. i. des.
          eapply INJ in H. ss. }
        destruct (_cardinal_total_le A (sig P0)); ss.
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
          { transitivity (Ordinal.from_wf_set WF0).
            2: { eapply H2. }
            transitivity c.
            { eapply H1. }
            inv H5.
            hexploit (projected_rel_rev_well_founded WF0 f); auto. i.
            hexploit (H0 (Ordinal.from_wf_set H5)).
            { eexists _, H5. splits; auto.
              - i. destruct (H3 (f a0) (f a1)) as [|[]]; auto.
              - reflexivity. }
            i. transitivity (Ordinal.from_wf_set H5); auto.
            eapply Ordinal.from_wf_set_inj; eauto.
          }
          { assert (CLT: _cardinal_lt A0 A).
            { des; ss. }
            hexploit (_cardinal_upperbound CLT WF0). i.
            exfalso. eapply Ordinal.lt_not_le.
            { eapply H6. }
            { eapply H2. }
          }
        - i. des. eapply Ordinal.build_spec. i. unfold Y.
          destruct a as [[P0 R0] [WF0 [TOTAL SMALL]]]; ss.
        eapply (@Ordinal.le_lt_lt (Ordinal.from_wf_set WF0)).
        { eapply Ordinal.same_wf_set_le. }
          eapply Ordinal.lt_eq_lt.
          { symmetry. eapply IN0. }
          destruct (total (Ordinal.from_wf_set WF) (Ordinal.from_wf_set WF0)); auto.
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
      _cardinal_le A B <-> Ordinal.le (cardinal A) (cardinal B).
    Proof.
      split. i.
      - hexploit (cardinal_is_cardinal B). i. destruct H0. des.
        transitivity (Ordinal.from_wf_set WF); auto.
        2: { eapply H2. }
        inv H. transitivity (Ordinal.from_wf_set (projected_rel_rev_well_founded WF f INJ)).
        { eapply cardinal_is_cardinal.
          exists (projected_rel_rev R f), (projected_rel_rev_well_founded WF f INJ). splits; auto.
          - i. destruct (H0 (f a0) (f a1)) as [|[]]; auto.
          - reflexivity.
        }
        { eapply Ordinal.from_wf_set_inj. instantiate (1:=f). i. apply LT. }
      - hexploit (cardinal_is_cardinal B). i. destruct H. des.
        i. eapply NNPP. ii. destruct (_cardinal_total_le A B); ss.
        hexploit (_cardinal_upperbound).
        { split; eauto. }
        instantiate (1:=WF). i. eapply Ordinal.lt_not_le; eauto.
        transitivity (cardinal B); auto. apply H2.
    Qed.

    Lemma _cardinal_eq_iff A B:
      _cardinal_eq A B <-> Ordinal.eq (cardinal A) (cardinal B).
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
      _cardinal_lt A B <-> Ordinal.lt (cardinal A) (cardinal B).
    Proof.
      split; i.
      - inv H. eapply _cardinal_le_iff in H0.
        eapply le_eq_or_lt in H0. des; auto.
        exfalso. eapply H1. eapply _cardinal_eq_iff; eauto.
      - split.
        + eapply _cardinal_le_iff. eapply Ordinal.lt_le; eauto.
        + ii. eapply _cardinal_le_iff in H0.
          eapply Ordinal.lt_not_le; eauto.
    Qed.

    Lemma cardinal_size_le A B (R: B -> B -> Prop) (WF: well_founded R)
          (TOTAL: forall b0 b1, R b0 b1 \/ b0 = b1 \/ R b1 b0)
          (LE: Ordinal.le (cardinal A) (Ordinal.from_wf_set WF)):
      Ordinal.le (cardinal A) (cardinal B).
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
          (EQ: Ordinal.eq (cardinal A) (Ordinal.from_wf_set WF)):
      Ordinal.eq (cardinal A) (cardinal B).
    Proof.
      split; i.
      - eapply cardinal_size_le; eauto. eapply EQ.
      - transitivity (Ordinal.from_wf_set WF).
        + eapply (cardinal_is_cardinal B). esplits; eauto. reflexivity.
        + eapply EQ.
    Qed.

    Lemma le_cardinal_le A B (RA: A -> A -> Prop) (RB: B -> B -> Prop) (WFA: well_founded RA) (WFB: well_founded RB)
          (TOTAL: forall a0 a1, RA a0 a1 \/ a0 = a1 \/ RA a1 a0)
          (LE: Ordinal.le (Ordinal.from_wf_set WFA) (Ordinal.from_wf_set WFB))
      :
        Ordinal.le (cardinal A) (cardinal B).
    Proof.
      hexploit (well_order_extendable WFB); eauto. i. des.
      hexploit (@from_wf_set_embed _ _ _ _ WFA H); eauto.
      { transitivity (Ordinal.from_wf_set WFB); auto.
        eapply Ordinal.from_wf_set_le; eauto. }
      i. des. eapply _cardinal_le_iff.
      eapply _cardinal_le_intro with (f:=f). i.
      destruct (TOTAL a0 a1) as [|[]]; auto.
      { eapply H2 in H3. rewrite EQ in *.
        exfalso. eapply (well_founded_irreflexive H); eauto. }
      { eapply H2 in H3. rewrite EQ in *.
        exfalso. eapply (well_founded_irreflexive H); eauto. }
    Qed.

    Lemma to_total_le o0 o1 (LE: Ordinal.le o0 o1):
      Ordinal.le (cardinal (to_total_set o0)) (cardinal (to_total_set o1)).
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

    Lemma to_total_cardinal_le o:
      Ordinal.le (cardinal (to_total_set o)) o.
    Proof.
      transitivity (Ordinal.from_wf_set (to_total_well_founded o)).
      { eapply cardinal_is_cardinal.
        exists (to_total_rel o), (to_total_well_founded o). split; auto.
        - eapply to_total_total.
        - reflexivity.
      }
      { eapply to_total_eq. }
    Qed.

    Lemma cardinal_to_total_bij1 A:
      Ordinal.eq (cardinal A) (cardinal (to_total_set (cardinal A))).
    Proof.
      eapply cardinal_size_eq.
      { eapply to_total_total. }
      eapply to_total_eq.
    Qed.

    Lemma cardinal_to_total_bij2 A c (CARDINAL: is_cardinal A c):
      Ordinal.eq c (cardinal (to_total_set c)).
    Proof.
      hexploit cardinal_unique.
      { eapply CARDINAL. }
      { eapply cardinal_is_cardinal. }
      i. transitivity (cardinal A); auto.
      transitivity (cardinal (to_total_set (cardinal A))).
      { eapply cardinal_to_total_bij1. }
      split.
      { eapply to_total_le. apply H. }
      { eapply to_total_le. apply H. }
    Qed.

    Lemma from_wf_set_to_total A (R: A -> A -> Prop) (WF: well_founded R):
      Ordinal.le (cardinal (to_total_set (Ordinal.from_wf_set WF))) (cardinal A).
    Proof.
      hexploit (well_order_extendable WF); eauto. i. des.
      assert (Ordinal.le (Ordinal.from_wf_set (to_total_well_founded (Ordinal.from_wf_set WF))) (Ordinal.from_wf_set H)).
      { transitivity (Ordinal.from_wf_set WF).
        { eapply to_total_eq. }
        { eapply Ordinal.from_wf_set_le; auto. }
      }
      dup H2. eapply from_wf_set_embed in H2; auto. des.
      hexploit (@from_wf_set_embed _ _ _ _ (to_total_well_founded (Ordinal.from_wf_set WF)) H); auto.
      i. des. eapply _cardinal_le_iff.
      eapply _cardinal_le_intro with (f:=f0).
      i. destruct (to_total_total a0 a1) as [|[]]; auto.
      { eapply H4 in H5. rewrite EQ in *. exfalso.
        eapply (well_founded_irreflexive H); eauto. }
      { eapply H4 in H5. rewrite EQ in *. exfalso.
        eapply (well_founded_irreflexive H); eauto. }
    Qed.

    Lemma total_from_wf_inj A (R: A -> A -> Prop) (WF: well_founded R)
          (TOTAL: forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0)
      :
        forall a0 a1,
          a0 = a1 <-> Ordinal.eq (Ordinal.from_wf WF a0) (Ordinal.from_wf WF a1).
    Proof.
      i. split.
      { i. subst. reflexivity. }
      { i. destruct (TOTAL a0 a1) as [|[]]; auto.
        { eapply (Ordinal.from_wf_lt WF) in H0. exfalso.
          eapply Ordinal.lt_not_le; eauto. eapply H. }
        { eapply (Ordinal.from_wf_lt WF) in H0. exfalso.
          eapply Ordinal.lt_not_le; eauto. eapply H. }
      }
    Qed.

    Lemma same_cardinality_bijection A B
          (CARDINAL: Ordinal.eq (cardinal A) (cardinal B))
      :
        exists (f: A -> B),
          (forall a0 a1 (EQ: f a0 = f a1), a0 = a1) /\
          (forall b, exists a, f a = b).
    Proof.
      hexploit (cardinal_is_cardinal A). i. inv H. des.
      hexploit (cardinal_is_cardinal B). i. inv H. des.
      hexploit (choice (fun a b => Ordinal.eq (Ordinal.from_wf WF a) (Ordinal.from_wf WF0 b))).
      { i. hexploit (@from_wf_set_complete _ _ WF0 (Ordinal.from_wf WF x)).
        { eapply Ordinal.lt_eq_lt.
          { eapply H5. }
          eapply Ordinal.lt_eq_lt.
          { symmetry. eapply CARDINAL. }
          eapply Ordinal.lt_eq_lt.
          { symmetry. eapply H2. }
          eapply Ordinal.from_wf_set_upperbound.
        }
        i. des. eauto.
      }
      i. des. exists f. splits; auto.
      { i. eapply (total_from_wf_inj WF); eauto.
        etransitivity.
        { eapply H. }
        etransitivity.
        2: { symmetry. eapply H. }
        rewrite EQ. reflexivity.
      }
      { i. hexploit (@from_wf_set_complete _ _ WF (Ordinal.from_wf WF0 b)).
        { eapply Ordinal.lt_eq_lt.
          { eapply H2. }
          eapply Ordinal.lt_eq_lt.
          { eapply CARDINAL. }
          eapply Ordinal.lt_eq_lt.
          { symmetry. eapply H5. }
          eapply Ordinal.from_wf_set_upperbound.
        }
        i. des. exists a. eapply (total_from_wf_inj WF0); auto.
        etransitivity.
        { symmetry. eapply H. }
        { symmetry. eapply H6. }
      }
    Qed.

    Lemma sum_of_smaller o:
      exists (os: to_total_set o -> Ordinal.t),
        Ordinal.eq o (Ordinal.build os).
    Proof.
      hexploit (to_total_eq o). i.
      exists (fun x => Ordinal.from_wf (to_total_well_founded o) x).
      eapply H.
    Qed.

    Lemma sum_of_smaller_same_cardinal o A (EQ: Ordinal.eq (cardinal A) (cardinal (to_total_set o))):
      exists (os: A -> Ordinal.t),
        Ordinal.eq o (Ordinal.build os).
    Proof.
      hexploit (sum_of_smaller o). i. des.
      eapply same_cardinality_bijection in EQ. des.
      exists (fun a => os (f a)). etransitivity.
      { eapply H. }
      split.
      { eapply Ordinal.build_spec. i. hexploit (EQ0 a). i. des.
        subst. eapply (Ordinal.build_upperbound (fun a => os (f a)) a0). }
      { eapply Ordinal.build_spec. i.
        eapply (Ordinal.build_upperbound os (f a)). }
    Qed.
  End CARDINALITY.

  Section NEXT.
    Variable A: Type.
    Let X: Type := @sig (A -> A -> Prop) (@well_founded _).

    Let Y (x: X): Ordinal.t := Ordinal.from_wf_set (proj2_sig x).

    Lemma next_cardinal_upperbound B (R: B -> B -> Prop) (WF: well_founded R)
          (CARD: Ordinal.le (cardinal B) (cardinal A))
      : Ordinal.lt (Ordinal.from_wf_set WF) (next_cardinal A).
    Proof.
      eapply _cardinal_le_iff in CARD. inv CARD.
      eapply (@Ordinal.le_lt_lt (Ordinal.from_wf_set (embed_projected_rel_well_founded WF f INJ))).
      { eapply Ordinal.from_wf_set_inj. instantiate (1:=f). i. econs; eauto. }
      eapply (@Ordinal.build_upperbound X Y (exist _ _ (embed_projected_rel_well_founded WF f INJ))).
    Qed.

    Lemma next_cardinal_incr
      : Ordinal.lt (cardinal A) (next_cardinal A).
    Proof.
      hexploit (cardinal_is_cardinal A). i. inv H. des.
      eapply Ordinal.eq_lt_lt.
      { symmetry. eapply H2. }
      eapply next_cardinal_upperbound.
      reflexivity.
    Qed.

    Lemma next_cardinal_supremum B (CARD: Ordinal.lt (cardinal A) (cardinal B)):
      Ordinal.le (next_cardinal A) (cardinal B).
    Proof.
      eapply Ordinal.build_spec. i. destruct a as [R WF]. unfold Y. ss.
      destruct (total (cardinal B) (Ordinal.from_wf_set WF)); auto.
      hexploit (cardinal_is_cardinal B); eauto. i. inv H0. des.
      hexploit (well_order_extendable WF); eauto. i. des.
      hexploit (@from_wf_set_embed _ _ _ _ WF0 H3); auto.
      { transitivity (cardinal B); auto.
        { eapply H0. }
        transitivity (Ordinal.from_wf_set WF); auto.
        eapply Ordinal.from_wf_set_le; auto.
      }
      i. des. exfalso.
      eapply _cardinal_lt_iff in CARD. des.
      eapply CARD0.
      eapply _cardinal_le_intro with (f:=f). i.
      destruct (H1 a0 a1) as [|[]]; auto.
      - eapply H6 in H7. rewrite EQ in *.
        exfalso. eapply (well_founded_irreflexive H3); eauto.
      - eapply H6 in H7. rewrite EQ in *.
        exfalso. eapply (well_founded_irreflexive H3); eauto.
    Qed.

    Lemma next_cardinal_is_cardinal:
      is_cardinal (to_total_set (next_cardinal A)) (next_cardinal A).
    Proof.
      split.
      { exists (to_total_rel (next_cardinal A)), (to_total_well_founded (next_cardinal A)).
        splits; auto.
        - eapply to_total_total.
        - symmetry. apply to_total_eq.
      }
      i. des. eapply Ordinal.build_spec. i. destruct a as [R0 WF0]. unfold Y. ss.
      destruct (total o1 (Ordinal.from_wf_set WF0)); auto.
      assert (LE: Ordinal.le (Ordinal.from_wf_set WF) (Ordinal.from_wf_set WF0)).
      { transitivity o1; auto. eapply IN0. }
      eapply le_cardinal_le in LE; auto. exfalso.
      eapply (next_cardinal_upperbound (to_total_well_founded (next_cardinal A))) in LE.
      eapply Ordinal.lt_not_le.
      { eapply LE. }
      { eapply to_total_eq. }
    Qed.

    Lemma next_cardinal_le_power_set:
      Ordinal.le (next_cardinal A) (cardinal (A -> Prop)).
    Proof.
      eapply next_cardinal_supremum.
      eapply _cardinal_lt_iff.
      assert (LE: _cardinal_le A (A -> Prop)).
      { eapply _cardinal_le_intro with (fun a0 a1 => a0 = a1).
        i. eapply equal_f with (x:=a1) in EQ.
        rewrite EQ. auto.
      }
      { split; auto. ii. inv H.
        hexploit (choice (fun (a: A) (P1: A -> Prop) =>
                            forall P0, f P0 = a -> P0 = P1)).
        { i. destruct (classic (exists P0, f P0 = x)).
          { des. exists P0. i. rewrite <- H0 in *. eauto. }
          { exists (fun _ => True). i. exfalso. eapply H; eauto. }
        }
        i. des. hexploit (cantor_theorem f0). i. des.
        eapply (H0 (f P)). exploit H; eauto.
      }
    Qed.
  End NEXT.

  Lemma next_cardinal_le A B
        (CARDINAL: Ordinal.le (cardinal A) (cardinal B)):
    Ordinal.le (next_cardinal A) (next_cardinal B).
  Proof.
    assert (EQ: Ordinal.eq (next_cardinal B) (cardinal (to_total_set (next_cardinal B)))).
    { eapply cardinal_unique.
      { eapply next_cardinal_is_cardinal. }
      { eapply cardinal_is_cardinal. }
    }
    transitivity (cardinal (to_total_set (next_cardinal B))).
    2: { apply EQ. }
    eapply next_cardinal_supremum.
    eapply Ordinal.lt_le_lt.
    2: { eapply EQ. }
    eapply Ordinal.le_lt_lt.
    { eapply CARDINAL. }
    { eapply next_cardinal_incr. }
  Qed.

  Lemma next_cardinal_eq A B
        (CARDINAL: Ordinal.eq (cardinal A) (cardinal B)):
    Ordinal.eq (next_cardinal A) (next_cardinal B).
  Proof.
    split.
    - eapply next_cardinal_le. eapply CARDINAL.
    - eapply next_cardinal_le. eapply CARDINAL.
  Qed.

  Lemma next_cardinal_lt A B
        (CARDINAL: Ordinal.lt (cardinal A) (cardinal B)):
    Ordinal.lt (next_cardinal A) (next_cardinal B).
  Proof.
    eapply next_cardinal_supremum in CARDINAL.
    eapply Ordinal.le_lt_lt.
    { eapply CARDINAL. }
    { eapply next_cardinal_incr. }
  Qed.

  Lemma next_cardinal_le_iff A B:
    Ordinal.le (cardinal A) (cardinal B) <-> Ordinal.le (next_cardinal A) (next_cardinal B).
  Proof.
    split; i.
    { eapply next_cardinal_le; auto. }
    { destruct (total (cardinal A) (cardinal B)); auto.
      eapply next_cardinal_lt in H0. exfalso. eapply Ordinal.lt_not_le; eauto. }
  Qed.

  Lemma next_cardinal_eq_iff A B:
    Ordinal.eq (cardinal A) (cardinal B) <-> Ordinal.eq (next_cardinal A) (next_cardinal B).
  Proof.
    split; i.
    { split.
      { eapply next_cardinal_le_iff. eapply H. }
      { eapply next_cardinal_le_iff. eapply H. }
    }
    { split.
      { eapply next_cardinal_le_iff. eapply H. }
      { eapply next_cardinal_le_iff. eapply H. }
    }
  Qed.

  Lemma next_cardinal_lt_iff A B:
    Ordinal.lt (cardinal A) (cardinal B) <-> Ordinal.lt (next_cardinal A) (next_cardinal B).
  Proof.
    destruct (total (cardinal B) (cardinal A)).
    { split.
      { i. exfalso. eapply Ordinal.lt_not_le; eauto. }
      { i. eapply next_cardinal_le_iff in H.
        exfalso. eapply Ordinal.lt_not_le; eauto. }
    }
    { split; i; auto. eapply next_cardinal_lt; auto. }
  Qed.

  Lemma same_cardinal_is_cardinal A B (EQ: Ordinal.eq (cardinal A) (cardinal B))
        c (CARDINAL: is_cardinal A c):
    is_cardinal B c.
  Proof.
    eapply cardinal_unique in CARDINAL.
    2: { eapply cardinal_is_cardinal. }
    eapply eq_is_cardinal.
    2: { eapply cardinal_is_cardinal. }
    transitivity (cardinal A); auto. symmetry. auto.
  Qed.

  Lemma cardinal_join_upperbound X (TS: X -> Type):
    is_cardinal (to_total_set (Ordinal.join (fun x => cardinal (TS x)))) (Ordinal.join (fun x => cardinal (TS x))).
  Proof.
    split.
    { exists (to_total_rel (Ordinal.join (fun x : X => cardinal (TS x)))), (to_total_well_founded _). splits.
      - eapply to_total_total.
      - symmetry. eapply to_total_eq. }
    { i. des. eapply Ordinal.join_supremum. i. etransitivity.
      2: { eapply IN0. }
      etransitivity.
      2: { eapply cardinal_lowerbound; auto. }
      transitivity (cardinal (to_total_set (cardinal (TS a)))).
      { eapply cardinal_to_total_bij1. }
      { eapply to_total_le. eapply (Ordinal.join_upperbound (fun x : X => cardinal (TS x))). }
    }
  Qed.

  Lemma is_cardinal_join_upperbound A (os: A -> Ordinal.t)
        (CARD: forall a, is_cardinal (to_total_set (os a)) (os a)):
    is_cardinal (to_total_set (Ordinal.join os)) (Ordinal.join os).
  Proof.
    assert (Ordinal.eq (Ordinal.join (fun x : A => cardinal (to_total_set (os x)))) (Ordinal.join os)).
    { split.
      { eapply Ordinal.join_supremum. i. transitivity (os a).
        { eapply cardinal_to_total_bij2; eauto. }
        { eapply Ordinal.join_upperbound. }
      }
      { eapply Ordinal.join_supremum. i. transitivity (cardinal (to_total_set (os a))).
        { eapply cardinal_to_total_bij2; eauto. }
        { eapply (Ordinal.join_upperbound (fun x : A => cardinal (to_total_set (os x)))). }
      }
    }
    hexploit (cardinal_join_upperbound (fun a => to_total_set (os a))). i.
    eapply same_cardinal_is_cardinal in H0.
    { eapply eq_is_cardinal.
      2: { eapply H0. }
      { auto. }
    }
    { split.
      - eapply to_total_le; apply H.
      - eapply to_total_le; apply H.
    }
  Qed.

  Lemma is_cardinal_size A c (CARDINAL: is_cardinal A c):
    is_cardinal (to_total_set c) c.
  Proof.
    eapply same_cardinal_is_cardinal; eauto.
    etransitivity.
    { eapply cardinal_to_total_bij1. }
    eapply cardinal_unique in CARDINAL.
    2: { eapply cardinal_is_cardinal. }
    split.
    { eapply to_total_le. eapply CARDINAL. }
    { eapply to_total_le. eapply CARDINAL. }
  Qed.

  Section FINITE.
    Fixpoint finite (n: nat): Type :=
      match n with
      | 0 => False
      | Datatypes.S n' => option (finite n')
      end.

    Fixpoint finite_lt (n: nat): finite n -> finite n -> Prop :=
      match n with
      | 0 => fun _ _ => False
      | Datatypes.S n' =>
        fun x y => match x, y with
                   | Some x', Some y' => finite_lt n' x' y'
                   | Some x', None => True
                   | _, _ => False
                   end
      end.

    Lemma finite_total: forall n x0 x1, finite_lt n x0 x1 \/ x0 = x1 \/ finite_lt n x1 x0.
    Proof.
      induction n.
      { i. ss. }
      { i. ss. destruct x0, x1; ss; eauto.
        destruct (IHn f f0) as [|[]]; eauto. subst. auto.
      }
    Qed.

    Lemma finite_lt_acc: forall n x (ACC: Acc (finite_lt n) x), Acc (finite_lt (Datatypes.S n)) (Some x).
    Proof.
      intros n x ACC. induction ACC. econs. i. destruct y; ss.
      eapply H0. auto.
    Qed.

    Lemma finite_well_founded: forall n, well_founded (finite_lt n).
    Proof.
      induction n.
      - ii. econs. i. ss.
      - ii. econs. i. destruct a, y; ss.
        + eapply finite_lt_acc. eapply IHn.
        + eapply finite_lt_acc. eapply IHn.
    Qed.

    Lemma finite_from_acc_eq:
      forall n (x: finite n)
             (ACC0: Acc (finite_lt n) x) (ACC1: Acc (finite_lt (Datatypes.S n)) (Some x)),
        Ordinal.eq (Ordinal.from_acc ACC0) (Ordinal.from_acc ACC1).
    Proof.
      intros n x ACC. dup ACC.
      induction ACC0. i. destruct ACC, ACC1. ss. split.
      { econs. i. destruct a1. exists (exist _ (Some x0) (f)). ss. eapply H0. auto. }
      { econs. i. destruct a1. destruct x0; ss. exists (exist _ f y). ss. eapply H0. auto. }
    Qed.

    Lemma finite_from_wf_eq:
      forall n (x: finite n),
        Ordinal.eq (Ordinal.from_wf (finite_well_founded n) x) (Ordinal.from_wf (finite_well_founded (Datatypes.S n)) (Some x)).
    Proof.
      i. eapply finite_from_acc_eq.
    Qed.

    Lemma finite_from_wf_set_eq:
      forall n,
        Ordinal.eq (Ordinal.from_wf_set (finite_well_founded n)) (Ordinal.from_wf (finite_well_founded (Datatypes.S n)) None).
    Proof.
      i. split.
      { eapply Ordinal.build_spec. i. eapply Ordinal.le_lt_lt.
        { eapply finite_from_wf_eq. }
        { eapply Ordinal.from_wf_lt. ss. }
      }
      { unfold Ordinal.from_wf at 1. destruct (finite_well_founded (Datatypes.S n) None).
        ss. econs. i. destruct a0. ss. destruct x; ss.
        exists f. eapply finite_from_acc_eq.
      }
    Qed.

    Lemma finite_S:
      forall n,
        Ordinal.eq (Ordinal.S (Ordinal.from_wf_set (finite_well_founded n))) (Ordinal.from_wf_set (finite_well_founded (Datatypes.S n))).
    Proof.
      i. split.
      - eapply Ordinal.S_spec. eapply Ordinal.le_lt_lt.
        { eapply finite_from_wf_set_eq. }
        { eapply Ordinal.from_wf_set_upperbound. }
      - econs. i. exists tt. ss. etransitivity.
        2: { eapply finite_from_wf_set_eq. }
        destruct a0.
        { eapply Ordinal.lt_le. eapply Ordinal.from_wf_lt. auto. }
        { reflexivity. }
    Qed.

    Lemma finite_O:
      Ordinal.eq (Ordinal.from_wf_set (finite_well_founded 0)) Ordinal.O.
    Proof.
      split.
      { econs. i. ss. }
      { eapply Ordinal.O_bot. }
    Qed.

    Lemma O_cardinal:
      is_cardinal False Ordinal.O.
    Proof.
      split.
      { exists (fun _ _ => False).
        assert (WF: well_founded (fun _ _: False => False)).
        { ii. ss. }
        exists WF. splits; auto. split.
        { econs. i. ss. }
        { eapply Ordinal.O_bot. }
      }
      { i. eapply Ordinal.O_bot. }
    Qed.

    Lemma O_is_cardinal:
      is_cardinal (to_total_set Ordinal.O) Ordinal.O.
    Proof.
      eapply is_cardinal_size. eapply O_cardinal.
    Qed.

    Lemma finite_cardinal_O:
      is_cardinal (to_total_set (Ordinal.from_wf_set (finite_well_founded 0))) (Ordinal.from_wf_set (finite_well_founded 0)).
    Proof.
      eapply is_cardinal_size. eapply eq_is_cardinal.
      2: { eapply O_cardinal. }
      symmetry. eapply finite_O.
    Qed.

    (* Lemma finite_incr n: Ordinal.lt (cardinal (finite n)) (cardinal (finite (Datatypes.S n))). *)
    (* Admitted. *)
  End FINITE.


  Section ALEPH.

    Lemma aleph_gen_le o0 o1 (LE: Ordinal.le o0 o1):
      Ordinal.le (next_cardinal (to_total_set o0)) (next_cardinal (to_total_set o1)).
    Proof.
      i. eapply next_cardinal_le. eapply to_total_le. apply LE.
    Qed.

    Lemma aleph_gen_eq o0 o1 (EQ: Ordinal.eq o0 o1):
      Ordinal.eq (next_cardinal (to_total_set o0)) (next_cardinal (to_total_set o1)).
    Proof.
      split.
      - eapply aleph_gen_le. apply EQ.
      - eapply aleph_gen_le. apply EQ.
    Qed.

    Lemma aleph_gen_lt o:
      Ordinal.lt o (next_cardinal (to_total_set o)).
    Proof.
      eapply Ordinal.eq_lt_lt.
      { eapply to_total_eq. }
      eapply next_cardinal_upperbound.
      reflexivity.
    Qed.

    Lemma aleph_gen_incr o:
      Ordinal.le o (next_cardinal (to_total_set o)).
    Proof.
      eapply Ordinal.lt_le. eapply aleph_gen_lt.
    Qed.

    Definition aleph_gen (o: Ordinal.t) := next_cardinal (to_total_set o).
    Definition aleph := Ordinal.orec Ordinal.omega aleph_gen.

    Lemma aleph_mon o0 o1 (LE: Ordinal.le o0 o1):
      Ordinal.le (aleph o0) (aleph o1).
    Proof.
      eapply Ordinal.orec_le; auto.
      eapply aleph_gen_le.
    Qed.

    Lemma aleph_le_omega o:
      Ordinal.le Ordinal.omega (aleph o).
    Proof.
      eapply Ordinal.orec_le_base.
      eapply aleph_gen_le.
    Qed.

    Lemma aleph_expand:
      forall o, Ordinal.le o (aleph o).
    Proof.
      i. transitivity (Ordinal.orec Ordinal.O Ordinal.S o).
      { eapply Ordinal.orec_of_S. }
      eapply (@Ordinal.rec_mon _ Ordinal.le Ordinal.join Ordinal.O Ordinal.S Ordinal.omega aleph_gen).
      { eapply Ordinal.O_bot. }
      { i. eapply Ordinal.S_spec. eapply Ordinal.le_lt_lt; eauto.
        eapply aleph_gen_lt.
      }
      { eapply Ordinal.le_PreOrder. }
      { i. eapply Ordinal.join_upperbound. }
      { i. eapply Ordinal.join_supremum. auto. }
    Qed.

    (* Lemma aleph_is_cardinal: *)
    (*   forall o, is_cardinal (to_total_set (aleph o)) (aleph o). *)
    (* Proof. *)
    (*   eapply (rec_wf Ordinal.le join (fun o => is_cardinal (to_total_set o) o) aleph_gen omega); eauto. *)
    (*   { i. reflexivity. } *)
    (*   { i. transitivity d1; auto. } *)
    (*   { i. eapply join_upperbound. } *)
    (*   { i. eapply join_supremum. auto. } *)
    (*   { i. eapply is_cardinal_join_upperbound. auto. } *)
    (*   { admit. } *)
    (*   { i. eapply next_cardinal_is_cardinal. } *)
    (*   { i. eapply aleph_gen_le. } *)
    (*   { i. eapply aleph_gen_eq; auto. } *)
    (* Admitted. *)

  End ALEPH.


  Section INACCESSIBLE.
    Let SmallT: Type := Type.
    Let X := @sig (@sigT SmallT (fun X => X -> X -> Prop))
                  (fun PR => well_founded (projT2 PR)).
    Let Y : X -> Ordinal.t := fun PRWF => Ordinal.from_wf_set (proj2_sig PRWF).

    Definition kappa := @Ordinal.build X Y.

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
          Ordinal.eq (Ordinal.from_wf (WF a) x)
                     (Ordinal.from_wf _union_rel_well_founded (existT _ a (Some x))).
      Proof.
        revert x. eapply (well_founded_induction (WF a)).
        i. split.
        { eapply Ordinal.from_wf_supremum. i. specialize (H _ LT). inv H.
          eapply Ordinal.le_lt_lt; eauto. eapply Ordinal.from_wf_lt. econs; eauto. }
        { eapply Ordinal.from_wf_supremum. i. dependent destruction LT.
          specialize (H _ LT). inv H.
          eapply Ordinal.le_lt_lt; eauto. eapply Ordinal.from_wf_lt. auto. }
      Qed.

      Let _from_wf_set_union:
        Ordinal.eq (@Ordinal.build A (fun a => Ordinal.from_wf_set (WF a)))
                   (Ordinal.from_wf_set _union_rel_well_founded).
      Proof.
        split.
        { econs. i. exists (existT _ a0 None). eapply Ordinal.build_spec. i.
          eapply (@Ordinal.le_lt_lt (Ordinal.from_wf _union_rel_well_founded (existT _ a0 (Some a)))).
          { eapply _from_wf_union. }
          { eapply Ordinal.from_wf_lt. econs. }
        }
        { econs. i. destruct a0 as [a0 [x|]].
          { exists a0. transitivity (Ordinal.from_wf (WF a0) x).
            { eapply _from_wf_union. }
            { eapply Ordinal.lt_le. eapply Ordinal.from_wf_set_upperbound. }
          }
          { exists a0. eapply Ordinal.from_wf_supremum. i.
            dependent destruction LT.
            eapply (@Ordinal.le_lt_lt (Ordinal.from_wf (WF a0) x)).
            { eapply _from_wf_union. }
            { eapply Ordinal.from_wf_set_upperbound. }
          }
        }
      Qed.

      Lemma small_join_small:
        exists (U: SmallT) (RU: U -> U -> Prop) (WFU: well_founded RU),
          forall a, Ordinal.lt (Ordinal.from_wf_set (WF a)) (Ordinal.from_wf_set WFU).
      Proof.
        exists _union_set, _union_rel, _union_rel_well_founded. i.
        eapply Ordinal.lt_eq_lt.
        { symmetry. eapply _from_wf_set_union. }
        eapply (@Ordinal.build_upperbound _ (fun a0 => Ordinal.from_wf_set (WF a0)) a).
      Qed.
    End UNION.

    Lemma kappa_inaccessible_build (A: SmallT) (os: A -> Ordinal.t) (LT: forall a, Ordinal.lt (os a) kappa)
      :
      Ordinal.lt (Ordinal.build os) kappa.
    Proof.
      hexploit (choice (fun (a: A) (XRWF: @sig (@sigT SmallT (fun X => X -> X -> Prop)) (fun XR => well_founded (projT2 XR))) =>
                          Ordinal.le (os a) (Ordinal.from_wf_set (proj2_sig XRWF)))).
      { i. eapply NNPP. ii. eapply Ordinal.lt_not_le.
        { eapply (LT x). }
        eapply Ordinal.build_spec. i. destruct (total (os x) (Y a)); auto.
        exfalso. eapply H. exists a. auto.
      }
      i. des.
      hexploit (@small_join_small A (fun a => projT1 (proj1_sig (f a))) (fun a => projT2 (proj1_sig (f a))) (fun a => proj2_sig (f a))).
      i. des. eapply (@Ordinal.le_lt_lt (Ordinal.from_wf_set WFU)).
      { eapply Ordinal.build_spec; eauto. i. eapply (@Ordinal.le_lt_lt (Ordinal.from_wf_set (proj2_sig (f a)))).
        { eapply H. }
        { eapply H0. }
      }
      eapply (@Ordinal.build_upperbound X Y (exist _ (existT _ U RU) WFU)).
    Qed.

    Lemma kappa_inaccessible_is_join (A: SmallT) (os: A -> Ordinal.t) (LT: forall a, Ordinal.lt (os a) kappa)
          o (JOIN: Ordinal.is_join os o)
      :
      Ordinal.lt o kappa.
    Proof.
      eapply (@Ordinal.le_lt_lt (Ordinal.build os)).
      2: { eapply kappa_inaccessible_build; auto. }
      eapply Ordinal.is_join_supremum; eauto.
      i. eapply Ordinal.lt_le. eapply Ordinal.build_upperbound.
    Qed.

    Lemma kappa_inaccessible_join (A: SmallT) (os: A -> Ordinal.t) (LT: forall a, Ordinal.lt (os a) kappa):
      Ordinal.lt (Ordinal.join os) kappa.
    Proof.
      eapply kappa_inaccessible_is_join; eauto. eapply Ordinal.join_is_join.
    Qed.

    Let D: SmallT := unit.
    Let D_well_founded: @well_founded D (fun _ _ => False).
    Proof.
      ii. econs; ss.
    Qed.

    Lemma kappa_inaccesible_from_acc (A: SmallT) (R: A -> A -> Prop) a (ACC: Acc R a):
      Ordinal.lt (Ordinal.from_acc ACC) kappa.
    Proof.
      dup ACC. revert ACC. induction ACC0. i.
      destruct ACC. ss.
      hexploit (@kappa_inaccessible_build (sig (fun a0 => R a0 x)) (fun a0p : {a0 : A | R a0 x} => Ordinal.from_acc (Ordinal.Ordinal.from_acc_obligation_1 (Acc_intro x a) a0p))); eauto.
      i. destruct a0. ss. eapply H0; eauto.
    Qed.

    Lemma kappa_inaccesible_from_wf (A: SmallT) (R: A -> A -> Prop) (WF: well_founded R) a:
      Ordinal.lt (Ordinal.from_wf WF a) kappa.
    Proof.
      eapply kappa_inaccesible_from_acc.
    Qed.

    Lemma kappa_inaccesible_from_wf_set (A: SmallT) (R: A -> A -> Prop) (WF: well_founded R):
      Ordinal.lt (Ordinal.from_wf_set WF) kappa.
    Proof.
      eapply kappa_inaccessible_build. i. eapply kappa_inaccesible_from_wf.
    Qed.

    Lemma kappa_inaccessible_is_O o (ZERO: Ordinal.is_O o):
      Ordinal.lt o kappa.
    Proof.
      eapply Ordinal.le_lt_lt.
      { eapply ZERO. }
      eapply (@Ordinal.build_upperbound X Y (exist _ (existT _ D (fun _ _ => False)) D_well_founded)).
    Qed.

    Lemma kappa_inaccessible_O:
      Ordinal.lt Ordinal.O kappa.
    Proof.
      eapply kappa_inaccessible_is_O. eapply Ordinal.O_is_O.
    Qed.

    Lemma kappa_inaccessible_is_S o s (SUCC: Ordinal.is_S o s) (LT: Ordinal.lt o kappa):
      Ordinal.lt s kappa.
    Proof.
      eapply (@Ordinal.le_lt_lt (@Ordinal.build D (fun _ => o))).
      { eapply SUCC. eapply (Ordinal.build_upperbound (fun _ : D => o) tt). }
      { eapply kappa_inaccessible_build; eauto. }
    Qed.

    Lemma kappa_inaccessible_S o (LT: Ordinal.lt o kappa):
      Ordinal.lt (Ordinal.S o) kappa.
    Proof.
      eapply kappa_inaccessible_is_S; eauto.
      eapply Ordinal.S_is_S.
    Qed.

    Lemma kappa_complete o (LT: Ordinal.lt o kappa):
      exists (A: SmallT) (R: A -> A -> Prop) (WF: well_founded R),
        Ordinal.le o (Ordinal.from_wf_set WF).
    Proof.
      eapply NNPP. ii. eapply Ordinal.lt_not_le.
      { eapply LT. }
      eapply Ordinal.build_spec. i. destruct a as [[A R] WF]. unfold Y. ss.
      destruct (total o (Ordinal.from_wf_set WF)); auto.
      exfalso. eapply H. esplits; eauto.
    Qed.

    Lemma kappa_incaccessible_nat n: Ordinal.lt (Ordinal.from_nat n) kappa.
    Proof.
      induction n; ss.
      - eapply kappa_inaccessible_O.
      - eapply kappa_inaccessible_S. auto.
    Qed.

    Lemma kappa_incaccessible_omega: Ordinal.lt Ordinal.omega kappa.
    Proof.
      eapply kappa_inaccessible_join.
      eapply kappa_incaccessible_nat.
    Qed.

    Lemma kappa_inaccessible_next_cardinal o (LT: Ordinal.lt o kappa):
      Ordinal.lt (next_cardinal (to_total_set o)) kappa.
    Proof.
      hexploit (kappa_complete LT); eauto. i. des.
      eapply (@Ordinal.le_lt_lt (next_cardinal A)).
      { eapply next_cardinal_le.
        etransitivity.
        { eapply to_total_le. eapply H. }
        eapply from_wf_set_to_total.
      }
      eapply (@Ordinal.le_lt_lt (cardinal (A -> Prop))).
      { eapply next_cardinal_le_power_set. }
      hexploit (cardinal_is_cardinal (A -> Prop)). i. inv H0.
      des. eapply Ordinal.eq_lt_lt.
      { symmetry. eapply H0. }
      eapply (@Ordinal.build_upperbound X Y (exist _ (existT _ (A -> Prop) R0) WF0)).
    Qed.

    Lemma smaller_cardinal_small (A: Type) (B: SmallT)
          (LE: Ordinal.le (cardinal A) (cardinal B))
      :
        exists (A': SmallT),
          Ordinal.eq (cardinal A) (cardinal A').
    Proof.
      eapply _cardinal_le_iff in LE. inv LE.
      set (A' := @sig B (fun b => exists a, f a = b)). exists A'.
      split.
      { eapply _cardinal_le_iff.
        eapply _cardinal_le_intro with (f:=fun a => exist _ (f a) (ex_intro _ a eq_refl)).
        i. inv EQ. eapply INJ; eauto.
      }
      { hexploit (choice (fun (a': A') (a: A) =>
                            f a = proj1_sig a')).
        { i. destruct x. s. eauto. }
        i. des. eapply _cardinal_le_iff.
        eapply _cardinal_le_intro with (f:=f0).
        i. destruct a0, a1. des. subst.
        dup EQ. eapply f_equal with (f:=f) in EQ0.
        rewrite H in EQ0. rewrite H in EQ0. ss.
        eapply INJ in EQ0. subst. auto.
      }
    Qed.

    Lemma small_odinal_small o (LT: Ordinal.lt o kappa):
      exists (A: SmallT), Ordinal.eq (cardinal A) (cardinal (to_total_set o)).
    Proof.
      eapply kappa_complete in LT. des.
      hexploit (@smaller_cardinal_small (to_total_set o) A).
      { etransitivity.
        2: { eapply from_wf_set_to_total. }
        { eapply to_total_le. eauto. }
      }
      i. des. esplits. symmetry. eapply H.
    Qed.

    Lemma sum_of_small o (LT: Ordinal.lt o kappa):
      exists (A: SmallT) (os: A -> Ordinal.t), Ordinal.eq o (Ordinal.build os).
    Proof.
      hexploit small_odinal_small; eauto. i. des.
      hexploit sum_of_smaller_same_cardinal; eauto.
    Qed.

    Lemma kappa_inaccessible_aleph o (LT: Ordinal.lt o kappa):
      Ordinal.lt (aleph o) kappa.
    Proof.
      revert o LT.
      eapply (well_founded_induction
                Ordinal.lt_well_founded
                (fun o => forall (LT: Ordinal.lt o kappa), Ordinal.lt (aleph o) kappa)).
      i. dup LT. eapply sum_of_small in LT. des.
      eapply Ordinal.le_lt_lt.
      { eapply aleph_mon. eapply LT. }
      eapply kappa_inaccessible_join. i. destruct a.
      { eapply kappa_incaccessible_omega. }
      { eapply kappa_inaccessible_join. i.
        eapply kappa_inaccessible_next_cardinal. eapply H; auto.
        { eapply Ordinal.lt_eq_lt.
          { eapply LT. }
          { eapply Ordinal.build_upperbound. }
        }
        { etransitivity.
          { eapply Ordinal.build_upperbound. }
          { eapply Ordinal.eq_lt_lt; eauto. symmetry. eauto. }
        }
      }
    Qed.

    Lemma kappa_aleph_fixpoint:
      Ordinal.eq kappa (aleph kappa).
    Proof.
      split.
      - eapply aleph_expand.
      - eapply Ordinal.orec_build_supremum.
        { eapply Ordinal.lt_le. eapply kappa_incaccessible_omega. }
        { i. eapply Ordinal.lt_le. unfold aleph_gen.
          eapply kappa_inaccessible_next_cardinal.
          eapply kappa_inaccessible_aleph. auto. }
    Qed.
  End INACCESSIBLE.
End ClassicalOrdinal.

Theorem well_ordering_theorem (X: Type)
  :
    exists (R: X -> X -> Prop),
      well_founded R /\
      (forall x0 x1, R x0 x1 \/ x0 = x1 \/ R x1 x0).
Proof.
  eapply ClassicalOrdinal._well_ordering_theorem.
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
    eapply ClassicalOrdinal._zorn_lemma_lt; eauto.
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
    eapply ClassicalOrdinal._zorn_lemma_antisym; eauto.
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
    eapply ClassicalOrdinal._zorn_lemma; eauto.
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
    eapply ClassicalOrdinal._zorn_lemma_weak; eauto.
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

  Definition lt A B: Prop := le A B /\ ~ le B A.

  Lemma lt_le A B (LT: lt A B): le A B.
  Proof.
    eapply LT.
  Qed.

  Lemma lt_le_lt B A C (LT: lt A B) (LE: le B C): lt A C.
  Proof.
    inv LT. split.
    - transitivity B; eauto.
    - ii. inv H1. eapply H0. transitivity C; auto. econs; eauto.
  Qed.

  Lemma le_lt_lt B A C (LE: le A B) (LT: lt B C): lt A C.
  Proof.
    inv LT. split.
    - transitivity B; eauto.
    - ii. inv H1. eapply H0. transitivity A; auto. econs; eauto.
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
      ii. eapply H0. split; auto.
    - des.
      + eapply H.
      + eapply eq_le. auto.
  Qed.

  Lemma total_le A B: le A B \/ le B A.
  Proof.
    hexploit (ClassicalOrdinal.set_comparable A B). i. des.
    - left. econs; eauto.
    - right. econs; eauto.
  Qed.

  Lemma total A B: le A B \/ lt B A.
  Proof.
    destruct (classic (le A B)); auto.
    destruct (total_le A B); auto.
    right. split; auto.
  Qed.

  Lemma trichotomy A B: lt A B \/ eq A B \/ lt B A.
  Proof.
    destruct (total A B); auto. eapply le_eq_or_lt in H. des; auto.
  Qed.

  Section CARDINAL.
    Let le_iff A B: le A B <-> ClassicalOrdinal._cardinal_le A B.
    Proof.
      split; i.
      - inv H. econs; eauto.
      - inv H. econs; eauto.
    Qed.

    Let eq_iff A B: eq A B <-> ClassicalOrdinal._cardinal_le A B /\ ClassicalOrdinal._cardinal_le B A.
    Proof.
      split; i.
      - inv H. split; eapply le_iff; auto.
      - inv H. split; eapply le_iff; auto.
    Qed.

    Let lt_iff A B: lt A B <-> ClassicalOrdinal._cardinal_le A B /\ ~ ClassicalOrdinal._cardinal_le B A.
    Proof.
      split; i.
      - inv H. split.
        + eapply le_iff; auto.
        + erewrite <- le_iff. auto.
      - des. split.
        + eapply le_iff; eauto.
        + erewrite le_iff; eauto.
    Qed.

    Lemma cardinal_upperbound A B (CARD: lt B A)
          (R: B -> B -> Prop) (WF: well_founded R)
      :
        Ordinal.lt (Ordinal.from_wf_set WF) (ClassicalOrdinal.cardinal A).
    Proof.
      eapply ClassicalOrdinal._cardinal_upperbound. eapply lt_iff; auto.
    Qed.

    Lemma cardinal_supremum A c
          (UPPER: forall B (CARD: lt B A)
                         (R: B -> B -> Prop) (WF: well_founded R),
              Ordinal.lt (Ordinal.from_wf_set WF) c)
      :
        Ordinal.le (ClassicalOrdinal.cardinal A) c.
    Proof.
      eapply ClassicalOrdinal._cardinal_supremum. i. eapply UPPER. des. split.
      - inv CARD. econs; eauto.
      - ii. eapply CARD0. inv H. econs; eauto.
    Qed.

    Lemma cardinal_le_iff A B:
      le A B <-> Ordinal.le (ClassicalOrdinal.cardinal A) (ClassicalOrdinal.cardinal B).
    Proof.
      rewrite <- ClassicalOrdinal._cardinal_le_iff. auto.
    Qed.

    Lemma cardinal_eq_iff A B:
      eq A B <-> Ordinal.eq (ClassicalOrdinal.cardinal A) (ClassicalOrdinal.cardinal B).
    Proof.
      rewrite <- ClassicalOrdinal._cardinal_eq_iff. auto.
    Qed.

    Lemma cardinal_lt_iff A B:
      lt A B <-> Ordinal.lt (ClassicalOrdinal.cardinal A) (ClassicalOrdinal.cardinal B).
    Proof.
      rewrite <- ClassicalOrdinal._cardinal_lt_iff. auto.
    Qed.
  End CARDINAL.

  Lemma cardinal_to_total_bij A:
    eq A (ClassicalOrdinal.to_total_set (ClassicalOrdinal.cardinal A)).
  Proof.
    eapply cardinal_eq_iff.
    eapply ClassicalOrdinal.cardinal_to_total_bij1.
  Qed.

  Lemma lt_well_founded: well_founded lt.
  Proof.
    assert (forall (o: Ordinal.t) A (EQ: Ordinal.eq o (ClassicalOrdinal.cardinal A)), Acc lt A).
    { eapply (well_founded_induction Ordinal.lt_well_founded (fun o => forall A (EQ: Ordinal.eq o (ClassicalOrdinal.cardinal A)), Acc lt A)).
      i. econs. i. eapply cardinal_lt_iff in H0.
      eapply H.
      { eapply Ordinal.lt_eq_lt.
        { eapply EQ. }
        { eapply H0. }
      }
      { reflexivity. }
    }
    ii. eapply (H (ClassicalOrdinal.cardinal a)). reflexivity.
  Qed.

  Lemma cantor A: lt A (A -> Prop).
  Proof.
    eapply cardinal_lt_iff.
    eapply (@Ordinal.lt_le_lt (ClassicalOrdinal.next_cardinal A)).
    { eapply ClassicalOrdinal.next_cardinal_incr. }
    { eapply ClassicalOrdinal.next_cardinal_le_power_set. }
  Qed.

  Definition O := False.
  Lemma O_bot A: le O A.
  Proof.
    eapply le_intro with (f:=False_rect _).
    i. ss.
  Qed.

  Definition S A:= ClassicalOrdinal.to_total_set (ClassicalOrdinal.next_cardinal A).
  Lemma S_lt A: lt A (S A).
  Proof.
    eapply cardinal_lt_iff. unfold S.
    eapply Ordinal.lt_eq_lt.
    { symmetry. eapply ClassicalOrdinal.cardinal_to_total_bij2.
      eapply ClassicalOrdinal.next_cardinal_is_cardinal. }
    { eapply ClassicalOrdinal.next_cardinal_incr. }
  Qed.
  Lemma S_supremum A B (LT: lt A B): le (S A) B.
  Proof.
    eapply cardinal_lt_iff in LT.
    eapply ClassicalOrdinal.next_cardinal_supremum in LT.
    eapply cardinal_le_iff. transitivity (ClassicalOrdinal.next_cardinal A); auto.
    unfold S. eapply ClassicalOrdinal.to_total_cardinal_le.
  Qed.

  Definition join X (TS: X -> Type):=
    ClassicalOrdinal.to_total_set (@Ordinal.join X (fun x => ClassicalOrdinal.cardinal (TS x))).

  Definition continnum_hypothesis_on A: Prop := eq (S A) (A -> Prop).
End Cardinal.


Section FIXPOINT.
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

  Let k := ClassicalOrdinal.next_cardinal D.

  Theorem fixpoint_theorem:
    dle (next (Ordinal.rec base next djoin k)) (Ordinal.rec base next djoin k).
  Proof.
    eapply (ClassicalOrdinal._fixpoint_theorem base next djoin dle wf); eauto.
  Qed.
End FIXPOINT.


Section KLEENE.
  Variable A: Type.
  Let kappa := ClassicalOrdinal.next_cardinal (A -> Prop).
  Let le: (A -> Prop) -> (A -> Prop) -> Prop :=
    fun P0 P1 => forall a (IN0: P0 a), P1 a.
  Let ge: (A -> Prop) -> (A -> Prop) -> Prop :=
    fun P0 P1 => forall a (IN0: P1 a), P0 a.
  Let join (X: Type) (Ps: X -> A -> Prop): A -> Prop :=
    fun a => exists x, Ps x a.
  Let meet (X: Type) (Ps: X -> A -> Prop): A -> Prop :=
    fun a => forall x, Ps x a.
  Let bot: A -> Prop := fun _ => False.
  Let top: A -> Prop := fun _ => True.

  Variable f: (A -> Prop) -> (A -> Prop).
  Hypothesis mon: forall (P0 P1: A -> Prop) (LE: le P0 P1), le (f P0) (f P1).

  Let mon_rev: forall (P0 P1: A -> Prop) (LE: ge P0 P1), ge (f P0) (f P1).
  Proof.
    ii. eapply mon; eauto.
  Qed.

  Definition mu := Ordinal.rec bot f join kappa.
  Definition nu := Ordinal.rec top f meet kappa.

  Theorem mu_fixpoint:
    le mu (f mu) /\ le (f mu) mu.
  Proof.
    split.
    { hexploit (ClassicalOrdinal.rec_wf bot f join le (fun P => le P (f P))); eauto.
      { ii. ss. }
      { ii. eapply LE1; eauto. }
      { ii. exists a. auto. }
      { ii. inv IN0. eapply LE; eauto. }
      { ii. inv IN0. eapply WF in H.
        eapply mon; eauto. ii. exists x. auto. }
      { ii. ss. }
      { ii. des. split; apply mon; auto. }
    }
    { hexploit (fixpoint_theorem bot f join le (fun P => le P (f P))); eauto.
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
    eapply (ClassicalOrdinal.rec_wf bot f join le (fun P0 => le P0 (f P0) /\ le P0 P)); eauto.
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
    { hexploit (fixpoint_theorem top f meet ge (fun P => le (f P) P)); eauto.
      { ii. ss. }
      { ii. eapply LE0; eauto. }
      { ii. eapply IN0; eauto. }
      { ii. eapply LE. auto. }
      { ii. eapply WF. eapply mon_rev in IN0; eauto.
        ii. eapply IN1; auto. }
      { ii. ss. }
      { ii. des. split; apply mon_rev; auto. }
    }
    { hexploit (ClassicalOrdinal.rec_wf top f meet ge (fun P => le (f P) P)); eauto.
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
    eapply (ClassicalOrdinal.rec_wf top f meet ge (fun P0 => le (f P0) P0 /\ le P P0)); eauto.
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
End KLEENE.
