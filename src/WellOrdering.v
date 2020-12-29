From Ordinal Require Import sflib Basics ClassicalOrdinal Fixedpoint.
From Ordinal Require Export Ordinal.

Require Import ClassicalChoice FunctionalExtensionality PropExtensionality.

Set Implicit Arguments.
Set Primitive Projections.

Lemma from_wf_set_embed A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
      (WFA: well_founded RA) (WFB: well_founded RB)
      (LE: Ord.le (Ord.from_wf_set WFA) (Ord.from_wf_set WFB))
      (TOTALB: forall b0 b1, RB b0 b1 \/ b0 = b1 \/ RB b1 b0)
  :
    exists (f: A -> B), forall a0 a1 (LT: RA a0 a1), RB (f a0) (f a1).
Proof.
  exploit (choice (fun a b => Ord.eq (Ord.from_wf WFA a) (Ord.from_wf WFB b))).
  { intros a. eapply ClassicOrd.from_wf_set_complete.
    eapply Ord.lt_le_lt; eauto. eapply Ord.from_wf_set_upperbound. }
  i. des. exists f. i. eapply Ord.from_wf_lt with (WF:=WFA) in LT.
  assert (Ord.lt (Ord.from_wf WFB (f a0)) (Ord.from_wf WFB (f a1))).
  { eapply (@Ord.le_lt_lt (Ord.from_wf WFA a0)); eauto.
    - eapply x0.
    - eapply (@Ord.lt_le_lt (Ord.from_wf WFA a1)); auto. eapply x0. }
  destruct (TOTALB (f a0) (f a1)) as [|[]].
  - auto.
  - rewrite H0 in *. eapply Ord.lt_not_le in H; ss. reflexivity.
  - eapply Ord.from_wf_lt with (WF:=WFB) in H0; eauto.
    exfalso. eapply Ord.lt_not_le in H; ss. eapply Ord.lt_le; auto.
Qed.

Section WO.
  Variable X: Type.

  Let subX: Type := (X -> Prop) * (X -> X -> Prop).
  Let subX_mk := @pair (X -> Prop) (X -> X -> Prop).
  Let P := @fst (X -> Prop) (X -> X -> Prop).
  Let R := @snd (X -> Prop) (X -> X -> Prop).

  Let subX_wf (X': subX): Prop :=
    (forall a0 a1 (LT: R X' a0 a1), P X' a0 /\ P X' a1) /\
    (forall a0 a1 (IN0: P X' a0) (IN1: P X' a1),
        R X' a0 a1 \/ a0 = a1 \/ R X' a1 a0) /\
    (well_founded (R X'))
  .

  Let subX_wf_intro X'
        (SOUND: forall a0 a1 (LT: R X' a0 a1), P X' a0 /\ P X' a1)
        (COMPLETE: forall a0 a1 (IN0: P X' a0) (IN1: P X' a1),
            R X' a0 a1 \/ a0 = a1 \/ R X' a1 a0)
        (WFO: well_founded (R X'))
    :
      subX_wf X'.
  Proof.
    split; auto.
  Qed.

  Let subX_sound X' (WF: subX_wf X'):
    forall a0 a1 (LT: R X' a0 a1), P X' a0 /\ P X' a1.
  Proof.
    apply WF.
  Qed.

  Let subX_complete X' (WF: subX_wf X'):
    forall a0 a1 (IN0: P X' a0) (IN1: P X' a1),
      R X' a0 a1 \/ a0 = a1 \/ R X' a1 a0.
  Proof.
    apply WF.
  Qed.

  Let subX_wfo X' (WF: subX_wf X'):
    well_founded (R X').
  Proof.
    apply WF.
  Qed.

  Variable x_bot: X.

  Let wfX := subX_wf.
  Let sound := subX_sound.
  Let complete := subX_complete.
  Let wfo := subX_wfo.

  Let leX (s0 s1: subX): Prop :=
    (forall a (IN: P s0 a), P s1 a) /\
    (forall a0 a1 (LT: R s0 a0 a1), R s1 a0 a1) /\
    (forall a0 a1 (IN: P s0 a1), R s1 a0 a1 <-> R s0 a0 a1).

  Let leX_intro s0 s1
      (_P_incl: forall a (IN: P s0 a), P s1 a)
      (_R_incl: forall a0 a1 (LT: R s0 a0 a1), R s1 a0 a1)
      (_no_insert: forall a0 a1 (IN: P s0 a1), R s1 a0 a1 <-> R s0 a0 a1)
    :
      leX s0 s1.
  Proof.
    split; auto.
  Qed.

  Let P_incl s0 s1 (LE: leX s0 s1):
    forall a (IN: P s0 a), P s1 a.
  Proof.
    apply LE.
  Qed.

  Let R_incl s0 s1 (LE: leX s0 s1):
    forall a0 a1 (LT: R s0 a0 a1), R s1 a0 a1.
  Proof.
    apply LE.
  Qed.

  Let no_insert s0 s1 (LE: leX s0 s1):
    forall a0 a1 (IN: P s0 a1), R s1 a0 a1 <-> R s0 a0 a1.
  Proof.
    apply LE.
  Qed.

  Let joinX A (Xs: A -> subX): subX :=
    subX_mk (fun x => exists a, P (Xs a) x) (fun x0 x1 => exists a, R (Xs a) x0 x1).

  Let base: subX := subX_mk (fun x => x = x_bot) (fun _ _ => False).

  Let leX_reflexive: forall d (WF: wfX d), leX d d.
  Proof.
    i. apply leX_intro; ss.
  Qed.

  Let leX_transitive: forall d1 d0 d2 (WF0: wfX d0) (WF1: wfX d1) (WF2: wfX d2) (LE0: leX d0 d1) (LE1: leX d1 d2),
      leX d0 d2.
  Proof.
    i. unfold leX in *. des. splits; auto.
    i. rewrite <- LE5; auto.
  Qed.

  Let joinX_upperbound: forall A (ds: A -> subX) (a: A) (CHAIN: forall a0 a1, leX (ds a0) (ds a1) \/ leX (ds a1) (ds a0)) (WF: forall a, wfX (ds a)), leX (ds a) (joinX ds).
  Proof.
    i. apply leX_intro; ss; eauto. i. split; i.
    - des. destruct (CHAIN a a2).
      + eapply H0 in H; eauto.
      + eapply (R_incl H0). eauto.
    - eauto.
  Qed.

  Let joinX_supremum: forall A (ds: A -> subX) (d: subX) (CHAIN: forall a0 a1, leX (ds a0) (ds a1) \/ leX (ds a1) (ds a0)) (WF: forall a, wfX (ds a)) (WFD: wfX d) (LE: forall a, leX (ds a) d), leX (joinX ds) d.
  Proof.
    i. apply leX_intro; ss.
    - i. des. eapply (P_incl (LE a0)) in IN. auto.
    - i. des. eapply (R_incl (LE a)) in LT. auto.
    - i. des. split; i.
      + eapply LE in H; eauto.
      + des. eapply (R_incl (LE a2)); eauto.
  Qed.

  Let joinX_wf: forall A (ds: A -> subX) (CHAIN: forall a0 a1, leX (ds a0) (ds a1) \/ leX (ds a1) (ds a0)) (WF: forall a, wfX (ds a)), wfX (joinX ds).
  Proof.
    i. apply subX_wf_intro; ss.
    - i. des. eapply (subX_sound (WF a)) in LT. des. eauto.
    - i. des. destruct (CHAIN a2 a).
      + eapply (P_incl H) in IN0. hexploit (complete (WF a) a0 a1); eauto.
        i. des; eauto.
      + eapply (P_incl H) in IN1. hexploit (complete (WF a2) a0 a1); eauto.
        i. des; eauto.
    - intros x1. econs. intros x0. ss. i. des.
      assert (ACC: Acc (R (ds a)) x0).
      { eapply WF. }
      eapply (subX_sound (WF a)) in H. des. clear H0.
      revert H. induction ACC. i.
      econs. i. des.
      assert (LT: R (ds a) y x).
      { destruct (CHAIN a a0).
        - eapply H3 in H2; auto.
        - eapply (R_incl H3) in H2; auto.
      }
      eapply H0; eauto. eapply (subX_sound (WF a)) in LT. des. auto.
  Qed.

  Let base_wf: wfX base.
  Proof.
    eapply subX_wf_intro; ss.
    i. subst. auto.
  Qed.

  Section NEXT.
    Hypothesis next: subX -> subX.

    Hypothesis next_wf: forall d (WF: wfX d), wfX (next d).
    Hypothesis next_le: forall d (WF: wfX d), leX d (next d).
    Hypothesis next_exhausted: forall d (WF: wfX d),
        (forall x, P d x) \/
        (exists x, P (next d) x /\ ~ P d x)
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
          + eapply (R_incl EQ).
          + eapply (R_incl EQ0).
      }
      subst. split; auto.
    Qed.

    Let eventually_exhausted
      :
        exists o, forall x, P (Ord.rec base next joinX o) x.
    Proof.
      hexploit (fixpoint_theorem base next joinX leX wfX); auto. i.
      exists (Ord.hartogs subX).
      hexploit next_exhausted.
      { eapply (ClassicOrd.rec_wf base next joinX leX wfX); eauto. }
      i. des; eauto. exfalso. eapply H2. eapply H. auto.
    Qed.

    Lemma _choice_then_well_ordering_theorem
      :
        exists (R: X -> X -> Prop),
          well_founded R /\
          (forall x0 x1, R x0 x1 \/ x0 = x1 \/ R x1 x0).
    Proof.
      hexploit eventually_exhausted. i. des.
      assert (WF: wfX (Ord.rec base next joinX o)).
      { hexploit (@ClassicOrd.rec_wf _ base next joinX leX wfX); eauto. }
      exists (R (Ord.rec base next joinX o)). splits; auto.
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
                   (forall x, P d x) \/
                   (exists x, P (next d) x /\ ~ P d x))).
    { hexploit (choice (fun d0 d1 =>
                          forall (WF: wfX d0),
                            wfX d1 /\ leX d0 d1 /\
                            ((forall x, P d0 x) \/ (exists x, P d1 x /\ ~ P d0 x)))).
      { intros d0. destruct (classic (forall x, P d0 x)).
        { exists d0. i. split; auto. }
        eapply not_all_ex_not in H. des.
        exists (subX_mk (fun x => P d0 x \/ x = n) (fun x0 x1 => R d0 x0 x1 \/ (P d0 x0 /\ x1 = n))).
        i. splits.
        - eapply subX_wf_intro; ss.
          + i. des; clarify; splits; auto.
            * left. eapply (subX_sound WF) in LT. des; eauto.
            * left. eapply (subX_sound WF) in LT. des; eauto.
          + i. des; clarify; eauto.
            destruct (complete WF a0 a1) as [|[|]]; auto.
          + assert (forall x, Acc (R d0) x -> P d0 x -> Acc (fun x0 x1 : X => R d0 x0 x1 \/ P d0 x0 /\ x1 = n) x).
            { i. revert H1. induction H0. econs. i. des; clarify.
              eapply H1; eauto. eapply (subX_sound WF) in H3. des; eauto. }
            econs. i. des; clarify.
            * eapply H0.
              { eapply WF. }
              { eapply (subX_sound WF) in H1. des; auto. }
            * eapply H0; eauto. eapply WF.
        - apply leX_intro; ss; auto. i. split; i; auto. des; clarify.
        - i. right. ss. eauto.
      }
      i. des. exists f. splits; i; try apply H; eauto.
    }
    des. eapply _choice_then_well_ordering_theorem; eauto.
  Qed.
End WO.

Theorem well_ordering_theorem (X: Type)
  :
    exists (R: X -> X -> Prop),
      well_founded R /\
      (forall x0 x1, R x0 x1 \/ x0 = x1 \/ R x1 x0).
Proof.
  destruct (classic (inhabited X)) as [[x]|].
  { eapply inhabited_well_ordering_theorem; auto. }
  { exists (fun _ _ => False). econs; i; ss. exfalso. eapply H; eauto. }
Qed.


Section EXTEND.
  Variable A: Type.
  Variable RT: A -> A -> Prop.
  Variable WFT: well_founded RT.
  Hypothesis TOTAL: forall a0 a1, RT a0 a1 \/ a0 = a1 \/ RT a1 a0.

  Variable R: A -> A -> Prop.
  Variable WF: well_founded R.

  Definition extended_order (a0 a1: A): Prop :=
    Ord.lt (Ord.from_wf WF a0) (Ord.from_wf WF a1) \/
    (Ord.eq (Ord.from_wf WF a0) (Ord.from_wf WF a1) /\ RT a0 a1)
  .

  Lemma extended_order_total:
    forall a0 a1, extended_order a0 a1 \/ a0 = a1 \/ extended_order a1 a0.
  Proof.
    i. destruct (ClassicOrd.trichotomy (Ord.from_wf WF a0) (Ord.from_wf WF a1)) as [|[]].
    - left. left. auto.
    - destruct (@TOTAL a0 a1) as [|[]]; auto.
      + left. right. auto.
      + right. right. right. split; auto. symmetry. auto.
    - right. right. left. auto.
  Qed.

  Lemma extended_order_well_founded: well_founded extended_order.
  Proof.
    ii. hexploit (well_founded_induction
                    Ord.lt_well_founded
                    (fun o => forall a (LE: Ord.le (Ord.from_wf WF a) o), Acc extended_order a)); eauto.
    { clear a. intros o IH.
      assert (LTS: forall a (LT: Ord.lt (Ord.from_wf WF a) o), Acc extended_order a).
      { i. econs. i.
        hexploit (IH _ LT).
        { reflexivity. }
        i. inv H0. eauto.
      }
      i. eapply ClassicOrd.le_eq_or_lt in LE. des; auto.
      eapply (well_founded_induction
                WFT (fun a => Ord.eq (Ord.from_wf WF a) o -> Acc extended_order a)); eauto.
      clear a LE. i. econs. i. inv H1.
      { eapply (IH (Ord.from_wf WF y)).
        { eapply Ord.lt_eq_lt; eauto. symmetry. auto. }
        { reflexivity. }
      }
      { des. eapply H; eauto. transitivity (Ord.from_wf WF x); auto. }
    }
    { eapply Ord.lt_le. eapply Ord.from_wf_set_upperbound. }
  Qed.

  Lemma extended_order_incl:
    forall a0 a1 (LT: R a0 a1), extended_order a0 a1.
  Proof.
    i. left. eapply Ord.from_wf_lt; auto.
  Qed.
End EXTEND.

Lemma well_founded_order_extendable
        A (R0: A -> A -> Prop) (WF: well_founded R0):
  exists R1,
    well_founded R1 /\
    (forall a0 a1 (LT: R0 a0 a1), R1 a0 a1) /\
    (forall a0 a1, R1 a0 a1 \/ a0 = a1 \/ R1 a1 a0).
Proof.
  hexploit (well_ordering_theorem A); eauto. i. des.
  exists (extended_order R WF). splits.
  - eapply extended_order_well_founded; eauto.
  - eapply extended_order_incl; eauto.
  - eapply extended_order_total; eauto.
Qed.

Lemma wf_set_comparable A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
      (WFA: well_founded RA) (WFB: well_founded RB)
      (TOTALA: forall a0 a1, RA a0 a1 \/ a0 = a1 \/ RA a1 a0)
      (TOTALB: forall b0 b1, RB b0 b1 \/ b0 = b1 \/ RB b1 b0)
  :
    (exists (f: A -> B), forall a0 a1 (LT: RA a0 a1), RB (f a0) (f a1)) \/
    (exists (f: B -> A), forall b0 b1 (LT: RB b0 b1), RA (f b0) (f b1)).
Proof.
  destruct (ClassicOrd.total_le (Ord.from_wf_set WFA) (Ord.from_wf_set WFB)).
  - left. eapply from_wf_set_embed; eauto.
  - right. eapply from_wf_set_embed; eauto.
Qed.

Lemma set_comparable A B
  :
    (exists (f: A -> B), forall a0 a1 (EQ: f a0 = f a1), a0 = a1) \/
    (exists (f: B -> A), forall b0 b1 (EQ: f b0 = f b1), b0 = b1).
Proof.
  hexploit (@well_ordering_theorem A); eauto. i. des.
  hexploit (@well_ordering_theorem B); eauto. i. des.
  hexploit (wf_set_comparable H H1); eauto. i. des.
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
