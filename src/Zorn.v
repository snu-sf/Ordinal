From Ordinal Require Import sflib Basics ClassicalOrdinal Fixedpoint.
From Ordinal Require Export Ordinal.

Require Import Coq.Classes.RelationClasses.
Require Import ClassicalChoice FunctionalExtensionality PropExtensionality.

Set Implicit Arguments.
Set Primitive Projections.

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
      hexploit (fixpoint_theorem_le base next chain_join chain_le wf); auto.
      i. inv H.
      hexploit (H0 (f (Ord.rec base next chain_join (Ord.hartogs chain)))); auto.
      { right. auto. }
      i. eapply (@antisym (f (Ord.rec base next chain_join (Ord.hartogs chain))) (f (Ord.rec base next chain_join (Ord.hartogs chain)))).
      { eapply INCR; auto.
        eapply (ClassicOrd.rec_wf base next chain_join chain_le wf); auto. }
      { eapply INCR; auto.
        eapply (ClassicOrd.rec_wf base next chain_join chain_le wf); auto. }
    Qed.
  End INCR.

  Hypothesis transitive: forall b0 b1 b2 (LT0: R b0 b1) (LT1: R b1 b2), R b0 b2.

  Hypothesis upperbound_exists:
    forall (c: B -> Prop) (CHAIN: forall b0 b1 (IN0: c b0) (IN1: c b1), R b0 b1 \/ b0 = b1 \/ R b1 b0),
    exists b_u, forall b (IN: c b), R b b_u \/ b = b_u.

  Theorem zorn_lemma_lt:
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
    i. des. eapply eventually_maximal; eauto.
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

  Lemma zorn_lemma_antisym:
    exists b_m, forall b (LE: R b_m b), b = b_m.
  Proof.
    hexploit (@zorn_lemma_lt B (fun b0 b1 => R b0 b1 /\ b0 <> b1)).
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
      destruct y. ss. des. eapply (a2 x1 a0); eauto.
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

  Theorem zorn_lemma:
    exists b_m, forall b (LE: R b_m b), R b b_m.
  Proof.
    hexploit (@zorn_lemma_antisym _ equiv_class_rel); eauto. i. des.
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

  Theorem zorn_lemma_weak:
    exists b_m, forall b (LE: R b_m b), R b b_m.
  Proof.
    eapply zorn_lemma; eauto. i. destruct (classic (exists b, c b)).
    { eapply upperbound_exists; eauto. }
    { dup INHABITED. inv INHABITED. exists X. i. exfalso. eapply H; eauto. }
  Qed.
End ZORNWEAK.
