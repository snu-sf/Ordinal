From Ordinal Require Import sflib Basics.
From Ordinal Require Import ClassicalOrdinal WfRel WellOrdering.
From Ordinal Require Export Ordinal.

Require Import Coq.Classes.RelationClasses.
Require Import ClassicalChoice FunctionalExtensionality PropExtensionality.
Require Import Program.

Set Implicit Arguments.
Set Primitive Projections.

Module ToSet.
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

  Lemma from_wf_union (A: Type) (Ts: A -> Type)
        (R: forall a, Ts a -> Ts a -> Prop)
        (WF: forall a, well_founded (R a))
        (a: A) (x: Ts a)
    :
      Ord.eq (Ord.from_wf (WF a) x)
             (Ord.from_wf (union_rel_well_founded R WF) (existT _ a (Some x))).
  Proof.
    revert x. eapply (well_founded_induction (WF a)).
    i. split.
    { eapply Ord.from_wf_supremum. i. specialize (H _ LT). inv H.
      eapply Ord.le_lt_lt; eauto. eapply Ord.from_wf_lt. econs; eauto. }
    { eapply Ord.from_wf_supremum. i. dependent destruction LT.
      specialize (H _ LT). inv H.
      eapply Ord.le_lt_lt; eauto. eapply Ord.from_wf_lt. auto. }
  Qed.

  (* TODO: axiom K necessary? *)
  Lemma from_wf_set_union (A: Type) (Ts: A -> Type)
        (R: forall a, Ts a -> Ts a -> Prop)
        (WF: forall a, well_founded (R a))
    :
      Ord.eq (@Ord.build A (fun a => Ord.from_wf_set (WF a)))
             (Ord.from_wf_set (union_rel_well_founded R WF)).
  Proof.
    split.
    { econs. i. exists (existT _ a0 None). eapply Ord.build_spec. i.
      eapply (@Ord.le_lt_lt (Ord.from_wf (union_rel_well_founded R WF) (existT _ a0 (Some a)))).
      { eapply from_wf_union. }
      { eapply Ord.from_wf_lt. econs. }
    }
    { econs. i. destruct a0 as [a0 [x|]].
      { exists a0. transitivity (Ord.from_wf (WF a0) x).
        { eapply from_wf_union. }
        { eapply Ord.lt_le. eapply Ord.from_wf_set_upperbound. }
      }
      { exists a0. eapply Ord.from_wf_supremum. i.
        dependent destruction LT.
        eapply (@Ord.le_lt_lt (Ord.from_wf (WF a0) x)).
        { eapply from_wf_union. }
        { eapply Ord.from_wf_set_upperbound. }
      }
    }
  Qed.

  Fixpoint to_set (o: Ord.t): @sigT Type (fun A => A -> A -> Prop) :=
    match o with
    | @Ord.build A os => existT
                           _
                           (union_set (fun a => projT1 (to_set (os a))))
                           (union_rel (fun a => projT2 (to_set (os a))))
    end.

  Lemma to_set_well_founded: forall o, well_founded (projT2 (to_set o)).
  Proof.
    induction o. ss. eapply union_rel_well_founded; auto.
  Defined.

  Lemma to_set_eq o:
    Ord.eq o (Ord.from_wf_set (to_set_well_founded o)).
  Proof.
    induction o. etransitivity.
    2: { eapply from_wf_set_union. }
    split.
    { econs. i. exists a0. eapply H. }
    { econs. i. exists a0. eapply H. }
  Qed.

  Lemma to_total_exists (o: Ord.t):
    exists (A: Type) (R: A -> A -> Prop) (WF: well_founded R),
      Ord.eq o (Ord.from_wf_set WF) /\
      (forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0).
  Proof.
    hexploit (to_set_eq o). intros EQ.
    hexploit (well_founded_order_extendable (to_set_well_founded o)). i. des.
    assert (Ord.le o (Ord.from_wf_set H)).
    { transitivity (Ord.from_wf_set (to_set_well_founded o)); auto.
      { eapply EQ. }
      { eapply from_wf_set_le; auto. }
    }
    eapply ClassicOrd.le_eq_or_lt in H2. des.
    { eapply ClassicOrd.from_wf_set_complete in H2. des.
      hexploit (from_wf_set_cut H H1 a). i.
      eexists _, _, (cut_rel_well_founded H a). splits.
      { transitivity (Ord.from_wf H a); auto. }
      { eapply cut_rel_total; eauto. }
    }
    { esplits; eauto. }
  Qed.

  Section TOTALIFY.
    Variable A: Type.
    Variable R: A -> A -> Prop.
    Hypothesis WF: well_founded R.

    Definition equiv_class: Type :=
      @sig (A -> Prop) (fun s => (exists a, s a) /\
                                 (forall a0 a1 (IN0: s a0), s a1 <-> Ord.eq (Ord.from_wf WF a0) (Ord.from_wf WF a1))).

    Program Definition to_equiv_class (a0: A): equiv_class :=
      exist _ (fun a1 => Ord.eq (Ord.from_wf WF a0) (Ord.from_wf WF a1)) _.
    Next Obligation.
      split.
      { exists a0. reflexivity. }
      { i. split; i.
        - transitivity (Ord.from_wf WF a0); eauto. symmetry. auto.
        - transitivity (Ord.from_wf WF a1); eauto.
      }
    Qed.

    Let to_equiv_class_equiv a (s: equiv_class) (IN: proj1_sig s a):
      s = to_equiv_class a.
    Proof.
      destruct s. ss. unfold to_equiv_class.
      assert (x = (fun a1 : A => Ord.eq (Ord.from_wf WF a) (Ord.from_wf WF a1))).
      { extensionality a1. eapply propositional_extensionality. des. split.
        { i. eapply a2; eauto. }
        { i. eapply a2; eauto. }
      }
      subst. f_equal. eapply proof_irrelevance.
    Qed.

    Definition equiv_class_rel: equiv_class -> equiv_class -> Prop :=
      fun s0 s1 => exists a0 a1, (proj1_sig s0) a0 /\ (proj1_sig s1) a1 /\ Ord.lt (Ord.from_wf WF a0) (Ord.from_wf WF a1).

    Lemma to_equiv_class_preserve a0 a1 (LT: R a0 a1):
      equiv_class_rel (to_equiv_class a0) (to_equiv_class a1).
    Proof.
      exists a0, a1. ss. splits.
      - reflexivity.
      - reflexivity.
      - eapply Ord.from_wf_lt; auto.
    Qed.

    Lemma equiv_class_total:
      forall s0 s1, equiv_class_rel s0 s1 \/ s0 = s1 \/ equiv_class_rel s1 s0.
    Proof.
      i. hexploit (proj2_sig s0). i. des. hexploit (proj2_sig s1). i. des.
      destruct (ClassicOrd.trichotomy (Ord.from_wf WF a) (Ord.from_wf WF a0)) as [|[]].
      - left. unfold equiv_class_rel. esplits; eauto.
      - right. left. assert (proj1_sig s0 = proj1_sig s1).
        { extensionality x. eapply propositional_extensionality. split; i.
          - eapply H2; eauto. transitivity (Ord.from_wf WF a); eauto.
            + symmetry. auto.
            + eapply (H0 a x); auto.
          - eapply H0; eauto. transitivity (Ord.from_wf WF a0); eauto.
            eapply (H2 a0 x); auto.
        }
        destruct s0, s1. ss. subst. f_equal. eapply proof_irrelevance.
      - right. right. unfold equiv_class_rel. esplits; eauto.
    Qed.

    Lemma equiv_class_well_founded: well_founded equiv_class_rel.
    Proof.
      assert (forall (o: Ord.t), forall (s: equiv_class) a0 (IN: proj1_sig s a0) (LT: Ord.lt (Ord.from_wf WF a0) o), Acc equiv_class_rel s).
      { eapply (well_founded_induction Ord.lt_well_founded (fun o => forall (s: equiv_class) a0 (IN: proj1_sig s a0) (LT: Ord.lt (Ord.from_wf WF a0) o), Acc equiv_class_rel s)).
        i. econs. i. unfold equiv_class_rel in H0. des.
        hexploit (proj2 (proj2_sig s) a0 a2); auto. i. dup H1.
        eapply H3 in H4. clear H3. eapply (H (Ord.from_wf WF a0)); eauto.
        eapply Ord.lt_eq_lt; eauto.
      }
      ii. hexploit (proj2_sig a); eauto. i. des.
      hexploit (H (Ord.S (Ord.from_wf WF a0))); eauto. eapply Ord.S_lt.
    Qed.

    Lemma to_equiv_class_eq a:
      Ord.eq (Ord.from_wf WF a) (Ord.from_wf equiv_class_well_founded (to_equiv_class a)).
    Proof.
      assert (forall (o: Ord.t), forall a (LT: Ord.lt (Ord.from_wf WF a) o), Ord.eq (Ord.from_wf WF a) (Ord.from_wf equiv_class_well_founded (to_equiv_class a))).
      { eapply (well_founded_induction Ord.lt_well_founded (fun o => forall a (LT: Ord.lt (Ord.from_wf WF a) o), Ord.eq (Ord.from_wf WF a) (Ord.from_wf equiv_class_well_founded (to_equiv_class a)))).
        i. split.
        { eapply Ord.from_wf_supremum. i. dup LT0. eapply (Ord.from_wf_lt WF) in LT0; eauto.
          hexploit H; eauto. i. eapply Ord.le_lt_lt; [eapply H0|].
          eapply Ord.from_wf_lt. eapply to_equiv_class_preserve. auto.
        }
        { eapply Ord.from_wf_supremum. i. unfold equiv_class_rel in LT0. des. ss.
          hexploit (H _ LT a2).
          { eapply Ord.lt_eq_lt; eauto. } i.
          eapply Ord.lt_eq_lt; eauto. eapply Ord.le_lt_lt; eauto.
          etransitivity; [|eapply H0].
          eapply to_equiv_class_equiv in LT0. subst. reflexivity.
        }
      }
      eapply (H (Ord.S (Ord.from_wf WF a))). eapply Ord.S_lt.
    Qed.

    Lemma from_wf_set_equiv_class:
      Ord.eq (Ord.from_wf_set WF) (Ord.from_wf_set equiv_class_well_founded).
    Proof.
      split.
      { eapply Ord.build_spec. i. eapply Ord.eq_lt_lt.
        { eapply to_equiv_class_eq. }
        { eapply Ord.from_wf_set_upperbound. }
      }
      { eapply Ord.build_spec. i. hexploit (proj2_sig a). i. des.
        eapply to_equiv_class_equiv in H. subst.
        eapply Ord.eq_lt_lt.
        { symmetry. eapply to_equiv_class_eq. }
        { eapply Ord.from_wf_set_upperbound. }
      }
    Qed.
  End TOTALIFY.

  Definition to_total_set (o: Ord.t): Type := equiv_class (to_set_well_founded o).
  Definition to_total_rel (o: Ord.t): (to_total_set o) -> (to_total_set o) -> Prop :=
    @equiv_class_rel _ _ (to_set_well_founded o).
  Arguments to_total_rel: clear implicits.

  Lemma to_total_well_founded (o: Ord.t): well_founded (to_total_rel o).
  Proof.
    eapply equiv_class_well_founded.
  Defined.
  Arguments to_total_well_founded: clear implicits.

  Lemma to_total_eq (o: Ord.t):
    Ord.eq o (Ord.from_wf_set (@to_total_well_founded o)).
  Proof.
    etransitivity.
    - eapply to_set_eq.
    - eapply (from_wf_set_equiv_class (@to_set_well_founded o)).
  Qed.

  Lemma to_total_total (o: Ord.t):
    forall (x0 x1: to_total_set o), to_total_rel o x0 x1 \/ x0 = x1 \/ to_total_rel o x1 x0.
  Proof.
    eapply equiv_class_total.
  Qed.
End ToSet.
