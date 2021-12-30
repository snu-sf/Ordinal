From Ordinal Require Import sflib Basics ClassicalOrdinal Cardinal Inaccessibility.
From Ordinal Require Export Ordinal Arithmetic.

Require Import ClassicalChoice.
Require Import Program.

Set Implicit Arguments.
Set Primitive Projections.

Section STRONGLYINACCESSIBLE.
  Let SmallT: Type := Type.
  Let X := @sig (@sigT SmallT (fun X => X -> X -> Prop))
                (fun PR => well_founded (projT2 PR)).
  Let Y : X -> Ord.t := fun PRWF => Ord.from_wf_set (proj2_sig PRWF).
  Definition kappa := Ord.large.
  Local Transparent Ord.large.

  Lemma kappa_complete o (LT: Ord.lt o kappa):
    exists (A: SmallT) (R: A -> A -> Prop) (WF: well_founded R),
      Ord.le o (Ord.from_wf_set WF).
  Proof.
    eapply Ord.lt_inv in LT. des. eauto.
  Qed.

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
        Ord.eq (Ord.from_wf (WF a) x)
               (Ord.from_wf _union_rel_well_founded (existT _ a (Some x))).
    Proof.
      revert x. eapply (well_founded_induction (WF a)).
      i. split.
      { eapply Ord.from_wf_supremum. i. specialize (H _ LT). inv H.
        eapply Ord.le_lt_lt; eauto. eapply Ord.lt_from_wf. econs; eauto. }
      { eapply Ord.from_wf_supremum. i. dependent destruction LT.
        specialize (H _ LT). inv H.
        eapply Ord.le_lt_lt; eauto. eapply Ord.lt_from_wf. auto. }
    Qed.

    Let _from_wf_set_union:
      Ord.eq (@Ord.build A (fun a => Ord.from_wf_set (WF a)))
             (Ord.from_wf_set _union_rel_well_founded).
    Proof.
      Local Transparent Ord.from_wf_set.
      split.
      { econs. i. exists (existT _ a0 None). eapply Ord.build_supremum. i.
        eapply (@Ord.le_lt_lt (Ord.from_wf _union_rel_well_founded (existT _ a0 (Some a)))).
        { eapply _from_wf_union. }
        { eapply Ord.lt_from_wf. econs. }
      }
      { econs. i. destruct a0 as [a0 [x|]].
        { exists a0. transitivity (Ord.from_wf (WF a0) x).
          { eapply _from_wf_union. }
          { eapply Ord.lt_le. eapply Ord.from_wf_set_upperbound. }
        }
        { exists a0. eapply Ord.from_wf_supremum. i.
          dependent destruction LT.
          eapply (@Ord.le_lt_lt (Ord.from_wf (WF a0) x)).
          { eapply _from_wf_union. }
          { eapply Ord.from_wf_set_upperbound. }
        }
      }
    Qed.

    Lemma small_join_small:
      exists (U: SmallT) (RU: U -> U -> Prop) (WFU: well_founded RU),
        forall a, Ord.lt (Ord.from_wf_set (WF a)) (Ord.from_wf_set WFU).
    Proof.
      exists _union_set, _union_rel, _union_rel_well_founded. i.
      eapply Ord.lt_eq_lt.
      { symmetry. eapply _from_wf_set_union. }
      eapply (@Ord.build_upperbound _ (fun a0 => Ord.from_wf_set (WF a0)) a).
    Qed.
  End UNION.

  Lemma smaller_cardinal_small (A: Type) (B: SmallT)
        (LE: Ord.le (Cardinal.cardinal A) (Cardinal.cardinal B))
    :
      exists (A': SmallT),
        Ord.eq (Cardinal.cardinal A) (Cardinal.cardinal A').
  Proof.
    eapply Cardinal._cardinal_le_iff in LE. inv LE.
    set (A' := @sig B (fun b => exists a, f a = b)). exists A'.
    split.
    { apply Cardinal._cardinal_le_iff.
      eapply Cardinal._cardinal_le_intro with (f:=fun a => exist _ (f a) (ex_intro _ a eq_refl)).
      i. inv EQ. eapply INJ; eauto.
    }
    { hexploit (choice (fun (a': A') (a: A) =>
                          f a = proj1_sig a')).
      { i. destruct x. s. eauto. }
      i. des. apply Cardinal._cardinal_le_iff.
      eapply Cardinal._cardinal_le_intro with (f:=f0).
      i. destruct a0, a1. des. subst.
      dup EQ. eapply f_equal with (f:=f) in EQ0.
      rewrite H in EQ0. rewrite H in EQ0. ss.
      eapply INJ in EQ0. subst. auto.
    }
  Qed.

  Lemma small_ordinal_small o (LT: Ord.lt o kappa):
    exists (A: SmallT), Ord.eq (Cardinal.cardinal A) (Cardinal.cardinal (ToSet.to_total_set o)).
  Proof.
    eapply kappa_complete in LT. des.
    hexploit (@smaller_cardinal_small (ToSet.to_total_set o) A).
    { etransitivity.
      2: { eapply Cardinal.from_wf_set_to_total. }
      { eapply Cardinal.to_total_le. eauto. }
    }
    i. des. esplits. symmetry. eapply H.
  Qed.

  Lemma sum_of_small o (LT: Ord.lt o kappa):
    exists (A: SmallT) (os: A -> Ord.t), Ord.eq o (Ord.build os).
  Proof.
    hexploit small_ordinal_small; eauto. i. des.
    hexploit Cardinal.sum_of_smaller_same_cardinal; eauto.
  Qed.



  Lemma kappa_inaccessible_build (A: SmallT) (os: A -> Ord.t) (LT: forall a, Ord.lt (os a) kappa)
    :
      Ord.lt (Ord.build os) kappa.
  Proof.
    hexploit (choice (fun (a: A) (XRWF: @sig (@sigT SmallT (fun X => X -> X -> Prop)) (fun XR => well_founded (projT2 XR))) =>
                        Ord.le (os a) (Ord.from_wf_set (proj2_sig XRWF)))).
    { i. eapply NNPP. ii. eapply Ord.lt_not_le.
      { eapply (LT x). }
      eapply Ord.build_supremum. i. destruct (ClassicOrd.total (os x) (Y a)); auto.
      exfalso. eapply H. exists a. auto.
    }
    i. des.
    hexploit (@small_join_small A (fun a => projT1 (proj1_sig (f a))) (fun a => projT2 (proj1_sig (f a))) (fun a => proj2_sig (f a))).
    i. des. eapply (@Ord.le_lt_lt (Ord.from_wf_set WFU)).
    { eapply Ord.build_supremum; eauto. i. eapply (@Ord.le_lt_lt (Ord.from_wf_set (proj2_sig (f a)))).
      { eapply H. }
      { eapply H0. }
    }
    eapply (@Ord.build_upperbound X Y (exist _ (existT _ U RU) WFU)).
  Qed.

  Lemma kappa_inaccessible_is_join (A: SmallT) (os: A -> Ord.t) (LT: forall a, Ord.lt (os a) kappa)
        o (JOIN: Ord.is_join os o)
    :
      Ord.lt o kappa.
  Proof.
    eapply (@Ord.le_lt_lt (Ord.build os)).
    2: { eapply kappa_inaccessible_build; auto. }
    eapply Ord.is_join_supremum; eauto.
    i. eapply Ord.lt_le. eapply Ord.build_upperbound.
  Qed.

  Lemma kappa_inaccessible_join (A: SmallT) (os: A -> Ord.t) (LT: forall a, Ord.lt (os a) kappa):
    Ord.lt (Ord.join os) kappa.
  Proof.
    eapply kappa_inaccessible_is_join; eauto. eapply Ord.join_is_join.
  Qed.

  Let D: SmallT := unit.
  Let D_well_founded: @well_founded D (fun _ _ => False).
  Proof.
    ii. econs; ss.
  Qed.

  Lemma kappa_inaccesible_from_acc (A: SmallT) (R: A -> A -> Prop) a (ACC: Acc R a):
    Ord.lt (Ord.from_acc ACC) kappa.
  Proof.
    dup ACC. revert ACC. induction ACC0. i.
    destruct ACC. ss.
    hexploit (@kappa_inaccessible_build (sig (fun a0 => R a0 x)) (fun a0p : {a0 : A | R a0 x} => Ord.from_acc (Ordinal.Ord.from_acc_obligation_1 (Acc_intro x a) a0p))); eauto.
    i. destruct a0. ss. eapply H0; eauto.
  Qed.

  Lemma kappa_inaccesible_from_wf (A: SmallT) (R: A -> A -> Prop) (WF: well_founded R) a:
    Ord.lt (Ord.from_wf WF a) kappa.
  Proof.
    Local Transparent Ord.from_wf.
    eapply kappa_inaccesible_from_acc.
  Qed.

  Lemma kappa_inaccesible_from_wf_set (A: SmallT) (R: A -> A -> Prop) (WF: well_founded R):
    Ord.lt (Ord.from_wf_set WF) kappa.
  Proof.
    Local Transparent Ord.from_wf_set.
    eapply kappa_inaccessible_build. i. eapply kappa_inaccesible_from_wf.
  Qed.

  Lemma kappa_inaccessible_cardinal (A: SmallT):
    Ord.lt (Cardinal.cardinal A) kappa.
  Proof.
    hexploit (Cardinal.cardinal_of_cardinal A). i. inv H.
    des. eapply Ord.eq_lt_lt.
    { symmetry. eapply H2. }
    eapply (@Ord.build_upperbound X Y (exist _ (existT _ A R) WF)).
  Qed.

  Lemma kappa_inaccessible_is_O o (ZERO: Ord.is_O o):
    Ord.lt o kappa.
  Proof.
    eapply Ord.le_lt_lt.
    { eapply ZERO. }
    eapply (@Ord.build_upperbound X Y (exist _ (existT _ D (fun _ _ => False)) D_well_founded)).
  Qed.

  Lemma kappa_inaccessible_O:
    Ord.lt Ord.O kappa.
  Proof.
    eapply kappa_inaccessible_is_O. eapply Ord.O_is_O.
  Qed.

  Lemma kappa_inaccessible_is_S o s (SUCC: Ord.is_S o s) (LT: Ord.lt o kappa):
    Ord.lt s kappa.
  Proof.
    eapply (@Ord.le_lt_lt (@Ord.build D (fun _ => o))).
    { eapply SUCC. eapply (Ord.build_upperbound (fun _ : D => o) tt). }
    { eapply kappa_inaccessible_build; eauto. }
  Qed.

  Lemma kappa_inaccessible_S o (LT: Ord.lt o kappa):
    Ord.lt (Ord.S o) kappa.
  Proof.
    eapply kappa_inaccessible_is_S; eauto.
    eapply Ord.S_is_S.
  Qed.

  Lemma kappa_inaccessible_nat n: Ord.lt (Ord.from_nat n) kappa.
  Proof.
    Local Transparent Ord.from_nat.
    induction n; ss.
    - eapply kappa_inaccessible_O.
    - eapply kappa_inaccessible_S. auto.
  Qed.

  Lemma kappa_inaccessible_omega: Ord.lt Ord.omega kappa.
  Proof.
    Local Transparent Ord.omega.
    eapply kappa_inaccessible_join.
    eapply kappa_inaccessible_nat.
  Qed.

  Lemma kappa_inaccessible_power o (LT: Ord.lt o kappa):
    Ord.lt (Cardinal.cardinal (ToSet.to_total_set o -> Prop)) kappa.
  Proof.
    hexploit (kappa_complete LT); eauto. i. des.
    eapply (@Ord.le_lt_lt (Cardinal.cardinal (A -> Prop))).
    { apply Cardinality.cardinal_le_iff.
      eapply Cardinality.le_power. apply Cardinality.cardinal_le_iff.
      etransitivity.
      { eapply Cardinal.to_total_le. eapply H. }
      eapply Cardinal.from_wf_set_to_total.
    }
    eapply kappa_inaccessible_cardinal.
  Qed.

  Lemma kappa_inaccessible_next_cardinal o (LT: Ord.lt o kappa):
    Ord.lt (Cardinal.next_cardinal (ToSet.to_total_set o)) kappa.
  Proof.
    eapply Ord.le_lt_lt.
    2: { eapply kappa_inaccessible_power. eauto. }
    eapply Cardinal.aleph_gen_le_beth_gen.
  Qed.

  Lemma kappa_inaccessible_union o0 o1 (LT0: Ord.lt o0 kappa) (LT1: Ord.lt o1 kappa):
    Ord.lt (Ord.union o0 o1) kappa.
  Proof.
    Local Transparent Ord.union.
    eapply kappa_inaccessible_join. i. destruct a; auto.
  Qed.

  Lemma kappa_regular A
        (SIZE: Ord.lt (Cardinal.cardinal A) kappa)
        (os: A -> Ord.t)
        (LT: forall a, Ord.lt (os a) kappa)
    :
      Ord.lt (Ord.join os) kappa.
  Proof.
    eapply small_ordinal_small in SIZE. des.
    assert (Cardinality.eq A0 A).
    { eapply Cardinality.cardinal_eq_iff in SIZE.
      etransitivity; [eapply SIZE|].
      symmetry. eapply Cardinality.cardinal_to_total_bij. }
    apply Cardinality.eq_bij_equiv in H. inv H.
    eapply (@Ord.le_lt_lt (@Ord.join A0 (fun a0 => os (f a0)))).
    { eapply Ord.le_join. i. exists (g a0).
      rewrite GF. reflexivity. }
    { eapply kappa_inaccessible_join. i. auto. }
  Qed.

  Lemma kappa_weakly_inaccesible
        A (SIZE: Ord.lt (Cardinal.cardinal A) kappa):
    inaccessible A Ord.omega Cardinal.aleph_gen kappa.
  Proof.
    econs.
    { eapply kappa_inaccessible_omega. }
    { eapply kappa_inaccessible_next_cardinal. }
    { eapply kappa_regular; eauto. }
    { eapply kappa_inaccessible_union. }
  Qed.

  Theorem kappa_strongly_inaccesible
          A (SIZE: Ord.lt (Cardinal.cardinal A) kappa):
    inaccessible A Ord.omega Cardinal.beth_gen kappa.
  Proof.
    econs.
    { eapply kappa_inaccessible_omega. }
    { eapply kappa_inaccessible_power. }
    { eapply kappa_regular; eauto. }
    { eapply kappa_inaccessible_union. }
  Qed.

  Lemma kappa_inaccessible_rec (base: Ord.t) (next: Ord.t -> Ord.t)
        (BASE: Ord.lt base kappa)
        (NEXT: forall o (LT: Ord.lt o kappa), Ord.lt (next o) kappa)
        (NEXTLE: forall o0 o1 (LE: Ord.le o0 o1), Ord.le (next o0) (next o1))
        o
        (LT: Ord.lt o kappa):
    Ord.lt (Ord.orec base next o) kappa.
  Proof.
    revert o LT.
    eapply (well_founded_induction
              Ord.lt_well_founded
              (fun o => forall (LT: Ord.lt o kappa), Ord.lt (Ord.orec base next o) kappa)).
    i. dup LT. eapply sum_of_small in LT. des.
    eapply Ord.le_lt_lt.
    { eapply Ord.le_orec.
      { auto. }
      { eapply LT. }
    }
    Local Transparent Ord.rec.
    eapply kappa_inaccessible_join. i. destruct a; auto.
    { eapply kappa_inaccessible_join. i.
      eapply NEXT. eapply H; auto.
      { eapply Ord.lt_eq_lt.
        { eapply LT. }
        { eapply Ord.build_upperbound. }
      }
      { etransitivity.
        { eapply Ord.build_upperbound. }
        { eapply Ord.eq_lt_lt; eauto. symmetry. eauto. }
      }
    }
  Qed.

  Lemma kappa_inaccessible_aleph o (LT: Ord.lt o kappa):
    Ord.lt (Cardinal.aleph o) kappa.
  Proof.
    eapply kappa_inaccessible_rec.
    { eapply kappa_inaccessible_omega. }
    { i. eapply kappa_inaccessible_next_cardinal. auto. }
    { i. eapply Cardinal.le_aleph_gen. auto. }
    { auto. }
  Qed.

  Lemma kappa_inaccessible_beth o (LT: Ord.lt o kappa):
    Ord.lt (Cardinal.beth o) kappa.
  Proof.
    eapply kappa_inaccessible_rec.
    { eapply kappa_inaccessible_omega. }
    { i. eapply kappa_inaccessible_power. auto. }
    { i. eapply Cardinal.le_beth_gen. auto. }
    { auto. }
  Qed.

  Lemma kappa_fixpoint (base: Ord.t) (next: Ord.t -> Ord.t)
        (BASE: Ord.lt base kappa)
        (NEXT: forall o (LT: Ord.lt o kappa), Ord.lt (next o) kappa)
        (NEXTLE: forall o0 o1 (LE: Ord.le o0 o1), Ord.le (next o0) (next o1))
        (EXPAND: forall o, Ord.le (Ord.S o) (next o)):
    Ord.eq kappa (Ord.orec base next kappa).
  Proof.
    split.
    - eapply Ord.eq_le_le.
      { eapply Ord.orec_of_S. }
      eapply Ord.orec_mon.
      { eapply Ord.O_bot. }
      { i. transitivity (Ord.S o1); auto.
        apply Ord.le_S. auto. }
    - eapply Ord.orec_build_supremum.
      { eapply Ord.lt_le. auto. }
      { i. eapply Ord.lt_le. eapply NEXT.
        eapply kappa_inaccessible_rec; auto. }
  Qed.

  Lemma kappa_aleph_fixpoint:
    Ord.eq kappa (Cardinal.aleph kappa).
  Proof.
    eapply kappa_fixpoint.
    { eapply kappa_inaccessible_omega. }
    { i. eapply kappa_inaccessible_next_cardinal. auto. }
    { i. eapply Cardinal.le_aleph_gen. auto. }
    { i. eapply Ord.S_supremum. eapply Cardinal.aleph_gen_lt. }
  Qed.

  Lemma kappa_beth_fixpoint:
    Ord.eq kappa (Cardinal.beth kappa).
  Proof.
    eapply kappa_fixpoint.
    { eapply kappa_inaccessible_omega. }
    { i. eapply kappa_inaccessible_power. auto. }
    { i. eapply Cardinal.le_beth_gen. auto. }
    { i. eapply Ord.S_supremum. eapply Cardinal.beth_gen_lt. }
  Qed.

  Lemma kappa_inaccessible_add o0 o1 (LT0: Ord.lt o0 kappa) (LT1: Ord.lt o1 kappa):
    Ord.lt (OrdArith.add o0 o1) kappa.
  Proof.
    Local Transparent OrdArith.add.
    eapply kappa_inaccessible_rec; auto.
    { eapply kappa_inaccessible_S. }
    { i. eapply Ord.le_S. auto. }
  Qed.

  Lemma kappa_inaccessible_mult o0 o1 (LT0: Ord.lt o0 kappa) (LT1: Ord.lt o1 kappa):
    Ord.lt (OrdArith.mult o0 o1) kappa.
  Proof.
    Local Transparent OrdArith.mult.
    eapply kappa_inaccessible_rec; auto.
    { eapply kappa_inaccessible_O. }
    { i. eapply kappa_inaccessible_add; auto. }
    { i. eapply OrdArith.le_add_l. auto. }
  Qed.

  Lemma kappa_inaccessible_expn o0 o1 (LT0: Ord.lt o0 kappa) (LT1: Ord.lt o1 kappa):
    Ord.lt (OrdArith.expn o0 o1) kappa.
  Proof.
    Local Transparent OrdArith.expn.
    eapply kappa_inaccessible_rec; auto.
    { eapply kappa_inaccessible_S.
      eapply kappa_inaccessible_O. }
    { i. eapply kappa_inaccessible_mult; auto. }
    { i. eapply OrdArith.le_mult_l. auto. }
  Qed.

End STRONGLYINACCESSIBLE.

Create HintDb ord_kappa.
#[export] Hint Resolve kappa_inaccessible_build: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_join: ord_kappa.
#[export] Hint Resolve kappa_inaccesible_from_acc: ord_kappa.
#[export] Hint Resolve kappa_inaccesible_from_wf: ord_kappa.
#[export] Hint Resolve kappa_inaccesible_from_wf_set: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_O: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_S: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_nat: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_omega: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_union: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_add: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_mult: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_expn: ord_kappa.
