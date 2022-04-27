From Ordinal Require Import sflib Basics.
From Ordinal Require Export Ordinal Arithmetic.

Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms.

Set Implicit Arguments.
Set Primitive Projections.

Module Hessenberg.
  Program Let _add: Ord.t * Ord.t -> Ord.t :=
    Fix (double_rel_well_founded Ord.lt_well_founded Ord.lt_well_founded) (fun _ => Ord.t)
        (fun o0o1 add =>
           match o0o1 with
           | (o0, o1) =>
               Ord.union
                 (match o1 with
                  | @Ord.build X1 os1 => Ord.build (fun x1 => @add (o0, os1 x1) _)
                  end)
                 (match o0 with
                  | @Ord.build X0 os0 => Ord.build (fun x0 => @add (os0 x0, o1) _)
                  end)
           end).
  Next Obligation.
    right. econs. reflexivity.
  Qed.
  Next Obligation.
    left. econs. reflexivity.
  Qed.

  Definition add (o0 o1: Ord.t): Ord.t :=
    _add (o0, o1).

  Let _add_red (o0o1: Ord.t * Ord.t)
    :
    Ord.eq
      (_add o0o1)
      (match o0o1 with
       | (o0, o1) =>
           Ord.union
             (match o1 with
              | @Ord.build X1 os1 => Ord.build (fun x1 => _add (o0, os1 x1))
              end)
             (match o0 with
              | @Ord.build X0 os0 => Ord.build (fun x0 => _add (os0 x0, o1))
              end)
       end).
  Proof.
    unfold _add. rewrite Fix_equiv; ss.
    { destruct o0o1 as [[] []]. ss. reflexivity. }
    { i. ss. destruct x as [[] []].
      eapply Ord.eq_union.
      { split.
        { econs. i. exists a0. eapply H. }
        { econs. i. exists a0. eapply H. }
      }
      { split.
        { econs. i. exists a0. eapply H. }
        { econs. i. exists a0. eapply H. }
      }
    }
  Qed.

  Lemma add_red X0 (os0: X0 -> Ord.t) X1 (os1: X1 -> Ord.t)
    :
    Ord.eq
      (add (@Ord.build X0 os0) (@Ord.build X1 os1))
      (Ord.union
         (Ord.build (fun x1 => add (@Ord.build X0 os0) (os1 x1)))
         (Ord.build (fun x0 => add (os0 x0) (@Ord.build X1 os1)))).
  Proof.
    unfold add. apply _add_red.
  Qed.
  Global Opaque add.

  Lemma le_add_l o0 o1 o2 (LE: Ord.le o0 o1)
    :
    Ord.le (add o0 o2) (add o1 o2).
  Proof.
    revert o0 LE. pattern o1, o2. revert o1 o2.
    eapply (double_well_founded_induction Ord.lt_well_founded Ord.lt_well_founded).
    i. dup LE. inv LE. destruct b1.
    rewrite add_red. rewrite add_red.
    eapply Ord.le_union.
    { econs. i. exists a0. eapply IHR; auto. econs. reflexivity. }
    { econs. i. specialize (LE1 a0). des.
      exists a1. eapply IHL; auto. econs. reflexivity. }
  Qed.

  Lemma le_add_r o0 o1 o2 (LE: Ord.le o1 o2)
    :
    Ord.le (add o0 o1) (add o0 o2).
  Proof.
    revert o1 LE. pattern o0. pattern o2. revert o0 o2.
    eapply (double_well_founded_induction Ord.lt_well_founded Ord.lt_well_founded).
    i. dup LE. inv LE. destruct a1.
    rewrite add_red. rewrite add_red.
    eapply Ord.le_union.
    { econs. i. specialize (LE1 a0). des.
      exists a1. eapply IHR; auto. econs. reflexivity. }
    { econs. i. exists a0. eapply IHL; auto. econs. reflexivity. }
  Qed.

  Lemma eq_add_l o0 o1 o2 (EQ: Ord.eq o0 o1)
    :
    Ord.eq (add o0 o2) (add o1 o2).
  Proof.
    econs.
    { eapply le_add_l. eapply EQ. }
    { eapply le_add_l. eapply EQ. }
  Qed.

  Lemma eq_add_r o0 o1 o2 (EQ: Ord.eq o1 o2)
    :
    Ord.eq (add o0 o1) (add o0 o2).
  Proof.
    econs.
    { eapply le_add_r. eapply EQ. }
    { eapply le_add_r. eapply EQ. }
  Qed.

  Global Program Instance add_eq_proper: Proper (Ord.eq ==> Ord.eq ==> Ord.eq) (add).
  Next Obligation.
    ii.
    etransitivity.
    - eapply eq_add_l; eauto.
    - eapply eq_add_r; eauto.
  Qed.

  Global Program Instance add_le_proper: Proper (Ord.le ==> Ord.le ==> Ord.le) (add).
  Next Obligation.
    ii.
    etransitivity.
    - eapply le_add_l; eauto.
    - eapply le_add_r; eauto.
  Qed.

  Lemma lt_add_l o0 o1 o2 (LT: Ord.lt o0 o1)
    :
    Ord.lt (add o0 o2) (add o1 o2).
  Proof.
    inv LT. destruct o2. rewrite add_red. eapply Ord.lt_le_lt.
    2:{ eapply Ord.union_r. }
    { eapply Ord.le_lt_lt.
      { rewrite LE. reflexivity. }
      { econs. reflexivity. }
    }
  Qed.

  Lemma lt_add_r o0 o1 o2 (LT: Ord.lt o1 o2)
    :
    Ord.lt (add o0 o1) (add o0 o2).
  Proof.
    inv LT. destruct o0. rewrite add_red. eapply Ord.lt_le_lt.
    2:{ eapply Ord.union_l. }
    { eapply Ord.le_lt_lt.
      { rewrite LE. reflexivity. }
      { econs. reflexivity. }
    }
  Qed.

  Lemma add_spec o0 o1 o2
        (SUP0: forall o (LT: Ord.lt o o0), Ord.lt (add o o1) o2)
        (SUP1: forall o (LT: Ord.lt o o1), Ord.lt (add o0 o) o2)
    :
    Ord.le (add o0 o1) o2.
  Proof.
    destruct o0, o1. rewrite add_red. eapply Ord.union_spec.
    { eapply Ord.build_supremum. i. eapply SUP1. econs. reflexivity. }
    { eapply Ord.build_supremum. i. eapply SUP0. econs. reflexivity. }
  Qed.

  Lemma add_comm o0 o1
    :
    Ord.eq (add o0 o1) (add o1 o0).
  Proof.
    revert o0 o1.
    cut (forall o0 o1, Ord.le (add o0 o1) (add o1 o0)).
    { i. split; eauto. }
    i. pattern o0, o1. revert o0 o1.
    eapply (double_well_founded_induction Ord.lt_well_founded Ord.lt_well_founded).
    i. destruct a1, b1. rewrite add_red. rewrite add_red.
    rewrite Ord.union_comm. eapply Ord.le_union.
    { econs. i. exists a0. eapply IHL. econs. reflexivity. }
    { econs. i. exists a0. eapply IHR. econs. reflexivity. }
  Qed.

  Lemma add_assoc o0 o1 o2
    :
    Ord.eq (add (add o0 o1) o2) (add o0 (add o1 o2)).
  Proof.
    revert o0 o1 o2.
    cut (forall o0 o1o2, (fun o0 o1o2 => (add (add o0 (fst o1o2)) (snd o1o2) == add o0 (add (fst o1o2) (snd o1o2)))%ord) o0 o1o2).
    { i. eapply (H o0 (o1, o2)). }
    eapply (double_well_founded_induction Ord.lt_well_founded (double_rel_well_founded Ord.lt_well_founded Ord.lt_well_founded)).
    intros o0 [o1 o2] IH0 IH12. ss.
    assert (IH1: forall o (LT: (o < o1)%ord), (add (add o0 o) o2 == add o0 (add o o2))%ord).
    { i. eapply (IH12 (o, o2)). left. auto. }
    assert (IH2: forall o (LT: (o < o2)%ord), (add (add o0 o1) o == add o0 (add o1 o))%ord).
    { i. eapply (IH12 (o1, o)). right. auto. }
    clear IH12. destruct o0, o1, o2.
    rewrite add_red. rewrite add_red.
    rewrite Ord.union_build. rewrite Ord.union_build.
    rewrite add_red. rewrite add_red.
    rewrite Ord.union_build. rewrite Ord.union_build. split.
    { econs.
      { i. destruct a0 as [|[]].
        { exists (inl (inl a)). ss. rewrite <- IH2.
          { rewrite add_red. rewrite Ord.union_build. reflexivity. }
          { econs. reflexivity. }
        }
        { exists (inl (inr a)). ss.
          eapply IH1. econs. reflexivity. }
        { exists (inr a). ss. rewrite IH0.
          { rewrite add_red. rewrite Ord.union_build. reflexivity. }
          { econs. reflexivity. }
        }
      }
    }
    { econs.
      { i. destruct a0 as [[]|].
        { exists (inl a). ss. rewrite <- IH2.
          { rewrite add_red. rewrite Ord.union_build. reflexivity. }
          { econs. reflexivity. }
        }
        { exists (inr (inl a)). ss.
          eapply IH1. econs. reflexivity. }
        { exists (inr (inr a)). ss. rewrite IH0.
          { rewrite add_red. rewrite Ord.union_build. reflexivity. }
          { econs. reflexivity. }
        }
      }
    }
  Qed.

  Lemma add_base_l o0 o1
    :
    Ord.le o0 (add o0 o1).
  Proof.
    revert o1. pattern o0. revert o0.
    eapply (well_founded_induction Ord.lt_well_founded).
    i. destruct x. eapply Ord.build_supremum. i.
    eapply Ord.le_lt_lt.
    { eapply H. econs. reflexivity. }
    { eapply lt_add_l. econs. reflexivity. }
  Qed.

  Lemma add_base_r o0 o1
    :
    Ord.le o1 (add o0 o1).
  Proof.
    rewrite add_comm. eapply add_base_l.
  Qed.

  Lemma arith_add_larger o0 o1
    :
    Ord.le (OrdArith.add o0 o1) (add o0 o1).
  Proof.
    revert o0. pattern o1. revert o1.
    eapply (well_founded_induction Ord.lt_well_founded).
    i. destruct x. rewrite OrdArith.add_build. eapply Ord.union_spec.
    { eapply add_base_l. }
    { eapply Ord.join_supremum. i. eapply Ord.S_supremum.
      eapply Ord.le_lt_lt.
      { eapply H. econs. reflexivity. }
      { eapply lt_add_r. econs. reflexivity. }
    }
  Qed.

  Lemma add_O_r o
    :
    Ord.eq (add o Ord.O) o.
  Proof.
    pattern o. revert o. eapply (well_founded_induction Ord.lt_well_founded).
    intros o IH. split.
    { eapply add_spec.
      { i. rewrite IH; auto. }
      { i. exfalso. eapply Ord.lt_StrictOrder. eapply Ord.lt_le_lt.
        { eapply LT. }
        { eapply Ord.O_bot. }
      }
    }
    { eapply add_base_l. }
  Qed.

  Lemma add_O_l o
    :
    Ord.eq (add Ord.O o) o.
  Proof.
    rewrite add_comm. eapply add_O_r.
  Qed.

  Lemma add_S_r o0 o1
    :
    Ord.eq (add o0 (Ord.S o1)) (Ord.S (add o0 o1)).
  Proof.
    revert o1. pattern o0. revert o0.
    eapply (well_founded_induction Ord.lt_well_founded). i.
    split.
    { eapply add_spec.
      { i. rewrite H; auto. eapply Ord.lt_S. eapply lt_add_l; auto. }
      { i. eapply Ord.le_lt_lt; [|eapply Ord.S_lt].
        eapply Ord.S_supremum in LT. eapply le_add_r.
        eapply Ord.le_S_rev; auto.
      }
    }
    { eapply Ord.S_supremum. eapply lt_add_r. eapply Ord.S_lt. }
  Qed.

  Lemma add_S_l o0 o1
    :
    Ord.eq (add (Ord.S o0) o1) (Ord.S (add o0 o1)).
  Proof.
    rewrite add_comm. rewrite add_S_r. rewrite add_comm. reflexivity.
  Qed.

  Lemma add_from_nat o (n: nat)
    :
    Ord.eq (add o n) (OrdArith.add o n).
  Proof.
    revert o. induction n; i.
    { rewrite Ord.from_nat_O.
      rewrite add_O_r. rewrite OrdArith.add_O_r. reflexivity.
    }
    { rewrite Ord.from_nat_S.
      rewrite add_S_r. rewrite OrdArith.add_S. rewrite IHn. reflexivity.
    }
  Qed.
End Hessenberg.
