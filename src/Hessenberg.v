From Ordinal Require Import sflib Basics.
From Ordinal Require Export Ordinal Arithmetic.

Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms.

Set Implicit Arguments.
Set Primitive Projections.

Module Hessenberg.
  Section ADD.
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

    Lemma add_supremum o0 o1 o
          (LE0: forall o2 (LT: Ord.lt o2 o0), Ord.lt (add o2 o1) o)
          (LE1: forall o2 (LT: Ord.lt o2 o1), Ord.lt (add o0 o2) o)
      :
      Ord.le (add o0 o1) o.
    Proof.
      destruct o0, o1. rewrite add_red.
      apply Ord.union_spec.
      { eapply Ord.build_supremum. i. eapply LE1. eapply Ord.build_upperbound. }
      { eapply Ord.build_supremum. i. eapply LE0. eapply Ord.build_upperbound. }
    Qed.

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

    Lemma add_lt_l o0 o1 (LT: Ord.lt Ord.O o1): Ord.lt o0 (add o0 o1).
    Proof.
      eapply Ord.lt_le_lt.
      2:{ eapply arith_add_larger. }
      eapply OrdArith.add_lt_l. auto.
    Qed.

    Lemma add_lt_r o0 o1 (LT: Ord.lt Ord.O o0): Ord.lt o1 (add o0 o1).
    Proof.
      rewrite add_comm. apply add_lt_l; auto.
    Qed.
  End ADD.
End Hessenberg.

Global Opaque Hessenberg.add.

Infix "⊕" := Hessenberg.add (at level 80, right associativity) : ord_scope.

(* following: *)
(* https://arxiv.org/pdf/1501.05747.pdf *)
(* (INTERMEDIATE ARITHMETIC OPERATIONS ON ORDINAL NUMBERS - HARRY ALTMAN) *)
Module Jacobsthal.
  Section MULT.
    Definition mult (o0: Ord.t): forall (o1: Ord.t), Ord.t := Ord.orec Ord.O (Hessenberg.add o0).

    Let _mult_gen_le := Hessenberg.add_base_r.
    Let _mult_gen_mon := Hessenberg.le_add_r.

    Lemma arith_mult_larger o0 o1
      :
      Ord.le (OrdArith.mult o0 o1) (mult o0 o1).
    Proof.
      Local Transparent OrdArith.mult.
      eapply Ord.orec_mon.
      { reflexivity. }
      { i. rewrite LE. rewrite Hessenberg.add_comm.
        eapply Hessenberg.arith_add_larger.
      }
    Qed.

    Lemma mult_O_r o: Ord.eq (mult o Ord.O) Ord.O.
    Proof.
      eapply (@Ord.orec_O Ord.O (Hessenberg.add o)); auto.
    Qed.

    Lemma mult_S o0 o1: Ord.eq (mult o0 (Ord.S o1)) (Hessenberg.add o0 (mult o0 o1)).
    Proof.
      eapply (@Ord.orec_S Ord.O (Hessenberg.add o0)); auto.
    Qed.

    Lemma mult_join o A (os: A -> Ord.t):
      Ord.eq (mult o (Ord.join os)) (Ord.join (fun a => mult o (os a))).
    Proof.
      transitivity (Ord.union Ord.O (Ord.join (fun a => mult o (os a)))).
      { eapply (@Ord.orec_join Ord.O (Hessenberg.add _)); eauto. }
      { eapply Ord.union_max. eapply Ord.O_bot. }
    Qed.

    Lemma mult_build o A (os: A -> Ord.t)
      :
      Ord.eq (mult o (Ord.build os)) (Ord.join (fun a => Hessenberg.add o (mult o (os a)))).
    Proof.
      transitivity (Ord.union Ord.O (Ord.join (fun a => Hessenberg.add o (mult o (os a))))).
      { eapply (@Ord.orec_build Ord.O (Hessenberg.add _)); eauto. }
      { eapply Ord.union_max. eapply Ord.O_bot. }
     Qed.

    Lemma mult_union o0 o1 o2
      :
      Ord.eq (mult o0 (Ord.union o1 o2)) (Ord.union (mult o0 o1) (mult o0 o2)).
    Proof.
      eapply Ord.orec_union; auto.
    Qed.

    Lemma le_mult_r o0 o1 o2 (LE: Ord.le o1 o2)
      :
      Ord.le (mult o0 o1) (mult o0 o2).
    Proof.
      eapply Ord.le_orec; auto.
    Qed.

    Lemma eq_mult_r o0 o1 o2 (EQ: Ord.eq o1 o2)
      :
      Ord.eq (mult o0 o1) (mult o0 o2).
    Proof.
      split.
      - eapply le_mult_r; eauto. eapply EQ.
      - eapply le_mult_r; eauto. eapply EQ.
    Qed.

    Lemma le_mult_l o0 o1 o2 (LE: Ord.le o0 o1)
      :
      Ord.le (mult o0 o2) (mult o1 o2).
    Proof.
      eapply (@Ord.orec_mon Ord.O (Hessenberg.add o0) Ord.O (Hessenberg.add o1)); auto.
      { reflexivity. }
      { i. transitivity (Hessenberg.add o0 o4).
        { eapply Hessenberg.le_add_r; auto. }
        { eapply Hessenberg.le_add_l; auto. }
      }
    Qed.

    Lemma eq_mult_l o0 o1 o2 (EQ: Ord.eq o0 o1)
      :
      Ord.eq (mult o0 o2) (mult o1 o2).
    Proof.
      split.
      - eapply le_mult_l; eauto. eapply EQ.
      - eapply le_mult_l; eauto. eapply EQ.
    Qed.

    Lemma lt_mult_r o0 o1 o2 (LT: Ord.lt o1 o2) (POS: Ord.lt Ord.O o0)
      :
      Ord.lt (mult o0 o1) (mult o0 o2).
    Proof.
      eapply Ord.S_supremum in LT.
      eapply Ord.lt_le_lt.
      2: { eapply le_mult_r. eapply LT. }
      eapply Ord.lt_eq_lt.
      { eapply mult_S. }
      eapply Hessenberg.add_lt_r. auto.
    Qed.

    Lemma mult_O_l o: Ord.eq (mult Ord.O o) Ord.O.
    Proof.
      induction o. etransitivity.
      { eapply mult_build. }
      { split.
        - eapply Ord.join_supremum. i.
          transitivity (mult Ord.O (os a)); auto.
          { eapply Hessenberg.add_O_l. }
          { eapply H. }
        - eapply Ord.O_bot. }
    Qed.

    Lemma mult_1_r o: Ord.eq (mult o (Ord.S Ord.O)) o.
    Proof.
      etransitivity.
      { eapply mult_S. }
      etransitivity.
      { eapply Hessenberg.eq_add_r. eapply mult_O_r. }
      eapply Hessenberg.add_O_r.
    Qed.

    Lemma mult_1_l o: Ord.eq (mult (Ord.S Ord.O) o) o.
    Proof.
      transitivity (Ord.orec Ord.O Ord.S o).
      2: { symmetry. eapply Ord.orec_of_S. }
      split.
      { eapply Ord.orec_mon.
        { reflexivity. }
        { i. etransitivity.
          { eapply Hessenberg.add_S_l. }
          { apply Ord.le_S. transitivity o0; auto.
            eapply Hessenberg.add_O_l.
          }
        }
      }
      { eapply Ord.orec_mon.
        { reflexivity. }
        { i. etransitivity.
          { apply Ord.le_S. eapply LE. }
          transitivity (Ord.S (Hessenberg.add Ord.O o1)); auto.
          { apply Ord.le_S. eapply Hessenberg.add_O_l. }
          { eapply Hessenberg.add_S_l. }
        }
      }
    Qed.

    Global Program Instance mult_eq_proper: Proper (Ord.eq ==> Ord.eq ==> Ord.eq) (mult).
    Next Obligation.
      ii.
      etransitivity.
      - eapply eq_mult_l; eauto.
      - eapply eq_mult_r; eauto.
    Qed.

    Global Program Instance add_le_proper: Proper (Ord.le ==> Ord.le ==> Ord.le) (mult).
    Next Obligation.
      ii.
      etransitivity.
      - eapply le_mult_l; eauto.
      - eapply le_mult_r; eauto.
    Qed.

    Lemma mult_dist o0 o1 o2: Ord.eq (mult o0 (Hessenberg.add o1 o2)) (Hessenberg.add (mult o0 o1) (mult o0 o2)).
    Proof.
      destruct o0. revert o1 o2.
      eapply (double_well_founded_induction Ord.lt_well_founded Ord.lt_well_founded).
      i. destruct a1 as [X1 os1], b1 as [X2 os2]. split.
      { etransitivity.
        { eapply eq_mult_r. symmetry. eapply Hessenberg.add_red. }
        etransitivity.
        2: { rewrite mult_build. rewrite mult_build. reflexivity. }
        rewrite mult_union.
        eapply Ord.union_spec.
        { rewrite mult_build.
          eapply Ord.join_supremum. i.
          rewrite IHR.
          2:{ eapply Ord.build_upperbound. }
          rewrite mult_build.
          rewrite Hessenberg.add_comm.
          rewrite Hessenberg.add_assoc.
          eapply Hessenberg.le_add_r.
          rewrite Hessenberg.add_comm.
          eapply (@Ord.join_upperbound _ (fun a0 => Hessenberg.add (Ord.build os) (mult (Ord.build os) (os2 a0)))).
        }
        { rewrite mult_build.
          eapply Ord.join_supremum. i.
          rewrite IHL.
          2:{ eapply Ord.build_upperbound. }
          rewrite mult_build.
          rewrite <- Hessenberg.add_assoc.
          eapply Hessenberg.le_add_l.
          eapply (@Ord.join_upperbound _ (fun a0 => Hessenberg.add (Ord.build os) (mult (Ord.build os) (os1 a0)))).
        }
      }
      { rewrite Hessenberg.add_red. rewrite mult_union.
        rewrite mult_build.
        rewrite mult_build.
        rewrite mult_build.
        rewrite mult_build.
        rewrite <- mult_build.
        rewrite <- mult_build.
        transitivity
          (Ord.union
             (Ord.join
                (fun a => Ord.build os ⊕ mult (Ord.build os) (Ord.build os1) ⊕ mult (Ord.build os) (os2 a)))
             (Ord.join
                (fun a => Ord.build os ⊕ mult (Ord.build os) (Ord.build os1) ⊕ mult (Ord.build os) (os1 a))))%ord.
        {
          (* please... somebody help me *)
    Admitted.

    Lemma mult_assoc o0 o1 o2: Ord.eq (mult (mult o0 o1) o2) (mult o0 (mult o1 o2)).
    Proof.
      revert o0 o1. induction o2. i. etransitivity.
      { eapply mult_build. } etransitivity.
      2: {
        eapply eq_mult_r; auto.
        { symmetry. eapply mult_build. }
      }
      etransitivity.
      2: { symmetry. eapply mult_join. }
      split.
      { eapply Ord.le_join. i. exists a0.
        etransitivity.
        { eapply Hessenberg.le_add_r. eapply H. }
        { eapply mult_dist. }
      }
      { eapply Ord.le_join. i. exists a0.
        etransitivity.
        { eapply mult_dist. }
        { eapply Hessenberg.le_add_r. eapply H. }
      }
    Qed.
  End MULT.
End Jacobsthal.

Global Opaque Jacobsthal.mult.

Infix "×" := Jacobsthal.mult (at level 80, right associativity) : ord_scope.
