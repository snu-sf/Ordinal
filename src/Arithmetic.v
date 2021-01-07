From Ordinal Require Import sflib Basics.
From Ordinal Require Export Ordinal.

Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms. (* TODO: Use Morphisms *)

Set Implicit Arguments.
Set Primitive Projections.

Module OrdArith.
  Section ARITHMETIC.
    Let flip A B C (f: A -> B -> C): B -> A -> C := fun b a => f a b.

    Section ADD.
      Definition add (o0: Ord.t): forall (o1: Ord.t), Ord.t := Ord.orec o0 Ord.S.

      Let _S_le o: Ord.le o (Ord.S o).
      Proof.
        eapply Ord.S_le.
      Qed.

      Let _le_S o0 o1 (LE: Ord.le o0 o1): Ord.le (Ord.S o0) (Ord.S o1).
      Proof.
        apply Ord.le_S. auto.
      Qed.

      Lemma add_base_l o0 o1: Ord.le o0 (add o0 o1).
      Proof.
        eapply Ord.orec_le_base; auto.
      Qed.

      Lemma add_base_r o0 o1: Ord.le o1 (add o0 o1).
      Proof.
        transitivity (Ord.orec Ord.O Ord.S o1).
        { eapply Ord.orec_of_S. }
        { eapply Ord.orec_mon; auto. eapply Ord.O_bot. }
      Qed.

      Lemma add_O_r o: Ord.eq (add o Ord.O) o.
      Proof.
        eapply (@Ord.orec_O o Ord.S); auto.
      Qed.

      Lemma add_S o0 o1: Ord.eq (add o0 (Ord.S o1)) (Ord.S (add o0 o1)).
      Proof.
        eapply (@Ord.orec_S o0 Ord.S); auto.
      Qed.

      Lemma add_join o A (os: A -> Ord.t):
        Ord.eq (add o (Ord.join os)) (Ord.union o (Ord.join (fun a => add o (os a)))).
      Proof.
        eapply (@Ord.orec_join o Ord.S); eauto.
      Qed.

      Lemma add_join_inhabited o A (os: A -> Ord.t)
            (INHABITED: inhabited A):
        Ord.eq (add o (Ord.join os)) (Ord.join (fun a => add o (os a))).
      Proof.
        eapply (@Ord.orec_join_inhabited o Ord.S); eauto.
      Qed.

      Lemma add_build o A (os: A -> Ord.t)
        :
          Ord.eq (add o (Ord.build os)) (Ord.union o (Ord.join (fun a => Ord.S (add o (os a))))).
      Proof.
        eapply Ord.orec_build.
      Qed.

      Lemma add_union o0 o1 o2
        :
          Ord.eq (add o0 (Ord.union o1 o2)) (Ord.union (add o0 o1) (add o0 o2)).
      Proof.
        eapply Ord.orec_union; auto.
      Qed.

      Lemma le_add_r o0 o1 o2 (LE: Ord.le o1 o2)
        :
          Ord.le (add o0 o1) (add o0 o2).
      Proof.
        eapply Ord.le_orec; auto.
      Qed.

      Lemma lt_add_r o0 o1 o2 (LT: Ord.lt o1 o2)
        :
          Ord.lt (add o0 o1) (add o0 o2).
      Proof.
        eapply Ord.S_supremum in LT.
        eapply Ord.lt_le_lt.
        2: { eapply le_add_r. eapply LT. }
        eapply Ord.lt_eq_lt.
        { eapply add_S. }
        eapply Ord.S_lt.
      Qed.

      Lemma eq_add_r o0 o1 o2 (EQ: Ord.eq o1 o2)
        :
          Ord.eq (add o0 o1) (add o0 o2).
      Proof.
        split.
        - eapply le_add_r; eauto. eapply EQ.
        - eapply le_add_r; eauto. eapply EQ.
      Qed.

      Lemma le_add_l o0 o1 o2 (LE: Ord.le o0 o1)
        :
          Ord.le (add o0 o2) (add o1 o2).
      Proof.
        eapply (@Ord.orec_mon o0 Ord.S o1 Ord.S); auto.
      Qed.

      Lemma eq_add_l o0 o1 o2 (EQ: Ord.eq o0 o1)
        :
          Ord.eq (add o0 o2) (add o1 o2).
      Proof.
        split.
        - eapply le_add_l; eauto. eapply EQ.
        - eapply le_add_l; eauto. eapply EQ.
      Qed.

      Lemma add_O_l o: Ord.eq (add Ord.O o) o.
      Proof.
        induction o. etransitivity.
        { eapply add_build. }
        { split.
          - eapply Ord.union_spec.
            + eapply Ord.O_bot.
            + eapply Ord.join_supremum. i. eapply Ord.S_supremum.
              eapply Ord.eq_lt_lt.
              * eapply H.
              * eapply Ord.build_upperbound.
          - eapply Ord.build_supremum. i.
            eapply (@Ord.lt_le_lt (Ord.join (fun a0 => Ord.S (Ord.orec Ord.O Ord.S (os a0))))).
            2: { eapply Ord.union_r. }
            eapply Ord.eq_lt_lt.
            { symmetry. eapply H. }
            eapply Ord.lt_le_lt.
            { eapply Ord.S_lt. }
            { eapply (@Ord.join_upperbound _ (fun a0 => Ord.S (Ord.orec Ord.O Ord.S (os a0)))). }
        }
      Qed.

      Lemma add_assoc o0 o1 o2: Ord.eq (add (add o0 o1) o2) (add o0 (add o1 o2)).
      Proof.
        revert o0 o1. induction o2. i. etransitivity.
        { eapply add_build. } etransitivity.
        2: {
          eapply eq_add_r; auto.
          { symmetry. eapply add_build. }
        }
        etransitivity.
        2: { symmetry. eapply add_union; auto. }
        split.
        { eapply Ord.union_spec.
          { eapply Ord.union_l. }
          { eapply Ord.join_supremum. i. etransitivity.
            { apply Ord.le_S. eapply H. }
            etransitivity.
            2: { eapply Ord.union_r. }
            etransitivity.
            2: {
              eapply le_add_r.
              eapply (@Ord.join_upperbound _ (fun a0 : A => Ord.S (add o1 (os a0))) a).
            }
            eapply add_S.
          }
        }
        { eapply Ord.union_spec.
          { eapply Ord.union_l. }
          etransitivity.
          { eapply add_join. }
          eapply Ord.union_spec.
          { etransitivity.
            { eapply add_base_l. }
            { eapply Ord.union_l. }
          }
          etransitivity.
          2: { eapply Ord.union_r. }
          eapply Ord.le_join. i. exists a0.
          etransitivity.
          { eapply add_S. }
          { apply Ord.le_S. eapply H. }
        }
      Qed.

      Lemma add_lt_l o0 o1 (LT: Ord.lt Ord.O o1): Ord.lt o0 (add o0 o1).
      Proof.
        eapply Ord.S_supremum in LT. eapply (@Ord.lt_le_lt (add o0 (Ord.S Ord.O))).
        { eapply Ord.lt_eq_lt.
          { eapply add_S. }
          eapply Ord.lt_le_lt.
          { eapply Ord.S_lt. }
          eapply Ord.le_S. eapply add_base_l.
        }
        { eapply le_add_r. auto. }
      Qed.
    End ADD.

    Section RECAPP.
      Variable D: Type.
      Variable next: D -> D.
      Variable djoin: forall (A: Type) (ds: A -> D), D.

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

      Let drec_wf base (WF: wf base) o: wf (Ord.rec base next djoin o).
      Proof.
        eapply (Ord.rec_wf base next djoin dle wf); auto.
      Qed.

      Let drec_rec_wf base (WF: wf base) o0 o1:
        wf (Ord.rec (Ord.rec base next djoin o0) next djoin o1).
      Proof.
        eapply (Ord.rec_wf _ next djoin dle wf); auto.
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

      Let drec_red base A (os: A -> Ord.t):
        Ord.rec base next djoin (Ord.build os) =
        dunion base (djoin (fun a => next (Ord.rec base next djoin (os a)))).
      Proof.
        eapply Ord.rec_red.
      Qed.

      Lemma rec_app base o0 o1 (WF: wf base):
        deq (Ord.rec base next djoin (add o0 o1)) (Ord.rec (Ord.rec base next djoin o0) next djoin o1).
      Proof.
        induction o1.

        eapply (@deq_transitive (dunion (Ord.rec base next djoin o0) (dunion base (djoin (fun a => next (Ord.rec (Ord.rec base next djoin o0) next djoin (os a))))))); auto.
        { eapply dunion_wf; auto. }
        { eapply (@deq_transitive (Ord.rec base next djoin (Ord.union o0 (Ord.join (fun a : A => Ord.S (add o0 (os a))))))); auto.
          { eapply dunion_wf; auto. }
          { eapply (@Ord.eq_rec _ base next djoin dle wf); auto.
            symmetry. eapply add_build. }
          eapply (@deq_transitive (dunion (Ord.rec base next djoin o0) (Ord.rec base next djoin (Ord.join (fun a : A => Ord.S (add o0 (os a))))))); auto.
          { eapply dunion_wf; auto. }
          { eapply (Ord.rec_union base next djoin dle wf); auto. }
          eapply dunion_eq; auto.
          { split; apply dle_reflexive; auto. }
          { eapply (@deq_transitive (dunion base (djoin (fun a : A => Ord.rec base next djoin ((fun a0 : A => Ord.S (add o0 (os a0))) a))))); auto.
            { eapply (Ord.rec_join base next djoin dle wf); auto. }
            { eapply dunion_eq; auto.
              { split; auto. }
              { eapply djoin_eq; auto. i.
                eapply (@deq_transitive (next (Ord.rec base next djoin (add o0 (os a))))); auto.
                eapply (Ord.rec_S base next djoin dle wf); auto.
              }
            }
          }
        }

        rewrite drec_red. split.
        { eapply dunion_supremum; auto.
          eapply dunion_supremum; auto.
          eapply (@dle_transitive (Ord.rec base next djoin o0)); auto.
          eapply (Ord.rec_le_base base next djoin dle wf); auto.
        }
        { eapply dunion_le; auto. }
      Qed.
    End RECAPP.

    Section ORECAPP.
      Variable next: Ord.t -> Ord.t.
      Hypothesis next_le: forall o, Ord.le o (next o).
      Hypothesis next_mon: forall o0 o1 (LE: Ord.le o0 o1), Ord.le (next o0) (next o1).

      Lemma orec_app base o0 o1:
        Ord.eq (Ord.orec base next (add o0 o1)) (Ord.orec (Ord.orec base next o0) next o1).
      Proof.
        eapply (rec_app next Ord.join Ord.le (fun _ => True)); auto.
        { i. reflexivity. }
        { i. transitivity d1; auto. }
        { i. eapply Ord.join_upperbound. }
        { i. eapply Ord.join_supremum. auto. }
      Qed.
    End ORECAPP.


    Section MULT.
      Definition mult (o0: Ord.t): forall (o1: Ord.t), Ord.t := Ord.orec Ord.O (flip add o0).

      Lemma mult_gen_le o0 o1: Ord.le o1 (flip add o0 o1).
      Proof.
        eapply add_base_l.
      Qed.
      Let _mult_gen_le := mult_gen_le.

      Lemma mult_gen_mon o o0 o1 (LE: Ord.le o0 o1): Ord.le (flip add o o0) (flip add o o1).
      Proof.
        eapply le_add_l. auto.
      Qed.
      Let _mult_gen_mon := mult_gen_mon.

      Lemma mult_O_r o: Ord.eq (mult o Ord.O) Ord.O.
      Proof.
        eapply (@Ord.orec_O Ord.O (flip add o)); auto.
      Qed.

      Lemma mult_S o0 o1: Ord.eq (mult o0 (Ord.S o1)) (add (mult o0 o1) o0).
      Proof.
        eapply (@Ord.orec_S Ord.O (flip add o0)); auto.
      Qed.

      Lemma mult_join o A (os: A -> Ord.t):
        Ord.eq (mult o (Ord.join os)) (Ord.join (fun a => mult o (os a))).
      Proof.
        transitivity (Ord.union Ord.O (Ord.join (fun a => mult o (os a)))).
        { eapply (@Ord.orec_join Ord.O (flip add _)); eauto. }
        { eapply Ord.union_max. eapply Ord.O_bot. }
      Qed.

      Lemma mult_build o A (os: A -> Ord.t)
        :
          Ord.eq (mult o (Ord.build os)) (Ord.join (fun a => add (mult o (os a)) o)).
      Proof.
        transitivity (Ord.union Ord.O (Ord.join (fun a => add (mult o (os a)) o))).
        { eapply (@Ord.orec_build Ord.O (flip add _)); eauto. }
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
        eapply (@Ord.orec_mon Ord.O (flip add o0) Ord.O (flip add o1)); auto.
        { reflexivity. }
        { i. unfold flip. transitivity (add o4 o0).
          { eapply le_add_l; auto. }
          { eapply le_add_r; auto. }
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
        eapply add_lt_l. auto.
      Qed.

      Lemma mult_O_l o: Ord.eq (mult Ord.O o) Ord.O.
      Proof.
        induction o. etransitivity.
        { eapply mult_build. }
        { split.
          - eapply Ord.join_supremum. i.
            transitivity (mult Ord.O (os a)); auto.
            { eapply add_O_r. }
            { eapply H. }
          - eapply Ord.O_bot. }
      Qed.

      Lemma mult_1_r o: Ord.eq (mult o (Ord.S Ord.O)) o.
      Proof.
        unfold Ord.from_nat. etransitivity.
        { eapply mult_S. }
        etransitivity.
        { eapply eq_add_l. eapply mult_O_r. }
        eapply add_O_l.
      Qed.

      Lemma mult_1_l o: Ord.eq (mult (Ord.S Ord.O) o) o.
      Proof.
        unfold Ord.from_nat. transitivity (Ord.orec Ord.O Ord.S o).
        2: { symmetry. eapply Ord.orec_of_S. }
        split.
        { eapply Ord.orec_mon.
          { reflexivity. }
          { i. unfold flip. etransitivity.
            { eapply add_S. }
            { apply Ord.le_S. transitivity o0; auto.
              eapply add_O_r.
            }
          }
        }
        { eapply Ord.orec_mon.
          { reflexivity. }
          { i. unfold flip. etransitivity.
            { apply Ord.le_S. eapply LE. }
            transitivity (Ord.S (add o1 Ord.O)); auto.
            { apply Ord.le_S. eapply add_O_r. }
            { eapply add_S. }
          }
        }
      Qed.

      Lemma mult_dist o0 o1 o2: Ord.eq (mult o0 (add o1 o2)) (add (mult o0 o1) (mult o0 o2)).
      Proof.
        revert o0 o1. induction o2. i. etransitivity.
        { eapply eq_mult_r. eapply add_build. }
        etransitivity.
        2: { eapply eq_add_r. symmetry. eapply mult_build. }
        etransitivity.
        { eapply mult_union. }
        etransitivity.
        { eapply Ord.eq_union.
          { reflexivity. }
          { eapply mult_join. }
        }
        etransitivity.
        2: { symmetry. eapply add_join. }
        eapply Ord.eq_union.
        { reflexivity. } split.
        { eapply Ord.le_join. i. exists a0.
          etransitivity.
          { eapply mult_S. }
          etransitivity.
          { eapply eq_add_l. symmetry. eapply H. }
          eapply add_assoc.
        }
        { eapply Ord.le_join. i. exists a0.
          etransitivity.
          { eapply add_assoc. }
          etransitivity.
          { eapply eq_add_l. eapply H. }
          eapply mult_S.
        }
      Qed.

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
          { eapply le_add_l. eapply H. }
          { eapply mult_dist. }
        }
        { eapply Ord.le_join. i. exists a0.
          etransitivity.
          { eapply mult_dist. }
          { eapply le_add_l. eapply H. }
        }
      Qed.

      Lemma mult_le_l o0 o1 (POS: Ord.lt Ord.O o0): Ord.le o1 (mult o1 o0).
      Proof.
        eapply Ord.S_supremum in POS. etransitivity.
        2: { eapply le_mult_r in POS. eauto. }
        eapply mult_1_r.
      Qed.

      Lemma mult_lt_l o0 o1 (POS: Ord.lt Ord.O o1)
            (TWO: Ord.lt (Ord.S Ord.O) o0): Ord.lt o1 (mult o1 o0).
      Proof.
        eapply Ord.S_supremum in TWO. eapply (@Ord.lt_le_lt (mult o1 (Ord.S (Ord.S Ord.O)))).
        { eapply Ord.lt_eq_lt.
          { eapply mult_S. }
          eapply Ord.lt_eq_lt.
          { eapply eq_add_l. eapply mult_S. }
          eapply Ord.lt_eq_lt.
          { eapply add_assoc. }
          eapply Ord.lt_le_lt.
          2: { eapply add_base_r. }
          eapply add_lt_l. apply POS.
        }
        { eapply le_mult_r. auto. }
      Qed.

    End MULT.


    Section EXPN.
      Definition expn (o0: Ord.t): forall (o1: Ord.t), Ord.t := Ord.orec (Ord.S Ord.O) (flip mult o0).

      Let expn_gen_mon o o0 o1 (LE: Ord.le o0 o1):
        Ord.le (flip mult o o0) (flip mult o o1).
      Proof.
        eapply le_mult_l. auto.
      Qed.

      Section BASE.
        Variable base: Ord.t.

        Lemma expn_O o: Ord.eq (expn o Ord.O) (Ord.S Ord.O).
        Proof.
          eapply Ord.orec_O; auto.
        Qed.

        Lemma expn_pos o: Ord.lt Ord.O (expn base o).
        Proof.
          eapply Ord.lt_le_lt.
          { eapply Ord.S_lt. }
          { eapply Ord.orec_le_base. auto. }
        Qed.

        Section POSITIVE.
          Hypothesis POS: Ord.lt Ord.O base.

          Let expn_gen_le o: Ord.le o (flip mult base o).
          Proof.
            eapply mult_le_l; auto.
          Qed.

          Lemma expn_S o:
            Ord.eq (expn base (Ord.S o)) (mult (expn base o) base).
          Proof.
            eapply Ord.orec_S; auto.
          Qed.

          Lemma le_expn_r o0 o1 (LE: Ord.le o0 o1):
            Ord.le (expn base o0) (expn base o1).
          Proof.
            eapply Ord.le_orec; auto.
          Qed.

          Lemma eq_expn_r o0 o1 (EQ: Ord.eq o0 o1):
            Ord.eq (expn base o0) (expn base o1).
          Proof.
            eapply Ord.eq_orec; auto.
          Qed.

          Lemma expn_join A (os: A -> Ord.t):
            Ord.eq (expn base (Ord.join os)) (Ord.union (Ord.S Ord.O) (Ord.join (fun a => expn base (os a)))).
          Proof.
            eapply Ord.orec_join; auto.
          Qed.

          Lemma expn_join_inhabited A (os: A -> Ord.t)
                (INHABITED: inhabited A):
            Ord.eq (expn base (Ord.join os)) (Ord.join (fun a => expn base (os a))).
          Proof.
            eapply Ord.orec_join_inhabited; auto.
          Qed.

          Lemma expn_build A (os: A -> Ord.t):
            Ord.eq (expn base (Ord.build os)) (Ord.union (Ord.S Ord.O) (Ord.join (fun a => mult (expn base (os a)) base))).
          Proof.
            eapply Ord.orec_build.
          Qed.

          Lemma expn_union o0 o1
            :
              Ord.eq (expn base (Ord.union o0 o1)) (Ord.union (expn base o0) (expn base o1)).
          Proof.
            eapply Ord.orec_union; auto.
          Qed.

          Lemma expn_1_r: Ord.eq (expn base (Ord.S Ord.O)) base.
          Proof.
            etransitivity.
            { eapply expn_S. }
            etransitivity.
            { eapply eq_mult_l. eapply expn_O. }
            eapply mult_1_l.
          Qed.

          Lemma expn_add o0 o1:
            Ord.eq (expn base (add o0 o1)) (mult (expn base o0) (expn base o1)).
          Proof.
            revert o0. induction o1. i. etransitivity.
            { eapply eq_expn_r. eapply add_build. }
            etransitivity.
            { eapply expn_union. }
            etransitivity.
            2: { eapply eq_mult_r. symmetry. eapply expn_build. }
            etransitivity.
            2: { symmetry. eapply mult_union. }
            etransitivity.
            { eapply Ord.eq_union.
              { reflexivity. }
              eapply expn_join.
            }
            etransitivity.
            { eapply Ord.union_assoc. }
            eapply Ord.eq_union.
            { etransitivity.
              { eapply Ord.union_comm. }
              { etransitivity.
                2: { symmetry. eapply mult_1_r. }
                { eapply Ord.union_max. eapply Ord.S_supremum. eapply expn_pos. }
              }
            }
            etransitivity.
            2: { symmetry. eapply mult_join. }
            eapply Ord.eq_join. i.
            etransitivity.
            { eapply expn_S. }
            etransitivity.
            2: { eapply mult_assoc. }
            eapply eq_mult_l.
            eapply H.
          Qed.
        End POSITIVE.

        Lemma lt_expn_r (TWO: Ord.lt (Ord.S Ord.O) base) o0 o1 (LT: Ord.lt o0 o1):
          Ord.lt (expn base o0) (expn base o1).
        Proof.
          assert (POS: Ord.lt Ord.O base).
          { eapply Ord.le_lt_lt; eauto. eapply Ord.S_le. }
          eapply (@Ord.lt_le_lt (expn base (Ord.S o0))).
          { eapply Ord.lt_eq_lt.
            { eapply expn_S. auto. }
            { eapply mult_lt_l; auto. eapply expn_pos. }
          }
          { eapply le_expn_r. eapply Ord.S_supremum. auto. }
        Qed.
      End BASE.

      Lemma expn_1_l o: Ord.eq (expn (Ord.S Ord.O) o) (Ord.S Ord.O).
      Proof.
        induction o. etransitivity.
        { eapply expn_build. }
        etransitivity.
        { eapply Ord.union_comm. }
        eapply Ord.union_max. eapply Ord.join_supremum.
        i. eapply Ord.eq_le_le.
        { eapply mult_1_r. }
        eapply H.
      Qed.

      Lemma le_expn_l o0 o1 o2 (LE: Ord.le o0 o1):
        Ord.le (expn o0 o2) (expn o1 o2).
      Proof.
        eapply Ord.orec_mon.
        { reflexivity. }
        { i. transitivity (mult o3 o1).
          { eapply le_mult_r. auto. }
          { eapply le_mult_l. auto. }
        }
      Qed.

      Lemma eq_expn_l o0 o1 o2 (EQ: Ord.eq o0 o1):
        Ord.eq (expn o0 o2) (expn o1 o2).
      Proof.
        split; eapply le_expn_l; apply EQ.
      Qed.

      Lemma expn_mult o0 (POS: Ord.lt Ord.O o0) o1 o2:
        Ord.eq (expn o0 (mult o1 o2)) (expn (expn o0 o1) o2).
      Proof.
        induction o2.
        etransitivity.
        { eapply eq_expn_r. eapply mult_build. }
        etransitivity.
        { eapply expn_join. auto. }
        etransitivity.
        2: { symmetry. eapply expn_build. }
        eapply Ord.eq_union.
        { reflexivity. }
        eapply Ord.eq_join. i.
        etransitivity.
        { eapply expn_add. auto. }
        eapply eq_mult_l. auto.
      Qed.
    End EXPN.

    Section FROMNAT.
      Lemma le_from_nat n0 n1 (LE: Peano.le n0 n1):
        Ord.le (Ord.from_nat n0) (Ord.from_nat n1).
      Proof.
        induction LE.
        { reflexivity. }
        { etransitivity; eauto. ss. eapply Ord.S_le. }
      Qed.

      Lemma lt_from_nat n0 n1 (LT: Peano.lt n0 n1):
        Ord.lt (Ord.from_nat n0) (Ord.from_nat n1).
      Proof.
        eapply Ord.lt_le_lt.
        2: { eapply le_from_nat. eapply LT. }
        { ss. eapply Ord.S_lt. }
      Qed.

      Lemma add_from_nat n0 n1:
        Ord.eq (Ord.from_nat (n0 + n1)) (add (Ord.from_nat n0) (Ord.from_nat n1)).
      Proof.
        induction n1; ss.
        { rewrite PeanoNat.Nat.add_0_r.
          symmetry. eapply add_O_r. }
        { rewrite PeanoNat.Nat.add_succ_r. ss.
          etransitivity.
          { eapply Ord.eq_S. eapply IHn1. }
          symmetry. eapply add_S.
        }
      Qed.

      Lemma mult_from_nat n0 n1:
        Ord.eq (Ord.from_nat (n0 * n1)) (mult (Ord.from_nat n0) (Ord.from_nat n1)).
      Proof.
        induction n1; ss.
        { rewrite PeanoNat.Nat.mul_0_r.
          symmetry. eapply mult_O_r. }
        { rewrite PeanoNat.Nat.mul_succ_r.
          etransitivity.
          { eapply add_from_nat. }
          etransitivity.
          { eapply eq_add_l. eapply IHn1. }
          symmetry. eapply mult_S.
        }
      Qed.

      Lemma expn_from_nat n0 (POS: 0 < n0) n1:
        Ord.eq (Ord.from_nat (Nat.pow n0 n1)) (expn (Ord.from_nat n0) (Ord.from_nat n1)).
      Proof.
        induction n1; ss.
        { symmetry. eapply expn_O. }
        { etransitivity.
          { rewrite PeanoNat.Nat.mul_comm. eapply mult_from_nat. }
          etransitivity.
          { eapply eq_mult_l. eapply IHn1. }
          symmetry. eapply expn_S.
          eapply (@lt_from_nat 0 n0). auto.
        }
      Qed.
    End FROMNAT.
  End ARITHMETIC.
End OrdArith.
