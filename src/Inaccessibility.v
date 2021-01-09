From Ordinal Require Import sflib Basics.
From Ordinal Require Export Ordinal Arithmetic.

Require Import ChoiceFacts.

Set Implicit Arguments.
Set Primitive Projections.

Section INACCESSIBLE.
  Let flip A B C (f: A -> B -> C): B -> A -> C := fun b a => f a b.

  Record inaccessible (X: Type) (base: Ord.t) (next: Ord.t -> Ord.t) (k: Ord.t): Prop :=
    mk_inaccessible
      { inaccessible_base: Ord.lt base k;
        inaccessible_next: forall o (LT: Ord.lt o k), Ord.lt (next o) k;
        inaccessible_join: forall (os: X -> Ord.t) (LT: forall a, Ord.lt (os a) k),
            Ord.lt (Ord.join os) k;
        inaccessible_union: forall o0 o1 (LT0: Ord.lt o0 k) (LT1: Ord.lt o1 k),
            Ord.lt (Ord.union o0 o1) k;
      }.

  Lemma inaccessible_mon X0 X1 base0 base1 next0 next1 k
        (SURJ: exists (f: X1 -> X0), forall x0, exists x1, f x1 = x0)
        (BASE: Ord.lt base0 k)
        (NEXT: forall o (LT: Ord.lt o k), Ord.le (next0 o) (next1 o))
        (INACCESSIBLE: inaccessible X1 base1 next1 k)
    :
      inaccessible X0 base0 next0 k.
  Proof.
    econs.
    { des; auto. }
    { i. eapply Ord.le_lt_lt; eauto.
      eapply INACCESSIBLE.(inaccessible_next). auto. }
    { i. des. eapply (@Ord.le_lt_lt (Ord.join (fun (x1: X1) => os (f x1)))).
      { eapply Ord.le_join. i. specialize (SURJ a0).
        des. subst. eexists. reflexivity. }
      { eapply INACCESSIBLE.(inaccessible_join). auto. }
    }
    { eapply INACCESSIBLE. }
  Qed.

  Record ginaccessible (X: Type) (base: Ord.t) (next: Ord.t -> Ord.t) (k: Ord.t): Prop :=
    mk_ginaccessible
      { ginaccessible_base: Ord.lt base k;
        ginaccessible_next: forall o (LT: Ord.lt o k), Ord.lt (next o) k;
        ginaccessible_join: forall (P: X -> Prop) (os: sig P -> Ord.t) (LT: forall a, Ord.lt (os a) k),
            Ord.lt (Ord.join os) k;
        ginaccessible_union: forall o0 o1 (LT0: Ord.lt o0 k) (LT1: Ord.lt o1 k),
            Ord.lt (Ord.union o0 o1) k;
      }.

  Lemma ginaccessible_inaccessible X base next k
        (INACCESSIBLE: ginaccessible X base next k)
    :
      inaccessible X base next k.
  Proof.
    econs; try by apply INACCESSIBLE. i.
    hexploit INACCESSIBLE.(ginaccessible_join).
    { instantiate (1:=fun (p: sig (fun _ => True)) => os (proj1_sig p)). ss. }
    i. eapply Ord.le_lt_lt; eauto.
    eapply Ord.le_join. i. exists (exist _ a0 I). reflexivity.
  Qed.

  Section TREE.
    Variable X: Type.

    Inductive tree: Type :=
    | tree_O
    | tree_S (tr: tree)
    | tree_join (trs: X -> tree)
    | tree_union (tr0 tr1: tree)
    .

    Definition tree_lt (tr0 tr1: tree): Prop :=
      match tr1 with
      | tree_O => False
      | tree_S tr => tr0 = tr
      | tree_join trs => exists x, tr0 = trs x
      | tree_union trl trr => tr0 = trl \/ tr0 = trr
      end.

    Lemma tree_lt_well_founded: well_founded tree_lt.
    Proof.
      ii. induction a.
      { econs. ii. ss. }
      { econs. i. ss. subst. auto. }
      { econs. i. ss. des. subst. auto. }
      { econs. i. ss. des; subst; auto. }
    Qed.

    Lemma tree_O_O: Ord.eq (Ord.from_wf tree_lt_well_founded tree_O) Ord.O.
    Proof.
      Local Transparent Ord.from_wf Ord.from_acc Ord.O.
      split.
      { unfold Ord.from_wf. destruct (tree_lt_well_founded tree_O).
        ss. econs. i. destruct a0. ss. }
      { eapply Ord.O_bot. }
    Qed.

    Lemma tree_S_S tr:
      Ord.eq (Ord.from_wf tree_lt_well_founded (tree_S tr)) (Ord.S (Ord.from_wf tree_lt_well_founded tr)).
    Proof.
      Local Transparent Ord.from_wf Ord.from_acc Ord.O Ord.S.
      split.
      { unfold Ord.from_wf at 1. destruct (tree_lt_well_founded (tree_S tr)).
        ss. econs. i. destruct a0. ss. subst. exists tt.
        ss. eapply Ord.same_acc_le.
      }
      { eapply Ord.S_supremum. eapply Ord.from_wf_lt. ss. }
    Qed.

    Lemma tree_join_build (trs: X -> tree):
      Ord.eq (Ord.from_wf tree_lt_well_founded (tree_join trs)) (Ord.build (fun x => Ord.from_wf tree_lt_well_founded (trs x))).
    Proof.
      split.
      { unfold Ord.from_wf at 1. destruct (tree_lt_well_founded (tree_join trs)).
        ss. econs. i. destruct a0. des. ss. subst. exists x0.
        ss. eapply Ord.same_acc_le.
      }
      { eapply Ord.build_supremum. i. eapply Ord.from_wf_lt. ss. eauto. }
    Qed.

    Lemma tree_union_union_le (tr0 tr1: tree):
      Ord.le (Ord.from_wf tree_lt_well_founded (tree_union tr0 tr1)) (Ord.S (Ord.union (Ord.from_wf tree_lt_well_founded tr0) (Ord.from_wf tree_lt_well_founded tr1))).
    Proof.
      unfold Ord.from_wf at 1. destruct (tree_lt_well_founded (tree_union tr0 tr1)).
      ss. econs. i. destruct a0. ss. exists tt. ss. des; subst.
      { transitivity (Ord.from_wf tree_lt_well_founded tr0).
        { eapply Ord.same_acc_le. }
        { eapply Ord.union_l. }
      }
      { transitivity (Ord.from_wf tree_lt_well_founded tr1).
        { eapply Ord.same_acc_le. }
        { eapply Ord.union_r. }
      }
    Qed.

    Lemma tree_union_union_le_rev (tr0 tr1: tree):
      Ord.le (Ord.union (Ord.from_wf tree_lt_well_founded tr0) (Ord.from_wf tree_lt_well_founded tr1)) (Ord.from_wf tree_lt_well_founded (tree_union tr0 tr1)).
    Proof.
      eapply Ord.union_spec.
      { eapply Ord.lt_le. eapply Ord.from_wf_lt. ss. auto. }
      { eapply Ord.lt_le. eapply Ord.from_wf_lt. ss. auto. }
    Qed.

    Definition tree_top := Ord.from_wf_set tree_lt_well_founded.

    Lemma inaccessible_rec_inaccessible (base0: Ord.t) (next: Ord.t -> Ord.t)
          (NEXTLE: forall o, Ord.le o (next o))
          (NEXTMON: forall o0 o1 (LE: Ord.le o0 o1), Ord.le (next o0) (next o1))
          (INACCESSIBLE: inaccessible X base0 next tree_top)
          base1
          (BASE1: Ord.lt base1 tree_top)
      :
        inaccessible X base0 (Ord.orec base1 next) tree_top.
    Proof.
      Local Transparent Ord.from_wf Ord.from_acc Ord.O Ord.S Ord.rec Ord.from_wf_set.
      econs; eauto.
      { eapply INACCESSIBLE. }
      2: { eapply INACCESSIBLE. }
      2: { eapply INACCESSIBLE. }
      assert (RECS: forall tr, Ord.lt (Ord.orec base1 next (Ord.from_wf tree_lt_well_founded tr)) tree_top).
      { induction tr.
        { eapply (@Ord.eq_lt_lt _ _ base1); auto.
          transitivity (Ord.orec base1 next Ord.O).
          { eapply Ord.eq_orec; auto. eapply tree_O_O. }
          { eapply Ord.orec_O; auto. }
        }
        { eapply (@Ord.eq_lt_lt _ _ (next (Ord.orec base1 next (Ord.from_wf tree_lt_well_founded tr)))).
          { transitivity (Ord.orec base1 next (Ord.S (Ord.from_wf tree_lt_well_founded tr))).
            { eapply Ord.eq_orec; auto. eapply tree_S_S. }
            { eapply Ord.orec_S; auto. }
          }
          { eapply INACCESSIBLE. auto. }
        }
        { eapply (@Ord.eq_lt_lt _ _ _).
          { etransitivity.
            { eapply Ord.eq_orec; auto. eapply tree_join_build. }
            { eapply Ord.orec_build. }
          }
          { eapply INACCESSIBLE; auto. eapply INACCESSIBLE. i.
            eapply INACCESSIBLE. auto. }
        }
        { eapply Ord.le_lt_lt.
          { eapply Ord.le_orec.
            { auto. }
            { eapply tree_union_union_le. }
          }
          eapply Ord.eq_lt_lt.
          { eapply Ord.orec_S; auto. }
          eapply INACCESSIBLE.
          eapply Ord.eq_lt_lt.
          { eapply Ord.orec_union; auto. }
          { eapply INACCESSIBLE; auto. }
        }
      }
      i. eapply Ord.lt_inv in LT. des. eapply (@Ord.le_lt_lt (Ord.orec base1 next (Ord.from_wf tree_lt_well_founded a))); auto.
      eapply Ord.le_orec; auto.
    Qed.

    Lemma tree_top_O
      :
        Ord.lt Ord.O tree_top.
    Proof.
      econs. instantiate (1:=tree_O). eapply Ord.O_bot.
    Qed.

    Lemma tree_top_S o (LT: Ord.lt o tree_top)
      :
        Ord.lt (Ord.S o) tree_top.
    Proof.
      i. eapply Ord.lt_inv in LT. des.
      econs. instantiate (1:=tree_S a).
      eapply Ord.S_supremum. eapply Ord.le_lt_lt; eauto.
      eapply Ord.from_wf_lt. ss.
    Qed.

    Lemma tree_top_union o0 o1 (LT0: Ord.lt o0 tree_top) (LT1: Ord.lt o1 tree_top)
      :
        Ord.lt (Ord.union o0 o1) tree_top.
    Proof.
      eapply Ord.lt_inv in LT0. eapply Ord.lt_inv in LT1. des.
      econs. instantiate (1:=tree_union a0 a). eapply Ord.union_spec.
      { etransitivity; eauto. eapply Ord.lt_le. eapply Ord.from_wf_lt. ss. auto. }
      { etransitivity; eauto. eapply Ord.lt_le. eapply Ord.from_wf_lt. ss. auto. }
    Qed.

    Hypothesis CHOICE: FunctionalChoice_on X tree.

    Lemma tree_top_join (os: X -> Ord.t) (LT: forall x, Ord.lt (os x) tree_top)
      :
        Ord.lt (Ord.join os) tree_top.
    Proof.
      i. hexploit (CHOICE (fun (x: X) (tr: tree) => Ord.le (os x) (Ord.from_wf tree_lt_well_founded tr))).
      { i. specialize (LT x). eapply Ord.lt_inv in LT. eauto. }
      i. des.
      econs. instantiate (1:=tree_join f).
      eapply Ord.join_supremum. i. etransitivity; eauto.
      eapply Ord.lt_le. eapply Ord.from_wf_lt. ss. eauto.
    Qed.

    Lemma tree_top_S_inaccessible
      :
        inaccessible X Ord.O Ord.S tree_top.
    Proof.
      econs.
      { eapply tree_top_O. }
      { eapply tree_top_S. }
      { eapply tree_top_join. }
      { eapply tree_top_union. }
    Qed.

    Lemma tree_top_add_inaccessible
          o (LT: Ord.lt o tree_top)
      :
        inaccessible X Ord.O (OrdArith.add o) tree_top.
    Proof.
      Local Transparent OrdArith.add.
      eapply inaccessible_rec_inaccessible; eauto.
      { i. eapply Ord.S_le. }
      { i. apply Ord.le_S. auto. }
      { eapply tree_top_S_inaccessible. }
    Qed.

    Lemma tree_top_add o0 o1 (LT0: Ord.lt o0 tree_top) (LT1: Ord.lt o1 tree_top)
      :
        Ord.lt (OrdArith.add o0 o1) tree_top.
    Proof.
      eapply tree_top_add_inaccessible; auto.
    Qed.

    Lemma tree_top_flip_add_inaccessible
          o (LT: Ord.lt o tree_top)
      :
        inaccessible X Ord.O (flip OrdArith.add o) tree_top.
    Proof.
      hexploit tree_top_add_inaccessible; eauto. i.
      econs; auto.
      { eapply Ord.le_lt_lt; eauto. eapply Ord.O_bot. }
      { i. eapply (@tree_top_add_inaccessible _ LT0).(inaccessible_next). auto. }
      { i. eapply H. auto. }
      { i. eapply H; auto. }
    Qed.

    Lemma tree_top_mult_inaccessible
          o (LT: Ord.lt o tree_top)
      :
        inaccessible X Ord.O (OrdArith.mult o) tree_top.
    Proof.
      Local Transparent OrdArith.mult.
      eapply inaccessible_rec_inaccessible; eauto.
      { i. eapply OrdArith.add_base_l. }
      { i. eapply OrdArith.le_add_l; auto. }
      { eapply tree_top_flip_add_inaccessible. auto. }
      { eapply Ord.le_lt_lt; eauto. eapply Ord.O_bot. }
    Qed.

    Lemma tree_top_mult o0 o1 (LT0: Ord.lt o0 tree_top) (LT1: Ord.lt o1 tree_top)
      :
        Ord.lt (OrdArith.mult o0 o1) tree_top.
    Proof.
      eapply tree_top_mult_inaccessible; auto.
    Qed.

    Lemma tree_top_flip_mult_inaccessible
          o (LT: Ord.lt o tree_top)
      :
        inaccessible X Ord.O (flip OrdArith.mult o) tree_top.
    Proof.
      hexploit tree_top_mult_inaccessible; eauto. i.
      econs; auto.
      { eapply Ord.le_lt_lt; eauto. eapply Ord.O_bot. }
      { i. eapply (@tree_top_mult_inaccessible _ LT0).(inaccessible_next). auto. }
      { i. eapply H. auto. }
      { i. eapply H; auto. }
    Qed.

    Lemma tree_top_expn_inaccessible
          o (POS: Ord.lt Ord.O o) (LT: Ord.lt o tree_top)
      :
        inaccessible X Ord.O (OrdArith.expn o) tree_top.
    Proof.
      Local Transparent OrdArith.expn.
      eapply inaccessible_rec_inaccessible; eauto.
      { i. unfold flip. eapply OrdArith.mult_le_l. auto. }
      { i. eapply OrdArith.le_mult_l. auto. }
      { eapply tree_top_flip_mult_inaccessible. auto. }
      { eapply tree_top_S. eapply tree_top_O. }
    Qed.

    Lemma tree_top_expn o0 o1 (LT0: Ord.lt o0 tree_top) (LT1: Ord.lt o1 tree_top)
      :
        Ord.lt (OrdArith.expn o0 o1) tree_top.
    Proof.
      eapply (@Ord.le_lt_lt (OrdArith.expn (Ord.S o0) o1)).
      { eapply OrdArith.le_expn_l. eapply Ord.S_le. }
      { eapply tree_top_expn_inaccessible; auto.
        { eapply Ord.S_pos. }
        { eapply tree_top_S. auto. }
      }
    Qed.

    Lemma tree_top_flip_expn_inaccessible
          o (LT: Ord.lt o tree_top)
      :
        inaccessible X Ord.O (flip OrdArith.expn o) tree_top.
    Proof.
      econs.
      { eapply tree_top_O. }
      { i. eapply tree_top_expn; auto. }
      { eapply tree_top_join. }
      { eapply tree_top_union. }
    Qed.
  End TREE.

  Section GTREE.
    Variable X: Type.

    Inductive gtree: Type :=
    | gtree_O
    | gtree_S (tr: gtree)
    | gtree_join (P: X -> Prop) (trs: sig P -> gtree)
    | gtree_union (tr0 tr1: gtree)
    .

    Definition gtree_lt (tr0 tr1: gtree): Prop :=
      match tr1 with
      | gtree_O => False
      | gtree_S tr => tr0 = tr
      | gtree_join trs => exists x, tr0 = trs x
      | gtree_union trl trr => tr0 = trl \/ tr0 = trr
      end.

    Lemma gtree_lt_well_founded: well_founded gtree_lt.
    Proof.
      ii. induction a.
      { econs. ii. ss. }
      { econs. i. ss. subst. auto. }
      { econs. i. ss. des. subst. auto. }
      { econs. i. ss. des; subst; auto. }
    Qed.

    Lemma gtree_O_O: Ord.eq (Ord.from_wf gtree_lt_well_founded gtree_O) Ord.O.
    Proof.
      Local Transparent Ord.from_wf Ord.from_acc Ord.O Ord.S Ord.rec Ord.from_wf_set.
      split.
      { unfold Ord.from_wf. destruct (gtree_lt_well_founded gtree_O).
        ss. econs. i. destruct a0. ss. }
      { eapply Ord.O_bot. }
    Qed.

    Lemma gtree_S_S tr:
      Ord.eq (Ord.from_wf gtree_lt_well_founded (gtree_S tr)) (Ord.S (Ord.from_wf gtree_lt_well_founded tr)).
    Proof.
      split.
      { unfold Ord.from_wf at 1. destruct (gtree_lt_well_founded (gtree_S tr)).
        ss. econs. i. destruct a0. ss. subst. exists tt.
        ss. eapply Ord.same_acc_le.
      }
      { eapply Ord.S_supremum. eapply Ord.from_wf_lt. ss. }
    Qed.

    Lemma gtree_join_build P (trs: sig P -> gtree):
      Ord.eq (Ord.from_wf gtree_lt_well_founded (gtree_join trs)) (Ord.build (fun x => Ord.from_wf gtree_lt_well_founded (trs x))).
    Proof.
      split.
      { unfold Ord.from_wf at 1. destruct (gtree_lt_well_founded (gtree_join trs)).
        ss. econs. i. destruct a0. des. ss. subst. exists x0.
        ss. eapply Ord.same_acc_le.
      }
      { eapply Ord.build_supremum. i. eapply Ord.from_wf_lt. ss. eauto. }
    Qed.

    Lemma gtree_union_union_le (tr0 tr1: gtree):
      Ord.le (Ord.from_wf gtree_lt_well_founded (gtree_union tr0 tr1)) (Ord.S (Ord.union (Ord.from_wf gtree_lt_well_founded tr0) (Ord.from_wf gtree_lt_well_founded tr1))).
    Proof.
      unfold Ord.from_wf at 1. destruct (gtree_lt_well_founded (gtree_union tr0 tr1)).
      ss. econs. i. destruct a0. ss. exists tt. ss. des; subst.
      { transitivity (Ord.from_wf gtree_lt_well_founded tr0).
        { eapply Ord.same_acc_le. }
        { eapply Ord.union_l. }
      }
      { transitivity (Ord.from_wf gtree_lt_well_founded tr1).
        { eapply Ord.same_acc_le. }
        { eapply Ord.union_r. }
      }
    Qed.

    Lemma gtree_union_union_le_rev (tr0 tr1: gtree):
      Ord.le (Ord.union (Ord.from_wf gtree_lt_well_founded tr0) (Ord.from_wf gtree_lt_well_founded tr1)) (Ord.from_wf gtree_lt_well_founded (gtree_union tr0 tr1)).
    Proof.
      eapply Ord.union_spec.
      { eapply Ord.lt_le. eapply Ord.from_wf_lt. ss. auto. }
      { eapply Ord.lt_le. eapply Ord.from_wf_lt. ss. auto. }
    Qed.

    Definition gtree_top := Ord.from_wf_set gtree_lt_well_founded.

    Lemma ginaccessible_rec_ginaccessible (base0: Ord.t) (next: Ord.t -> Ord.t)
          (NEXTLE: forall o, Ord.le o (next o))
          (NEXTMON: forall o0 o1 (LE: Ord.le o0 o1), Ord.le (next o0) (next o1))
          (INACCESSIBLE: ginaccessible X base0 next gtree_top)
          base1
          (BASE1: Ord.lt base1 gtree_top)
      :
        ginaccessible X base0 (Ord.orec base1 next) gtree_top.
    Proof.
      econs; eauto.
      { eapply INACCESSIBLE. }
      2: { eapply INACCESSIBLE. }
      2: { eapply INACCESSIBLE. }
      assert (RECS: forall tr, Ord.lt (Ord.orec base1 next (Ord.from_wf gtree_lt_well_founded tr)) gtree_top).
      { induction tr.
        { eapply (@Ord.eq_lt_lt _ _ base1); auto.
          transitivity (Ord.orec base1 next Ord.O).
          { eapply Ord.eq_orec; auto. eapply gtree_O_O. }
          { eapply Ord.orec_O; auto. }
        }
        { eapply (@Ord.eq_lt_lt _ _ (next (Ord.orec base1 next (Ord.from_wf gtree_lt_well_founded tr)))).
          { transitivity (Ord.orec base1 next (Ord.S (Ord.from_wf gtree_lt_well_founded tr))).
            { eapply Ord.eq_orec; auto. eapply gtree_S_S. }
            { eapply Ord.orec_S; auto. }
          }
          { eapply INACCESSIBLE. auto. }
        }
        { eapply (@Ord.eq_lt_lt _ _ _).
          { etransitivity.
            { eapply Ord.eq_orec; auto. eapply gtree_join_build. }
            { eapply Ord.orec_build. }
          }
          { eapply INACCESSIBLE; auto. eapply INACCESSIBLE. i.
            eapply INACCESSIBLE. auto. }
        }
        { eapply Ord.le_lt_lt.
          { eapply Ord.le_orec.
            { auto. }
            { eapply gtree_union_union_le. }
          }
          eapply Ord.eq_lt_lt.
          { eapply Ord.orec_S; auto. }
          eapply INACCESSIBLE.
          eapply Ord.eq_lt_lt.
          { eapply Ord.orec_union; auto. }
          { eapply INACCESSIBLE; auto. }
        }
      }
      i. eapply Ord.lt_inv in LT. des. eapply (@Ord.le_lt_lt (Ord.orec base1 next (Ord.from_wf gtree_lt_well_founded a))); auto.
      eapply Ord.le_orec; auto.
    Qed.

    Lemma gtree_top_O
      :
        Ord.lt Ord.O gtree_top.
    Proof.
      econs. instantiate (1:=gtree_O). eapply Ord.O_bot.
    Qed.

    Lemma gtree_top_S o (LT: Ord.lt o gtree_top)
      :
        Ord.lt (Ord.S o) gtree_top.
    Proof.
      i. eapply Ord.lt_inv in LT. des.
      econs. instantiate (1:=gtree_S a).
      eapply Ord.S_supremum. eapply Ord.le_lt_lt; eauto.
      eapply Ord.from_wf_lt. ss.
    Qed.

    Lemma gtree_top_union o0 o1 (LT0: Ord.lt o0 gtree_top) (LT1: Ord.lt o1 gtree_top)
      :
        Ord.lt (Ord.union o0 o1) gtree_top.
    Proof.
      eapply Ord.lt_inv in LT0. eapply Ord.lt_inv in LT1. des.
      econs. instantiate (1:=gtree_union a0 a). eapply Ord.union_spec.
      { etransitivity; eauto. eapply Ord.lt_le. eapply Ord.from_wf_lt. ss. auto. }
      { etransitivity; eauto. eapply Ord.lt_le. eapply Ord.from_wf_lt. ss. auto. }
    Qed.

    Hypothesis CHOICE: forall (P: X -> Prop), FunctionalChoice_on (sig P) gtree.

    Lemma gtree_top_join (P: X -> Prop) (os: sig P -> Ord.t)
          (LT: forall x, Ord.lt (os x) gtree_top)
      :
        Ord.lt (Ord.join os) gtree_top.
    Proof.
      i. hexploit (CHOICE (fun (x: sig P) (tr: gtree) => Ord.le (os x) (Ord.from_wf gtree_lt_well_founded tr))).
      { i. specialize (LT x). eapply Ord.lt_inv in LT. eauto. }
      i. des.
      econs. instantiate (1:=gtree_join f).
      eapply Ord.join_supremum. i. etransitivity; eauto.
      eapply Ord.lt_le. eapply Ord.from_wf_lt. ss. eauto.
    Qed.

    Lemma gtree_top_S_ginaccessible
      :
        ginaccessible X Ord.O Ord.S gtree_top.
    Proof.
      econs.
      { eapply gtree_top_O. }
      { eapply gtree_top_S. }
      { eapply gtree_top_join. }
      { eapply gtree_top_union. }
    Qed.

    Lemma gtree_top_add_ginaccessible
          o (LT: Ord.lt o gtree_top)
      :
        ginaccessible X Ord.O (OrdArith.add o) gtree_top.
    Proof.
      Local Transparent OrdArith.add.
      eapply ginaccessible_rec_ginaccessible; eauto.
      { i. eapply Ord.S_le. }
      { i. apply Ord.le_S. auto. }
      { eapply gtree_top_S_ginaccessible. }
    Qed.

    Lemma gtree_top_add o0 o1 (LT0: Ord.lt o0 gtree_top) (LT1: Ord.lt o1 gtree_top)
      :
        Ord.lt (OrdArith.add o0 o1) gtree_top.
    Proof.
      eapply gtree_top_add_ginaccessible; auto.
    Qed.

    Lemma gtree_top_flip_add_ginaccessible
          o (LT: Ord.lt o gtree_top)
      :
        ginaccessible X Ord.O (flip OrdArith.add o) gtree_top.
    Proof.
      hexploit gtree_top_add_ginaccessible; eauto. i.
      econs; auto.
      { eapply Ord.le_lt_lt; eauto. eapply Ord.O_bot. }
      { i. eapply (@gtree_top_add_ginaccessible _ LT0).(ginaccessible_next). auto. }
      { i. eapply H. auto. }
      { i. eapply H; auto. }
    Qed.

    Lemma gtree_top_mult_ginaccessible
          o (LT: Ord.lt o gtree_top)
      :
        ginaccessible X Ord.O (OrdArith.mult o) gtree_top.
    Proof.
      Local Transparent OrdArith.mult.
      eapply ginaccessible_rec_ginaccessible; eauto.
      { i. eapply OrdArith.add_base_l. }
      { i. eapply OrdArith.le_add_l; auto. }
      { eapply gtree_top_flip_add_ginaccessible. auto. }
      { eapply Ord.le_lt_lt; eauto. eapply Ord.O_bot. }
    Qed.

    Lemma gtree_top_mult o0 o1 (LT0: Ord.lt o0 gtree_top) (LT1: Ord.lt o1 gtree_top)
      :
        Ord.lt (OrdArith.mult o0 o1) gtree_top.
    Proof.
      eapply gtree_top_mult_ginaccessible; auto.
    Qed.

    Lemma gtree_top_flip_mult_ginaccessible
          o (LT: Ord.lt o gtree_top)
      :
        ginaccessible X Ord.O (flip OrdArith.mult o) gtree_top.
    Proof.
      hexploit gtree_top_mult_ginaccessible; eauto. i.
      econs; auto.
      { eapply Ord.le_lt_lt; eauto. eapply Ord.O_bot. }
      { i. eapply (@gtree_top_mult_ginaccessible _ LT0).(ginaccessible_next). auto. }
      { i. eapply H. auto. }
      { i. eapply H; auto. }
    Qed.

    Lemma gtree_top_expn_ginaccessible
          o (POS: Ord.lt Ord.O o) (LT: Ord.lt o gtree_top)
      :
        ginaccessible X Ord.O (OrdArith.expn o) gtree_top.
    Proof.
      Local Transparent OrdArith.expn.
      eapply ginaccessible_rec_ginaccessible; eauto.
      { i. unfold flip. eapply OrdArith.mult_le_l. auto. }
      { i. eapply OrdArith.le_mult_l. auto. }
      { eapply gtree_top_flip_mult_ginaccessible. auto. }
      { eapply gtree_top_S. eapply gtree_top_O. }
    Qed.

    Lemma gtree_top_expn o0 o1 (LT0: Ord.lt o0 gtree_top) (LT1: Ord.lt o1 gtree_top)
      :
        Ord.lt (OrdArith.expn o0 o1) gtree_top.
    Proof.
      eapply (@Ord.le_lt_lt (OrdArith.expn (Ord.S o0) o1)).
      { eapply OrdArith.le_expn_l. eapply Ord.S_le. }
      { eapply gtree_top_expn_ginaccessible; auto.
        { eapply Ord.S_pos. }
        { eapply gtree_top_S. auto. }
      }
    Qed.

    Lemma gtree_top_flip_expn_ginaccessible
          o (LT: Ord.lt o gtree_top)
      :
        ginaccessible X Ord.O (flip OrdArith.expn o) gtree_top.
    Proof.
      econs.
      { eapply gtree_top_O. }
      { i. eapply gtree_top_expn; auto. }
      { eapply gtree_top_join. }
      { eapply gtree_top_union. }
    Qed.
  End GTREE.
End INACCESSIBLE.
