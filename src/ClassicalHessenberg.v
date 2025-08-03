From Ordinal Require Import sflib Basics.
From Ordinal Require Export Ordinal Arithmetic Hessenberg ClassicalOrdinal.

Require Import Stdlib.Classes.RelationClasses Stdlib.Classes.Morphisms.

Set Implicit Arguments.
Set Primitive Projections.


(* TODO: find a constructive proof!! *)
Module ClassicJacobsthal.
  Lemma mult_dist o0 o1 o2: Ord.eq (Jacobsthal.mult o0 (Hessenberg.add o1 o2)) (Hessenberg.add (Jacobsthal.mult o0 o1) (Jacobsthal.mult o0 o2)).
  Proof.
    destruct (ClassicOrd.total o0 Ord.O) as [LE|LT].
    { assert (ZERO: Ord.eq o0 Ord.O).
      { split; auto. apply Ord.O_bot. }
      rewrite ZERO. rewrite ! Jacobsthal.mult_O_l. rewrite Hessenberg.add_O_l. reflexivity.
    }
    revert o1 o2.
    eapply (double_well_founded_induction Ord.lt_well_founded Ord.lt_well_founded).
    i. hexploit (ClassicOrd.limit_or_S a1). i. des.
    { hexploit Ord.is_S_unique.
      { eapply H. }
      { eapply Ord.S_is_S. }
      i. rewrite H0. rewrite Hessenberg.add_S_l.
      rewrite Jacobsthal.mult_S. rewrite Jacobsthal.mult_S.
      rewrite IHL.
      { rewrite Hessenberg.add_assoc. reflexivity. }
      { eapply H. }
    }
    hexploit (ClassicOrd.limit_or_S b1). i. des.
    { hexploit Ord.is_S_unique.
      { eapply H1. }
      { eapply Ord.S_is_S. }
      i. rewrite H2. rewrite Hessenberg.add_S_r.
      rewrite Jacobsthal.mult_S. rewrite Jacobsthal.mult_S.
      rewrite IHR.
      { rewrite Hessenberg.add_comm.
        rewrite Hessenberg.add_assoc.
        eapply Hessenberg.eq_add_r.
        eapply Hessenberg.add_comm.
      }
      { eapply H1. }
    }
    hexploit Ord.is_join_unique.
    { eapply H. }
    { eapply Ord.join_is_join. }
    i. rewrite H3.
    hexploit Ord.is_join_unique.
    { eapply H1. }
    { eapply Ord.join_is_join. }
    i. rewrite H4.
    rewrite Jacobsthal.mult_join. rewrite Jacobsthal.mult_join.
    rewrite <- Ord.build_join; auto.
    rewrite <- Ord.build_join; auto.
    symmetry. rewrite <- Ord.build_join.
    2:{ ii. specialize (H0 a0). des. exists a2. eapply Jacobsthal.lt_mult_r; auto. }
    rewrite <- Ord.build_join.
    2:{ ii. specialize (H2 a0). des. exists a2. eapply Jacobsthal.lt_mult_r; auto. }
    rewrite Hessenberg.add_red.
    rewrite Hessenberg.add_red.
    rewrite Jacobsthal.mult_union. eapply Ord.eq_union.
    { rewrite Jacobsthal.mult_build. rewrite Ord.build_join.
      2:{ ii. specialize (H2 a0). des. exists a2. eapply Hessenberg.lt_add_r. eapply Jacobsthal.lt_mult_r; auto. }
      split.
      { eapply Ord.le_join. i. hexploit (H2 a0); auto. i. des.
        exists a2. rewrite (Ord.build_join H0); auto.
        rewrite <- H3. rewrite IHR.
        2:{ rewrite H4. rewrite <- Ord.build_join; auto. eapply Ord.build_upperbound. }
        eapply Ord.S_supremum in H5. rewrite <- H5.
        rewrite Jacobsthal.mult_S. rewrite <- Hessenberg.add_assoc.
        rewrite <- Hessenberg.add_assoc.
        eapply Hessenberg.le_add_l.
        eapply Ord.build_supremum. i.
        eapply Ord.lt_le_lt.
        { apply Jacobsthal.lt_mult_r; auto. eapply Ord.build_upperbound. }
        { rewrite Ord.build_join; auto.
          rewrite <- H3. rewrite Hessenberg.add_comm.
          rewrite <- Hessenberg.add_assoc. eapply Hessenberg.add_base_r.
        }
      }
      { eapply Ord.le_join. i. hexploit (H2 a0); auto. i. des.
        exists a2. rewrite Ord.build_join; auto.
        rewrite <- H3. rewrite IHR.
        2:{ rewrite H4. rewrite <- Ord.build_join; auto. eapply Ord.build_upperbound. }
        eapply Ord.S_supremum in H5. rewrite <- H5.
        rewrite Jacobsthal.mult_S. rewrite <- Hessenberg.add_assoc.
        rewrite <- Hessenberg.add_assoc.
        eapply Hessenberg.le_add_l.
        rewrite Hessenberg.add_comm.
        eapply Hessenberg.le_add_l.
        rewrite H3. rewrite Jacobsthal.mult_join.
        rewrite Ord.build_join; auto.
        2:{ ii. specialize (H0 a3). des. exists a4. apply Jacobsthal.lt_mult_r; auto. }
        reflexivity.
      }
    }
    { rewrite Jacobsthal.mult_build. rewrite Ord.build_join.
      2:{ ii. specialize (H0 a0). des. exists a2. eapply Hessenberg.lt_add_l. eapply Jacobsthal.lt_mult_r; auto. }
      split.
      { eapply Ord.le_join. i. hexploit (H0 a0); auto. i. des.
        exists a2. rewrite (Ord.build_join H2); auto.
        rewrite <- H4. rewrite IHL.
        2:{ rewrite H3. rewrite <- Ord.build_join; auto. eapply Ord.build_upperbound. }
        eapply Ord.S_supremum in H5. rewrite <- H5.
        rewrite Jacobsthal.mult_S. transitivity (Jacobsthal.mult o0 (os a0) ⊕ o0 ⊕ Jacobsthal.mult o0 b1)%ord.
        { eapply Hessenberg.le_add_r.
          eapply Ord.build_supremum. i.
          eapply Ord.lt_le_lt.
          { apply Jacobsthal.lt_mult_r; auto. eapply Ord.build_upperbound. }
          { rewrite Ord.build_join; auto.
            rewrite <- H4. eapply Hessenberg.add_base_r.
          }
        }
        { etransitivity; [|eapply Hessenberg.add_base_r].
          rewrite <- Hessenberg.add_assoc.
          eapply Hessenberg.le_add_l. rewrite Hessenberg.add_comm. reflexivity.
        }
      }
      { eapply Ord.le_join. i. hexploit (H0 a0); auto. i. des.
        exists a2. rewrite Ord.build_join; auto.
        rewrite <- H4. rewrite IHL.
        2:{ rewrite H3. rewrite <- Ord.build_join; auto. eapply Ord.build_upperbound. }
        eapply Ord.S_supremum in H5. rewrite <- H5.
        rewrite Jacobsthal.mult_S. rewrite Hessenberg.add_assoc.
        eapply Hessenberg.le_add_r.
        eapply Hessenberg.le_add_r.
        rewrite H4. rewrite Jacobsthal.mult_join.
        rewrite Ord.build_join; auto.
        2:{ ii. specialize (H2 a3). des. exists a4. apply Jacobsthal.lt_mult_r; auto. }
        reflexivity.
      }
    }
  Qed.

  Lemma mult_assoc o0 o1 o2: Ord.eq (Jacobsthal.mult (Jacobsthal.mult o0 o1) o2) (Jacobsthal.mult o0 (Jacobsthal.mult o1 o2)).
  Proof.
    revert o0 o1. induction o2. i. etransitivity.
    { eapply Jacobsthal.mult_build. } etransitivity.
    2: {
      eapply Jacobsthal.eq_mult_r; auto.
      { symmetry. eapply Jacobsthal.mult_build. }
    }
    etransitivity.
    2: { symmetry. eapply Jacobsthal.mult_join. }
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

  Lemma expn_add base (POS: Ord.lt Ord.O base) o0 o1:
    Ord.eq (Jacobsthal.expn base (OrdArith.add o0 o1)) (Jacobsthal.mult (Jacobsthal.expn base o0) (Jacobsthal.expn base o1)).
  Proof.
    revert o0. induction o1. i. etransitivity.
    { eapply Jacobsthal.eq_expn_r. eapply OrdArith.add_build. }
    etransitivity.
    { eapply Jacobsthal.expn_union. auto. }
    etransitivity.
    2: { eapply Jacobsthal.eq_mult_r. symmetry. eapply Jacobsthal.expn_build. }
    etransitivity.
    2: { symmetry. eapply Jacobsthal.mult_union. }
    etransitivity.
    { eapply Ord.eq_union.
      { reflexivity. }
      eapply Jacobsthal.expn_join. auto.
    }
    etransitivity.
    { eapply Ord.union_assoc. }
    eapply Ord.eq_union.
    { etransitivity.
      { eapply Ord.union_comm. }
      { etransitivity.
        2: { symmetry. eapply Jacobsthal.mult_1_r. }
        { eapply Ord.union_max. eapply Ord.S_supremum. eapply Jacobsthal.expn_pos. }
      }
    }
    etransitivity.
    2: { symmetry. eapply Jacobsthal.mult_join. }
    eapply Ord.eq_join. i.
    etransitivity.
    { eapply Jacobsthal.expn_S. auto. }
    etransitivity.
    2: { eapply mult_assoc. }
    eapply Jacobsthal.eq_mult_l.
    eapply H.
  Qed.

  Lemma expn_mult o0 (POS: Ord.lt Ord.O o0) o1 o2:
    Ord.eq (Jacobsthal.expn o0 (OrdArith.mult o1 o2)) (Jacobsthal.expn (Jacobsthal.expn o0 o1) o2).
  Proof.
    induction o2.
    etransitivity.
    { eapply Jacobsthal.eq_expn_r. eapply OrdArith.mult_build. }
    etransitivity.
    { eapply Jacobsthal.expn_join. auto. }
    etransitivity.
    2: { symmetry. eapply Jacobsthal.expn_build. }
    eapply Ord.eq_union.
    { reflexivity. }
    eapply Ord.eq_join. i.
    etransitivity.
    { eapply expn_add. auto. }
    eapply Jacobsthal.eq_mult_l. auto.
  Qed.

End ClassicJacobsthal.
