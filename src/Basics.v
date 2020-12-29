From Ordinal Require Import sflib.

Require Import Coq.Classes.RelationClasses Coq.Relations.Relation_Operators Coq.Classes.Morphisms. (* TODO: Use Morphisms *)
Require Import Program.

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

Lemma acc_incl A (R0 R1: A -> A -> Prop) (INCL: forall a0 a1 (LE: R0 a0 a1), R1 a0 a1)
      a (ACC: Acc R1 a)
  :
    Acc R0 a.
Proof.
  induction ACC. econs. i. eapply H0; eauto.
Qed.

Lemma wf_incl A (R0 R1: A -> A -> Prop) (INCL: forall a0 a1 (LE: R0 a0 a1), R1 a0 a1)
      (WF: well_founded R1)
  :
    well_founded R0.
Proof.
  econs. i. eapply acc_incl; eauto.
Qed.

Lemma bot_well_founded A: @well_founded A (fun _ _ => False).
Proof.
  ii. econs; ss.
Qed.
