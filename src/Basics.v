From Ordinal Require Import sflib.

Require Import Coq.Classes.RelationClasses Coq.Relations.Relation_Operators Coq.Classes.Morphisms Coq.Init.Wf. (* TODO: Use Morphisms *)

Set Implicit Arguments.
Set Primitive Projections.

Theorem cantor_theorem A (f: A -> (A -> Prop)):
  exists P, forall a, f a <> P.
Proof.
  exists (fun a => ~ (f a) a). ii.
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

Lemma Fix_equiv
      A (R : A -> A -> Prop) (Rwf : well_founded R)
      (B: Type) (eqv: B -> B -> Prop)
      (F : forall x, (forall y, R y x -> B) -> B)
      (EQ: forall x (f g : forall y, R y x -> B),
          (forall y (p0 p1: R y x), eqv (f y p0) (g y p1)) -> eqv (F x f) (F x g))
  :
  forall x,
    eqv (Fix Rwf (fun _ => B) F x) (F x (fun (y : A) (_ : R y x) => Fix Rwf (fun _ => B) F y)).
Proof.
  cut (forall x (p0 p1: Acc R x), eqv (Fix_F (fun _ => B) F p0) (Fix_F (fun _ => B) F p1)).
  { i. unfold Fix. rewrite <- Fix_F_eq. eapply EQ. i. eapply H. }
  intros x. pattern x. revert x. eapply (well_founded_induction Rwf).
  i. rewrite <- Fix_F_eq. rewrite <- Fix_F_eq.
  eapply EQ. i. eapply H. auto.
Qed.

Variant double_rel A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
  : A * B -> A * B -> Prop :=
| double_rel_left a0 a1 b (LT: RA a0 a1): double_rel RA RB (a0, b) (a1, b)
| double_rel_right a b0 b1 (LT: RB b0 b1): double_rel RA RB (a, b0) (a, b1)
.

Lemma double_rel_well_founded A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
      (WFA: well_founded RA) (WFB: well_founded RB)
  :
  well_founded (double_rel RA RB).
Proof.
  cut (forall a b, Acc (double_rel RA RB) (a, b)).
  { ii. destruct a as [a b]. eapply H. }
  intros a0. pattern a0. revert a0.
  eapply (well_founded_induction WFA).
  intros a0 IHL. intros b0. pattern b0. revert b0.
  eapply (well_founded_induction WFB).
  intros b0 IHR. econs. intros [a1 b1]. i. inv H.
  { eapply IHL; eauto. }
  { eapply IHR; eauto. }
Qed.

Lemma double_well_founded_induction A B (RA: A -> A -> Prop) (RB: B -> B -> Prop)
      (WFA: well_founded RA) (WFB: well_founded RB)
      (P: A -> B -> Prop)
      (IND: forall a1 b1
                   (IHL: forall a0 (LT: RA a0 a1), P a0 b1)
                   (IHR: forall b0 (LT: RB b0 b1), P a1 b0),
          P a1 b1)
  :
  forall a b, P a b.
Proof.
  cut (forall ab, P (fst ab) (snd ab)).
  { i. apply (H (a, b)). }
  intros ab. pattern ab. revert ab.
  eapply (well_founded_induction (double_rel_well_founded WFA WFB)).
  intros [a b] ?. ss. eapply IND.
  { i. eapply (H (a0, b)). econstructor 1. auto. }
  { i. eapply (H (a, b0)). econstructor 2. auto. }
Qed.
