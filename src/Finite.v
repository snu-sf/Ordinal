From Ordinal Require Import sflib Basics WFRel.
From Ordinal Require Export Ordinal ToSet Cardinal.

Require Import Program.

Set Implicit Arguments.
Set Primitive Projections.

Fixpoint finite (n: nat): Type :=
  match n with
  | 0 => False
  | Datatypes.S n' => option (finite n')
  end.

Fixpoint finite_lt (n: nat): finite n -> finite n -> Prop :=
  match n with
  | 0 => fun _ _ => False
  | Datatypes.S n' =>
    fun x y => match x, y with
               | Some x', Some y' => finite_lt n' x' y'
               | Some x', None => True
               | _, _ => False
               end
  end.

Lemma finite_total: forall n x0 x1, finite_lt n x0 x1 \/ x0 = x1 \/ finite_lt n x1 x0.
Proof.
  induction n.
  { i. ss. }
  { i. ss. destruct x0, x1; ss; eauto.
    destruct (IHn f f0) as [|[]]; eauto. subst. auto.
  }
Qed.

Lemma finite_lt_acc: forall n x (ACC: Acc (finite_lt n) x), Acc (finite_lt (Datatypes.S n)) (Some x).
Proof.
  intros n x ACC. induction ACC. econs. i. destruct y; ss.
  eapply H0. auto.
Qed.

Lemma finite_well_founded: forall n, well_founded (finite_lt n).
Proof.
  induction n.
  - ii. econs. i. ss.
  - ii. econs. i. destruct a, y; ss.
    + eapply finite_lt_acc. eapply IHn.
    + eapply finite_lt_acc. eapply IHn.
Qed.

Lemma finite_from_acc_eq:
  forall n (x: finite n)
         (ACC0: Acc (finite_lt n) x) (ACC1: Acc (finite_lt (Datatypes.S n)) (Some x)),
    Ord.eq (Ord.from_acc ACC0) (Ord.from_acc ACC1).
Proof.
  intros n x ACC. dup ACC.
  induction ACC0. i. destruct ACC, ACC1. ss. split.
  { econs. i. destruct a1. exists (exist _ (Some x0) (f)). ss. eapply H0. auto. }
  { econs. i. destruct a1. destruct x0; ss. exists (exist _ f y). ss. eapply H0. auto. }
Qed.

Lemma finite_from_wf_eq:
  forall n (x: finite n),
    Ord.eq (Ord.from_wf (finite_well_founded n) x) (Ord.from_wf (finite_well_founded (Datatypes.S n)) (Some x)).
Proof.
  i. eapply finite_from_acc_eq.
Qed.

Lemma finite_from_wf_set_eq:
  forall n,
    Ord.eq (Ord.from_wf_set (finite_well_founded n)) (Ord.from_wf (finite_well_founded (Datatypes.S n)) None).
Proof.
  i. split.
  { eapply Ord.build_spec. i. eapply Ord.le_lt_lt.
    { eapply finite_from_wf_eq. }
    { eapply Ord.from_wf_lt. ss. }
  }
  { unfold Ord.from_wf at 1. destruct (finite_well_founded (Datatypes.S n) None).
    ss. econs. i. destruct a0. ss. destruct x; ss.
    exists f. eapply finite_from_acc_eq.
  }
Qed.

Lemma finite_S:
  forall n,
    Ord.eq (Ord.S (Ord.from_wf_set (finite_well_founded n))) (Ord.from_wf_set (finite_well_founded (Datatypes.S n))).
Proof.
  i. split.
  - eapply Ord.S_spec. eapply Ord.le_lt_lt.
    { eapply finite_from_wf_set_eq. }
    { eapply Ord.from_wf_set_upperbound. }
  - econs. i. exists tt. ss. etransitivity.
    2: { eapply finite_from_wf_set_eq. }
    destruct a0.
    { eapply Ord.lt_le. eapply Ord.from_wf_lt. auto. }
    { reflexivity. }
Qed.

Lemma finite_O:
  Ord.eq (Ord.from_wf_set (finite_well_founded 0)) Ord.O.
Proof.
  split.
  { econs. i. ss. }
  { eapply Ord.O_bot. }
Qed.

Lemma O_cardinal:
  Cardinal.of_cardinal False Ord.O.
Proof.
  split.
  { exists (fun _ _ => False).
    assert (WF: well_founded (fun _ _: False => False)).
    { ii. ss. }
    exists WF. splits; auto. split.
    { econs. i. ss. }
    { eapply Ord.O_bot. }
  }
  { i. eapply Ord.O_bot. }
Qed.

Lemma O_is_cardinal:
  Cardinal.is_cardinal Ord.O.
Proof.
  eapply Cardinal.of_cardinal_is_cardinal. eapply O_cardinal.
Qed.

Lemma finite_cardinal_O:
  Cardinal.is_cardinal (Ord.from_wf_set (finite_well_founded 0)).
Proof.
  eapply Cardinal.of_cardinal_is_cardinal. eapply Cardinal.eq_of_cardinal.
  2: { eapply O_cardinal. }
  symmetry. eapply finite_O.
Qed.

(* Lemma finite_incr n: Ord.lt (cardinal (finite n)) (cardinal (finite (Datatypes.S n))). *)
