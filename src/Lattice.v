From Paco Require Import paco.
From Ordinal Require Import sflib Ordinal Fixedpoint.
Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.
Set Primitive Projections.

Ltac oinduction := let o := fresh "o" in intros o; pattern o; revert o; eapply (well_founded_induction Ord.lt_well_founded).

Section LATTICE.
  Variable X: Type.
  Let rel := forall (x0: X), Prop.
  Let irel := Ord.t -> rel.

  Let le : rel -> rel -> Prop :=
    fun r0 r1 => forall x (IN: r0 x), r1 x.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. eauto.
  Qed.
  Next Obligation.
  Proof.
    ii. eauto.
  Qed.

  Definition prefixpoint (f: rel -> rel) (r: rel) := le (f r) r.
  Definition postfixpoint (f: rel -> rel) (r: rel) := le r (f r).

  Definition mu (f: rel -> rel): rel :=
    fun x => forall (r: rel) (FIX: prefixpoint f r), r x.
  Arguments mu: clear implicits.

  Lemma mu_least f r (FIX: prefixpoint f r):
    le (mu f) r.
  Proof.
    ii. eapply IN. auto.
  Qed.

  Lemma mu_fold f (MONOTONE: monotone1 f):
    le (f (mu f)) (mu f).
  Proof.
    ii. eapply FIX. eapply MONOTONE; eauto.
    i. eapply mu_least; eauto.
  Qed.

  Lemma mu_unfold f (MONOTONE: monotone1 f):
    le (mu f) (f (mu f)).
  Proof.
    ii. eapply IN. ii. eapply MONOTONE; eauto.
    i. ss. eapply mu_fold; eauto.
  Qed.

  Lemma mu_mon (f0 f1: rel -> rel)
        (LE: forall r, le (f0 r) (f1 r)):
    le (mu f0) (mu f1).
  Proof.
    ii. eapply IN. ii. eapply FIX. eapply LE. auto.
  Qed.

  Definition nu (f: rel -> rel): rel :=
    fun x => exists (r: rel), postfixpoint f r /\ r x.
  Arguments nu: clear implicits.

  Lemma nu_greatest f r (FIX: postfixpoint f r):
    le r (nu f).
  Proof.
    ii. exists r. eauto.
  Qed.

  Lemma nu_unfold f (MONOTONE: monotone1 f):
    le (nu f) (f (nu f)).
  Proof.
    ii. unfold nu in IN. des. eapply IN in IN0. eapply MONOTONE; eauto.
    i. eapply nu_greatest; eauto.
  Qed.

  Lemma nu_fold f (MONOTONE: monotone1 f):
    le (f (nu f)) (nu f).
  Proof.
    ii. exists (f (nu f)). split; auto.
    ii. eapply MONOTONE; eauto. i. eapply nu_unfold; auto.
  Qed.

  Lemma nu_mon (f0 f1: rel -> rel)
        (LE: forall r, le (f0 r) (f1 r)):
    le (nu f0) (nu f1).
  Proof.
    unfold nu. ii. des. esplits; eauto.
    ii. eapply LE. eapply IN. auto.
  Qed.

  Opaque mu nu.


  Variable F: rel -> rel -> rel.
  Arguments F: clear implicits.

  Hypothesis MON:
    forall rg0 rl0 rg1 rl1
           (LEG: le rg0 rg1) (LEL: le rl0 rl1),
      le (F rg0 rl0) (F rg1 rl1).

  Let union (P: Ord.t -> Prop) (ir: irel): rel :=
    fun x => exists o, ir o x /\ P o.

  Definition ilift (ir: irel): irel :=
    fun o1 => F (union (fun o0 => True) ir) (union (fun o0 => Ord.lt o0 o1) ir).

  Lemma ilift_mon: monotone2 ilift.
  Proof.
    ii. unfold ilift, union in *. eapply MON; eauto.
    { ii. des. eauto. }
    { ii. des. eauto. }
  Qed.
  Hint Resolve ilift_mon: paco.


  Definition ilift_snd (r: rel) (ir: irel): irel :=
    fun o1 => F r (union (fun o0 => Ord.lt o0 o1) ir).

  Lemma ilift_snd_mon r: monotone2 (ilift_snd r).
  Proof.
    ii. eapply MON; eauto.
    { ii. auto. }
    { ii. unfold union in *. des. eauto. }
  Qed.
  Hint Resolve ilift_snd_mon: paco.


  Definition inaccessible (ir: irel) (k: Ord.t): Prop :=
    forall o x (IN: ir o x), union (fun o0 => Ord.lt o0 k) ir x.

  (* classic needed *)
  Lemma hartogs_inaccessible:
    forall (r: rel), inaccessible (paco2 (ilift_snd r) bot2) (Ord.S (Ord.hartogs rel)).
  Proof.
    ii. exists (Ord.hartogs rel). split.
    2: { eapply Ord.S_lt. }
    cut (Fixedpoint.mu (F r) x).
    { clear IN. unfold Fixedpoint.mu. revert x. clear o.
      unfold rel. generalize (Ord.hartogs (X -> Prop)).
      pcofix CIH. oinduction. i. destruct x.
      rewrite Ord.rec_red in H0. des. destruct x; ss. des.
      pfold. eapply MON; eauto; ss.
      ii. exists (os x). splits; eauto. eapply Ord.build_upperbound.
    }
    cut (mu (F r) x).
    { clear o IN. revert x. apply mu_least.
      ii. eapply mu_fixpoint; auto.
      i. eapply MON; eauto; ss.
    }
    { revert o x IN.
      eapply (well_founded_induction Ord.lt_well_founded (fun o => forall x (IN: paco2 (ilift_snd r) bot2 o x), mu (F r) x)).
      i. eapply mu_fold; auto.
      { ii. eapply MON; eauto. ss. }
      punfold IN. eapply MON; eauto; ss.
      ii. inv IN0. des. pclearbot. eapply H; eauto.
    }
  Qed.
End LATTICE.

#[export] Hint Resolve ilift_mon: paco.
#[export] Hint Resolve ilift_snd_mon: paco.
Arguments ilift [_].
Arguments ilift_snd [_].
Arguments inaccessible [_].

Section EQUIVALENCE.
  Variable X: Type.
  Let rel := forall (x0: X), Prop.
  Let irel := Ord.t -> rel.

  Let le : rel -> rel -> Prop :=
    fun r0 r1 => forall x (IN: r0 x), r1 x.

  Variable F: rel -> rel -> rel.
  Hypothesis MON: forall rg0 rl0 rg1 rl1 (LEG: le rg0 rg1) (LEL: le rl0 rl1),
      le (F rg0 rl0) (F rg1 rl1).

  Let MONFST: forall r, monotone1 (F r).
  Proof.
    ii. eapply MON; eauto. reflexivity.
  Qed.

  Let MONMU: monotone1 (fun r => mu (F r)).
  Proof.
    ii. eapply mu_mon; eauto. ii. eapply FIX.
    eapply MON; [..|eauto]; eauto. reflexivity.
  Qed.

  Let ipaco_snd_mon: monotone1 (fun r x => exists o, paco2 (ilift_snd F r) bot2 o x).
  Proof.
    ii. des. exists o. revert x0 o IN. pcofix CIH. i.
    punfold IN. pfold. eapply MON; eauto.
    ii. des. esplits; eauto. pclearbot. right. eauto.
  Qed.

  Section INACCESSIBLE.
    Variable k: Ord.t.
    Hypothesis INACCESSIBLE: forall (r: rel), inaccessible (paco2 (ilift_snd F r) bot2) k.

    Let mu_equivalent r:
      forall x, mu (F r) x <-> (exists o, paco2 (ilift_snd F r) bot2 o x).
    Proof.
      i. split.
      { revert x. eapply mu_least. ii. exists k.
        pfold. eapply MON; eauto.
        { reflexivity. }
        ii. des. exploit INACCESSIBLE; eauto. i. des.
        exists o0. split; eauto.
      }
      { i. des. revert o x H.
        eapply (well_founded_induction Ord.lt_well_founded (fun o => forall x (IN: paco2 (ilift_snd F r) bot2 o x), mu (F r) x)).
        i. eapply mu_fold; auto. punfold IN.
        eapply MON; eauto.
        { reflexivity. }
        ii. inv IN0. des. pclearbot. eapply H; eauto.
      }
    Qed.

    Let nu_impl:
      forall x o (IN: paco2 (ilift_snd F (nu (fun r x => exists o, paco2 (ilift_snd F r) bot2 o x))) bot2 o x),
        paco2 (ilift F) bot2 o x.
    Proof.
      pcofix CIH. i. punfold IN. pfold.
      eapply MON; eauto.
      { ii. eapply nu_unfold in IN0; auto. des. exists o0. split; auto. }
      { ii. inv IN0. des. pclearbot. eapply CIH in H.
        exists x1. split; auto. }
    Qed.

    Let nu_equivalent:
      forall x, nu (fun r x => exists o, paco2 (ilift_snd F r) bot2 o x) x
                <-> exists o, paco2 (ilift F) bot2 o x.
    Proof.
      i. split.
      { i. eapply nu_unfold in H; auto. des.
        eapply nu_impl in H; eauto. }
      { revert x. eapply nu_greatest. ii. des. revert o x IN.
        eapply (well_founded_induction Ord.lt_well_founded (fun o => forall x (IN: paco2 (ilift F) bot2 o x), exists o0, paco2 (ilift_snd F (fun x => exists o1, paco2 (ilift F) bot2 o1 x)) bot2 o0 x)).
        i. exists k.
        pfold. punfold IN. unfold ilift_snd at 1. unfold ilift at 1 in IN.
        eapply MON; eauto.
        { ii. des. pclearbot. eauto. }
        { ii. des. pclearbot.
          hexploit H; eauto. i. des.
          dup INACCESSIBLE. unfold inaccessible in INACCESSIBLE0.
          eapply INACCESSIBLE in H0. des. exists o1. split; eauto. }
      }
    Qed.

    Lemma ipaco_munu_gen:
      forall x, nu (fun r => mu (F r)) x <-> exists o, paco2 (ilift F) bot2 o x.
    Proof.
      i. etransitivity.
      2: { eapply nu_equivalent. }
      split; i.
      { revert x H. eapply nu_greatest. ii.
        erewrite <- (mu_equivalent (nu (fun r : rel => mu (F r)))).
        eapply nu_unfold in IN; auto.
      }
      { revert x H. eapply nu_greatest. ii.
        eapply (mu_equivalent (nu (fun (r : rel) x => exists o : Ord.t, paco2 (ilift_snd F r) bot2 o x))).
        eapply nu_unfold in IN; eauto.
        ii. eapply FIX. eauto. }
    Qed.

    Lemma ipaco_inaccessible_gen:
      inaccessible (paco2 (ilift F) bot2) k.
    Proof.
      ii. hexploit (proj2 (@nu_equivalent x)); eauto. i.
      eapply nu_unfold in H; auto. des.
      eapply INACCESSIBLE in H; eauto. des.
      eapply nu_impl in H. exists o1. split; auto.
    Qed.
  End INACCESSIBLE.


  Theorem ipaco_munu:
    forall x, nu (fun r => mu (F r)) x <-> exists o, paco2 (ilift F) bot2 o x.
  Proof.
    eapply ipaco_munu_gen.
    i. eapply hartogs_inaccessible; eauto.
  Qed.

  Theorem ipaco_inaccessible:
    exists k, inaccessible (paco2 (ilift F) bot2) k.
  Proof.
    eexists. eapply ipaco_inaccessible_gen.
    i. eapply hartogs_inaccessible; eauto.
  Qed.
End EQUIVALENCE.
