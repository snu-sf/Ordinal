Require Import sflib.

Require Import Coq.Classes.RelationClasses Coq.Relations.Relation_Operators Coq.Classes.Morphisms ChoiceFacts. (* TODO: Use Morphisms *)
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.
Require Import Program.

Require Import Constructive.

Set Implicit Arguments.
Set Primitive Projections.

Lemma exists_forall_commute A (B: A -> Type) (P: forall (a: A) (b: B a), Prop)
  :
    (exists (a: A), forall (b: B a), P a b) ->
    (forall (f: forall (a: A), B a), exists (a: A), P a (f a)).
Proof.
  i. des. esplits; eauto.
Qed.

Lemma exists_forall_commute_rev A (B: A -> Type) (P: forall (a: A) (b: B a), Prop)
  :
    (forall (f: forall (a: A), B a), exists (a: A), P a (f a)) ->
    (exists (a: A), forall (b: B a), P a b).
Proof.
  i. eapply NNPP. ii. generalize (not_ex_all_not _ _ H0). i. clear H0.
  exploit non_dep_dep_functional_choice.
  { ii. eapply choice. auto. }
  { instantiate (1:=(fun a b => ~ P a b)).
    i. specialize (H1 x). eapply not_all_ex_not in H1; eauto. }
  i. des. specialize (H f). des. eapply x0; eauto.
Qed.

Lemma forall_exists_commute A (B: A -> Type) (P: forall (a: A) (b: B a), Prop)
  :
    (forall (a: A), exists (b: B a), P a b)
    ->
    (exists (f: forall (a: A), B a), forall (a: A), P a (f a)).
Proof.
  i. eapply non_dep_dep_functional_choice; auto.
  ii. eapply choice. auto.
Qed.

Lemma forall_exists_commute_rev A (B: A -> Type) (P: forall (a: A) (b: B a), Prop)
  :
    (exists (f: forall (a: A), B a), forall (a: A), P a (f a)) ->
    (forall (a: A), exists (b: B a), P a b).
Proof.
  i. des. eauto.
Qed.

Module iProp.
  Definition t := Ordinal.t -> Prop.
  Definition le (P0 P1: t): Prop := forall i (IN: P0 i), P1 i.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. eauto.
  Qed.
  Next Obligation.
  Proof.
    ii. eauto.
  Qed.

  Global Program Instance le_Antisymmetric: Antisymmetric _ eq le.
  Next Obligation.
  Proof.
    extensionality i. eapply propositional_extensionality. eauto.
  Qed.

  Definition ge := flip le.

  Definition closed (P: t): Prop :=
    forall i0 i1 (IN: P i0) (LE: Ordinal.le i0 i1), P i1.


  Definition next (P: t): t :=
    fun i1 => exists i0, P i0 /\ Ordinal.lt i0 i1.

  Lemma next_incl P (CLOSED: closed P): le (next P) P.
  Proof.
    unfold next in *. ii. des. eapply CLOSED; eauto. eapply Ordinal.lt_le; eauto.
  Qed.

  Lemma next_mon P0 P1 (LE: le P0 P1): le (next P0) (next P1).
  Proof.
    unfold next in *. ii. des. exists i0; eauto.
  Qed.

  Lemma next_closed P: closed (next P).
  Proof.
    ii. unfold next in *. des. esplits; eauto.
    eapply Ordinal.lt_le_lt; eauto.
  Qed.

  Definition meet A (Ps: A -> t): t :=
    fun i => forall a, Ps a i.

  Lemma meet_mon A Ps0 Ps1 (LE: forall (a: A), le (Ps0 a) (Ps1 a)): le (meet Ps0) (meet Ps1).
  Proof.
    ii. des. specialize (IN a). eapply LE in IN. eauto.
  Qed.

  Lemma meet_lowerbound A (Ps: A -> t) a:
      le (meet Ps) (Ps a).
  Proof.
    ii. eauto.
  Qed.

  Lemma meet_infimum A (Ps: A -> t) P
        (LE: forall a, le P (Ps a))
    :
      le P (meet Ps).
  Proof.
    ii. eapply LE in IN; eauto.
  Qed.

  Lemma meet_closed A (Ps: A -> t) (CLOSED: forall a, closed (Ps a)): closed (meet Ps).
  Proof.
    unfold meet. ii. eapply CLOSED; eauto.
  Qed.


  Definition join A (Ps: A -> t): t :=
    fun i => exists a, Ps a i.

  Lemma join_mon A Ps0 Ps1 (LE: forall (a: A), le (Ps0 a) (Ps1 a)): le (join Ps0) (join Ps1).
  Proof.
    unfold join in *. ii. des. eapply LE in IN. eauto.
  Qed.

  Lemma join_upperbound A (Ps: A -> t) a
    :
      le (Ps a) (join Ps).
  Proof.
    unfold join. ii. eauto.
  Qed.

  Lemma join_supremum A (Ps: A -> t) P
        (LE: forall a, le (Ps a) P)
    :
      le (join Ps) P.
  Proof.
    unfold join. ii. des. eapply LE; eauto.
  Qed.

  Lemma join_closed A (Ps: A -> t) (CLOSED: forall a, closed (Ps a)): closed (join Ps).
  Proof.
    unfold join. ii. des. esplits; eauto. eapply CLOSED; eauto.
  Qed.


  Definition top: t := meet (False_rect _).

  Lemma top_spec P: le P top.
  Proof.
    eapply meet_infimum. i. ss.
  Qed.

  Lemma top_closed: closed top.
  Proof.
    eapply meet_closed. ss.
  Qed.


  Definition bot: t := join (False_rect _).

  Lemma bot_spec P: le bot P.
  Proof.
    eapply join_supremum. i. ss.
  Qed.

  Lemma bot_closed: closed bot.
  Proof.
    eapply join_closed. ss.
  Qed.


  Definition future (P: t): t :=
    fun i1 => exists i0, P i0.

  Lemma future_mon P0 P1 (LE: le P0 P1): le (future P0) (future P1).
  Proof.
    unfold future in *. ii. des. eauto.
  Qed.

  Lemma future_incl P: le P (future P).
  Proof.
    unfold future. ii. eauto.
  Qed.

  Lemma future_closed P: closed (future P).
  Proof.
    ii. auto.
  Qed.


  Lemma meet_meet A (B: A -> Type) (k: forall a (b: B a), t)
    :
      meet (fun a => meet (k a)) =
      meet (fun (ab: sigT B) => let (a, b) := ab in k a b).
  Proof.
    eapply le_Antisymmetric.
    - ii. destruct a as [a b]. eapply IN; eauto.
    - ii. specialize (IN (existT _ a a0)). eauto.
  Qed.

  Lemma meet_join A (B: A -> Type) (k: forall a (b: B a), t)
    :
      meet (fun a => join (k a)) =
      join (fun (f: forall a, B a) => meet (fun a => k a (f a))).
  Proof.
    eapply le_Antisymmetric.
    - unfold join, meet. ii. eapply forall_exists_commute in IN; eauto.
    - unfold join, meet. ii. revert a. eapply forall_exists_commute_rev; eauto.
  Qed.

  Lemma join_meet A (B: A -> Type) (k: forall a (b: B a), t)
    :
      join (fun a => meet (k a)) =
      meet (fun (f: forall a, B a) => join (fun a => k a (f a))).
  Proof.
    eapply le_Antisymmetric.
    - unfold join, meet. ii. eapply exists_forall_commute in IN; eauto.
    - unfold join, meet. ii. eapply exists_forall_commute_rev; eauto.
  Qed.

  Lemma join_join A (B: A -> Type) (k: forall a (b: B a), t)
    :
      join (fun a => join (k a)) =
      join (fun (ab: sigT B) => let (a, b) := ab in k a b).
  Proof.
    unfold join. eapply le_Antisymmetric.
    - ii. des. exists (existT _ a a0). eauto.
    - ii. des. destruct a as [a b]. eauto.
  Qed.

  Lemma join_next A k
        (INHABITED: inhabited A)
    :
      join (fun a: A => next (k a)) = next (join k).
  Proof.
    destruct INHABITED. unfold next, join.
    eapply le_Antisymmetric.
    - ii. des. exists i0. esplits; eauto.
    - ii. des. esplits; eauto.
  Qed.

  Lemma join_empty A k
        (INHABITED: ~ inhabited A)
    :
      @join A k = bot.
  Proof.
    eapply le_Antisymmetric.
    - eapply join_supremum. i. exfalso. eapply INHABITED. econs; eauto.
    - eapply bot_spec.
  Qed.

  Lemma meet_empty A k
        (INHABITED: ~ inhabited A)
    :
      @meet A k = top.
  Proof.
    eapply le_Antisymmetric.
    - eapply top_spec.
    - eapply meet_infimum. i. exfalso. eapply INHABITED. econs; eauto.
  Qed.

  Lemma next_meet A k
    :
      le (next (meet k)) (meet (fun a: A => next (k a))).
  Proof.
    unfold next. ii. des. exists i0. splits; auto.
  Qed.

  Remark not_meet_next:
    ~ (forall A k (CLOSED: forall a, closed (k a)),
          le (meet (fun a: A => next (k a))) (next (meet k))).
  Proof.
    set (nextn := @nat_rect (fun _ => t) top (fun n s => next s)).
    assert (CLOSED: forall n, closed (nextn n)).
    { induction n.
      { ss. apply top_closed. }
      { ss. apply next_closed; auto. }
    }
    assert (NAT: forall n, nextn n (Ordinal.from_nat n)).
    { induction n; ss. exists (Ordinal.from_nat n).
      split; auto. eapply Ordinal.S_lt. }
    ii. hexploit (H nat (@nat_rect (fun _ => t) top (fun n s => next s))); auto.
    i. ss. exploit (H0 Ordinal.omega).
    { unfold meet. i.
      assert (nextn (S a) Ordinal.omega); auto.
      eapply CLOSED.
      { eapply NAT. }
      { eapply Ordinal.join_upperbound. }
    }
    { i. unfold next at 1 in x0. unfold meet, Ordinal.omega in x0. des.
      eapply Ordinal.lt_not_le.
      { eapply x1. }
      { eapply Ordinal.join_supremum. i.
        specialize (x0 a).
        clear - x0. revert i0 x0. induction a; ss.
        { i. eapply Ordinal.O_bot. }
        { i. unfold next in x0. des. eapply IHa in x0.
          eapply Ordinal.S_spec in x1. etransitivity.
          { rewrite <- Ordinal.S_le_mon. apply x0. }
          { apply x1. }
        }
      }
    }
  Qed.


  Lemma next_future P: future (next P) = future P.
  Proof.
    unfold next, future. eapply le_Antisymmetric.
    - ii. des. esplits; eauto.
    - ii. des. esplits; eauto. eapply (Ordinal.S_lt).
  Qed.

  Lemma future_future P: future (future P) = future P.
  Proof.
    eapply le_Antisymmetric.
    - unfold future. ii. des. esplits; eauto.
    - eapply future_incl; eauto.
  Qed.

  Lemma join_future A k
    :
      join (fun a: A => future (k a)) = future (join k).
  Proof.
    unfold join, future. eapply le_Antisymmetric.
    - ii. des. esplits; eauto.
    - ii. des. esplits; eauto.
  Qed.

  Lemma future_meet A k
    :
      le (future (meet k)) (meet (fun a: A => future (k a))).
  Proof.
    unfold future. ii. des. esplits; eauto.
  Qed.

  Lemma meet_future A k (CLOSED: forall a, closed (k a))
    :
      meet (fun a: A => future (k a)) = future (meet k).
  Proof.
    unfold meet, future. eapply le_Antisymmetric.
    - ii. eapply choice in IN. des.
      exists (Ordinal.join f). i. eapply CLOSED; eauto. eapply Ordinal.join_upperbound.
    - eapply future_meet.
  Qed.
End iProp.
