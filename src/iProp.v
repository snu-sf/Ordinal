Require Import sflib.

Require Import Coq.Classes.RelationClasses Coq.Relations.Relation_Operators Coq.Classes.Morphisms ChoiceFacts. (* TODO: Use Morphisms *)
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.
Require Import Program.

Require Import Ordinal.

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
  Definition le (P0 P1: t): Prop := forall o (IN: P0 o), P1 o.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. eauto.
  Qed.
  Next Obligation.
  Proof.
    ii. eauto.
  Qed.

  Let eq (P0 P1: t): Prop := forall o, P0 o <-> P1 o.

  Global Program Instance le_Equivalence: Equivalence eq.
  Next Obligation.
  Proof.
    ii. reflexivity.
  Qed.
  Next Obligation.
  Proof.
    ii. symmetry. auto.
  Qed.
  Next Obligation.
  Proof.
    ii. etransitivity; eauto.
  Qed.


  Global Program Instance le_Antisymmetric: @Antisymmetric _ eq _ le.
  Next Obligation.
  Proof.
    ii. split; auto.
  Qed.

  (* axioms needed *)
  Lemma eq_eq P0 P1 (EQ: eq P0 P1): P0 = P1.
  Proof.
    extensionality i. eapply propositional_extensionality. auto.
  Qed.

  Let ge := flip le.

  Let ge_Antisymmetric P0 P1 (GE: ge P0 P1 /\ ge P1 P0): eq P0 P1.
  Proof.
    ii. des. split.
    { eapply GE0. }
    { eapply GE. }
  Qed.

  Definition closed (P: t): Prop :=
    forall o0 o1 (IN: P o0) (LE: Ordinal.le o0 o1), P o1.

  Definition next (P: t): t :=
    fun o1 => exists o0, P o0 /\ Ordinal.lt o0 o1.

  Lemma next_le P (CLOSED: closed P): le (next P) P.
  Proof.
    unfold next in *. ii. des. eapply CLOSED; eauto. eapply Ordinal.lt_le; eauto.
  Qed.

  Lemma next_mon P0 P1 (LE: le P0 P1): le (next P0) (next P1).
  Proof.
    unfold next in *. ii. des. exists o0; eauto.
  Qed.

  Lemma next_closed P: closed (next P).
  Proof.
    ii. unfold next in *. des. esplits; eauto.
    eapply Ordinal.lt_le_lt; eauto.
  Qed.


  Definition top: t := fun _ => True.

  Lemma top_spec P: le P top.
  Proof.
    ss.
  Qed.

  Lemma top_closed: closed top.
  Proof.
    ss.
  Qed.


  Definition bot: t := fun _ => False.

  Lemma bot_spec P: le bot P.
  Proof.
    ss.
  Qed.

  Lemma bot_closed: closed bot.
  Proof.
    ss.
  Qed.


  Definition lt (P0 P1: t): Prop := le P0 (next P1).

  Lemma lt_le P0 P1 (LT: lt P0 P1) (CLOSED: closed P1): le P0 P1.
  Proof.
    ii. eapply next_le.
    { eapply CLOSED. }
    eapply LT. auto.
  Qed.

  Lemma lt_le_lt P0 P1 P2 (LT: lt P0 P1) (LE: le P1 P2): lt P0 P2.
  Proof.
    ii. eapply LT in IN. eapply next_mon; eauto.
  Qed.

  Lemma le_lt_lt P0 P1 P2 (LE: le P0 P1) (LT: lt P1 P2): lt P0 P2.
  Proof.
    ii. eapply LE in IN. eapply LT; eauto.
  Qed.

  Lemma lob_next P0 (LE: le P0 (next P0)): le P0 bot.
  Proof.
    ii. exfalso.
    eapply (well_founded_induction Ordinal.lt_well_founded (fun i => ~ P0 i)); eauto.
    ii. eapply LE in H0. destruct H0. des. eapply H; eauto.
  Qed.

  Lemma lob_lt P0 (LT: lt P0 P0): le P0 bot.
  Proof.
    eapply lob_next. eauto.
  Qed.

  Lemma lt_lt_lt P0 P1 P2 (LT0: lt P0 P1) (LT1: lt P1 P2): lt P0 P2.
  Proof.
    ii. eapply LT0 in IN. destruct IN. des.
    eapply LT1 in H. destruct H. des. exists x0.
    split; auto. etransitivity; eauto.
  Qed.


  Definition meet A (Ps: A -> t): t :=
    fun o => forall a, Ps a o.

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
    fun o => exists a, Ps a o.

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


  Definition future (P: t): t :=
    fun o1 => exists o0, P o0.

  Lemma future_mon P0 P1 (LE: le P0 P1): le (future P0) (future P1).
  Proof.
    unfold future in *. ii. des. eauto.
  Qed.

  Lemma future_le P: le P (future P).
  Proof.
    unfold future. ii. eauto.
  Qed.

  Lemma future_closed P: closed (future P).
  Proof.
    ii. auto.
  Qed.


  Lemma meet_meet A (B: A -> Type) (k: forall a (b: B a), t)
    :
      eq (meet (fun a => meet (k a)))
         (meet (fun (ab: sigT B) => let (a, b) := ab in k a b)).
  Proof.
    eapply le_Antisymmetric.
    - ii. destruct a as [a b]. eapply IN; eauto.
    - ii. specialize (IN (existT _ a a0)). eauto.
  Qed.

  Lemma meet_join A (B: A -> Type) (k: forall a (b: B a), t)
    :
      eq (meet (fun a => join (k a)))
         (join (fun (f: forall a, B a) => meet (fun a => k a (f a)))).
  Proof.
    eapply le_Antisymmetric.
    - unfold join, meet. ii. eapply forall_exists_commute in IN; eauto.
    - unfold join, meet. ii. revert a. eapply forall_exists_commute_rev; eauto.
  Qed.

  Lemma join_meet A (B: A -> Type) (k: forall a (b: B a), t)
    :
      eq (join (fun a => meet (k a)))
         (meet (fun (f: forall a, B a) => join (fun a => k a (f a)))).
  Proof.
    eapply le_Antisymmetric.
    - unfold join, meet. ii. eapply exists_forall_commute in IN; eauto.
    - unfold join, meet. ii. eapply exists_forall_commute_rev; eauto.
  Qed.

  Lemma join_join A (B: A -> Type) (k: forall a (b: B a), t)
    :
      eq (join (fun a => join (k a)))
         (join (fun (ab: sigT B) => let (a, b) := ab in k a b)).
  Proof.
    unfold join. eapply le_Antisymmetric.
    - ii. des. exists (existT _ a a0). eauto.
    - ii. des. destruct a as [a b]. eauto.
  Qed.

  Lemma join_next A k
        (INHABITED: inhabited A)
    :
      eq (join (fun a: A => next (k a))) (next (join k)).
  Proof.
    destruct INHABITED. unfold next, join.
    eapply le_Antisymmetric.
    - ii. des. exists o0. esplits; eauto.
    - ii. des. esplits; eauto.
  Qed.

  Lemma join_empty A k
        (INHABITED: ~ inhabited A)
    :
      eq (@join A k) bot.
  Proof.
    eapply le_Antisymmetric.
    - eapply join_supremum. i. exfalso. eapply INHABITED. econs; eauto.
    - eapply bot_spec.
  Qed.

  Lemma meet_empty A k
        (INHABITED: ~ inhabited A)
    :
      eq (@meet A k) top.
  Proof.
    eapply le_Antisymmetric.
    - eapply top_spec.
    - eapply meet_infimum. i. exfalso. eapply INHABITED. econs; eauto.
  Qed.

  Lemma next_meet A k
    :
      le (next (meet k)) (meet (fun a: A => next (k a))).
  Proof.
    unfold next. ii. des. exists o0. splits; auto.
  Qed.

  Remark not_meet_next:
    ~ (forall A k (CLOSED: forall a, closed (k a)),
          le (meet (fun a: A => next (k a))) (next (meet k))).
  Proof.
    set (nextn := @nat_rect (fun _ => t) top (fun n s => next s)).
    assert (CLOSED: forall n, closed (nextn n)).
    { induction n.
      { ss. }
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
        clear - x0. revert o0 x0. induction a; ss.
        { i. eapply Ordinal.O_bot. }
        { i. unfold next in x0. des. eapply IHa in x0.
          eapply Ordinal.S_spec in x1. etransitivity.
          { rewrite <- Ordinal.S_le_mon. apply x0. }
          { apply x1. }
        }
      }
    }
  Qed.


  Lemma next_future P: eq (future (next P)) (future P).
  Proof.
    unfold next, future. eapply le_Antisymmetric.
    - ii. des. esplits; eauto.
    - ii. des. esplits; eauto. eapply (Ordinal.S_lt).
  Qed.

  Lemma future_future P: eq (future (future P)) (future P).
  Proof.
    eapply le_Antisymmetric.
    - unfold future. ii. des. esplits; eauto.
    - eapply future_le; eauto.
  Qed.

  Lemma join_future A k
    :
      eq (join (fun a: A => future (k a))) (future (join k)).
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
      eq (meet (fun a: A => future (k a))) (future (meet k)).
  Proof.
    unfold meet, future. eapply le_Antisymmetric.
    - ii. eapply choice in IN. des.
      exists (Ordinal.join f). i. eapply CLOSED; eauto. eapply Ordinal.join_upperbound.
    - eapply future_meet.
  Qed.

  Lemma union_closed (P0 P1: t) (CLOSED0: closed P0) (CLOSED1: closed P1):
    closed (fun i => P0 i \/ P1 i).
  Proof.
    ii. des.
    - left. eapply CLOSED0; eauto.
    - right. eapply CLOSED1; eauto.
  Qed.

  Lemma inter_closed (P0 P1: t) (CLOSED0: closed P0) (CLOSED1: closed P1):
    closed (fun i => P0 i /\ P1 i).
  Proof.
    ii. des. split.
    - eapply CLOSED0; eauto.
    - eapply CLOSED1; eauto.
  Qed.


  Definition closure (P: t): t :=
    fun o1 => exists o0, P o0 /\ Ordinal.le o0 o1.

  Lemma closure_le P: le P (closure P).
  Proof.
    ii. exists o. split; auto. reflexivity.
  Qed.

  Lemma closure_mon P0 P1 (LE: le P0 P1): le (closure P0) (closure P1).
  Proof.
    ii. destruct IN. des. eapply LE in H. exists x; eauto.
  Qed.

  Lemma closure_mon_eq P0 P1 (EQ: eq P0 P1): eq (closure P0) (closure P1).
  Proof.
    eapply le_Antisymmetric.
    { eapply closure_mon. ii. apply EQ. auto. }
    { eapply closure_mon. ii. apply EQ. auto. }
  Qed.

  Lemma closure_closed P: closed (closure P).
  Proof.
    ii. destruct IN. des.
    exists x. split; auto. transitivity o0; auto.
  Qed.

  Lemma closure_eq_closed P (CLOSED: le (closure P) P): closed P.
  Proof.
    ii. eapply CLOSED. exists o0; auto.
  Qed.

  Lemma closed_closure_eq P (CLOSED: closed P): le (closure P) P.
  Proof.
    ii. destruct IN. des. eapply CLOSED; eauto.
  Qed.


  Definition inhabited (P: t) := exists o, P o.

  Lemma le_inhabited P0 P1 (LE: le P0 P1) (INHABITED: inhabited P0):
    inhabited P1.
  Proof.
    destruct INHABITED. exists x. auto.
  Qed.

  Lemma inhabited_future_top P (INHABITED: inhabited P):
    le top (future P).
  Proof.
    ii. eauto.
  Qed.

  Lemma future_top_inhabited P (INHABITED: le top (future P)):
    inhabited P.
  Proof.
    exploit (INHABITED (Ordinal.O)); ss.
  Qed.

  Lemma top_inhabited: inhabited top.
  Proof.
    exists Ordinal.O. ss.
  Qed.

  Lemma next_inhabited P (INHABITED: inhabited P): inhabited (next P).
  Proof.
    destruct INHABITED. exists (Ordinal.S x).
    exists x. splits; auto. eapply Ordinal.S_lt.
  Qed.

  Lemma next_inhabited_rev P (INHABITED: inhabited (next P)): inhabited P.
  Proof.
    destruct INHABITED. destruct H. des. exists x0; eauto.
  Qed.

  Lemma future_inhabited P (INHABITED: inhabited P): inhabited (future P).
  Proof.
    eapply le_inhabited; eauto. eapply future_le.
  Qed.

  Lemma future_inhabited_rev P (INHABITED: inhabited (future P)):
    inhabited P.
  Proof.
    destruct INHABITED. destruct H. exists x0; auto.
  Qed.

  Lemma meet_inhabited A (Ps: A -> t)
        (INHABITED: forall a, inhabited (Ps a))
        (CLOSED: forall a, closed (Ps a)):
    inhabited (meet Ps).
  Proof.
    hexploit (choice (fun a o => Ps a o) INHABITED). i. des.
    exists (Ordinal.join f). ii.
    eapply CLOSED; eauto. eapply Ordinal.join_upperbound.
  Qed.

  Lemma meet_inhabited_rev A (Ps: A -> t)
        (INHABITED: inhabited (meet Ps)):
    forall a, inhabited (Ps a).
  Proof.
    destruct INHABITED. ii. exists x. eauto.
  Qed.

  Lemma join_inhabited A (Ps: A -> t)
        a
        (INHABITED: inhabited (Ps a)):
    inhabited (join Ps).
  Proof.
    eapply le_inhabited; eauto. eapply join_upperbound.
  Qed.

  Lemma join_inhabited_rev A (Ps: A -> t)
        (INHABITED: inhabited (join Ps)):
    exists a, inhabited (Ps a).
  Proof.
    destruct INHABITED. destruct H. exists x0, x. auto.
  Qed.

  Definition upper (o0: Ordinal.t): t := fun o1 => Ordinal.le o0 o1.

  Lemma upper_inhabited o0: inhabited (upper o0).
  Proof.
    exists o0. reflexivity.
  Qed.

  Lemma upper_closed o0: closed (upper o0).
  Proof.
    ii. transitivity o1; auto.
  Qed.

  Lemma le_upper i (P: t) (IN: P i) (CLOSED: closed P): le (upper i) P.
  Proof.
    ii. eapply CLOSED; eauto.
  Qed.

  Definition next_o (P: t) (o: Ordinal.t): t := Ordinal.rec (closure P) next meet o.

  Lemma next_o_closed (P: t) o: closed (next_o P o).
  Proof.
    eapply (Ordinal.rec_wf (closure P) next meet ge closed).
    { i. unfold ge in *. transitivity d1; auto. }
    { i. eapply meet_lowerbound. }
    { i. eapply meet_infimum. auto. }
    { i. eapply meet_closed. auto. }
    { eapply closure_closed. }
    { i. eapply next_closed. }
    { i. eapply next_mon. auto. }
  Qed.

  Lemma next_o_le P o (CLOSED: closed P): le (next_o P o) P.
  Proof.
    transitivity (closure P).
    2: { eapply closed_closure_eq. auto. }
    eapply (Ordinal.rec_le_base (closure P) next meet ge (fun _ => True)).
    { i. unfold ge in *. transitivity d1; auto. }
    { i. eapply meet_lowerbound. }
    { i. eapply meet_infimum. auto. }
    { ss. }
    { ss. }
    { ss. }
    { i. eapply next_mon. auto. }
  Qed.

  Let orec_mon P0 P1 o (LE: le P0 P1):
    le (Ordinal.rec P0 next meet o) (Ordinal.rec P1 next meet o).
  Proof.
    eapply (@Ordinal.rec_mon t ge meet P1 next P0 next); auto.
    { i. eapply next_mon. auto. }
    { econs; ii; eauto. }
    { i. eapply meet_lowerbound. }
    { i. eapply meet_infimum. auto. }
  Qed.

  Let orec_mon_eq P0 P1 o (EQ: eq P0 P1):
    eq (Ordinal.rec P0 next meet o) (Ordinal.rec P1 next meet o).
  Proof.
    eapply le_Antisymmetric.
    { eapply orec_mon. ii. apply EQ. auto. }
    { eapply orec_mon. ii. apply EQ. auto. }
  Qed.

  Lemma next_o_closure_mon P0 P1 (LE: le (closure P0) (closure P1)) o:
    le (next_o P0 o) (next_o P1 o).
  Proof.
    eapply orec_mon. auto.
  Qed.

  Lemma next_o_mon P0 P1 (LE: le P0 P1) o: le (next_o P0 o) (next_o P1 o).
  Proof.
    eapply next_o_closure_mon.
    eapply closure_mon; eauto.
  Qed.

  Lemma next_o_closure_mon_eq P0 P1 (EQ: eq (closure P0) (closure P1)) o:
    eq (next_o P0 o) (next_o P1 o).
  Proof.
    eapply orec_mon_eq. auto.
  Qed.

  Lemma next_o_mon_eq P0 P1 (EQ: eq P0 P1) o:
    eq (next_o P0 o) (next_o P1 o).
  Proof.
    eapply le_Antisymmetric.
    { eapply next_o_mon. ii. apply EQ. auto. }
    { eapply next_o_mon. ii. apply EQ. auto. }
  Qed.

  Lemma next_o_decr P o0 o1 (LE: Ordinal.le o0 o1): le (next_o P o1) (next_o P o0).
  Proof.
    eapply (Ordinal.rec_le (closure P) next meet ge (fun _ => True)); auto.
    { i. unfold ge in *. transitivity d1; auto. }
    { i. eapply meet_lowerbound. }
    { i. eapply meet_infimum. auto. }
    { i. eapply next_mon. auto. }
  Qed.

  Lemma closure_future P: le (closure (future P)) (future (closure P)).
  Proof.
    ii. inv IN. des. inv H.
    exists x0, x0. split; auto. reflexivity.
  Qed.

  Lemma closure_next P: le (closure (next P)) (next (closure P)).
  Proof.
    ii. eapply next_mon.
    { eapply closure_le. }
    { eapply closed_closure_eq; eauto. eapply next_closed. }
  Qed.

  Lemma closure_next_o o P: le (closure (next_o P o)) (next_o (closure P) o).
  Proof.
    induction o. ii. ss. inv IN. des. ii. destruct a.
    { specialize (H0 true). ss. exists x. split; auto. }
    { specialize (H0 false). ss. ii. specialize (H0 a). ss.
      eapply next_mon.
      { eapply H. }
      { eapply closure_next. eexists. eauto. }
    }
  Qed.

  Lemma next_o_O P: eq (next_o P Ordinal.O) (closure P).
  Proof.
    eapply ge_Antisymmetric.
    eapply (Ordinal.rec_O (closure P) next meet ge (fun _ => True)); auto.
    { i. unfold ge in *. reflexivity. }
    { i. unfold ge in *. transitivity d1; auto. }
    { i. eapply meet_lowerbound. }
    { i. eapply meet_infimum. auto. }
    { i. eapply next_mon. auto. }
  Qed.

  Lemma next_o_O_closed P (CLOSED: closed P): eq (next_o P Ordinal.O) P.
  Proof.
    transitivity (closure P).
    { eapply next_o_O. }
    { split.
      { eapply closed_closure_eq. auto. }
      { eapply closure_le. }
    }
  Qed.

  Lemma next_o_closure_eq P o: eq (next_o P o) (next_o (closure P) o).
  Proof.
    eapply next_o_closure_mon_eq. eapply le_Antisymmetric.
    { eapply closure_le. }
    { eapply closed_closure_eq. eapply closure_closed. }
  Qed.

  Lemma next_o_S o P:
    eq (next_o P (Ordinal.S o)) (next (next_o P o)).
  Proof.
    eapply ge_Antisymmetric.
    eapply (Ordinal.rec_S (closure P) next meet ge closed); auto.
    { i. unfold ge in *. transitivity d1; auto. }
    { i. eapply meet_lowerbound. }
    { i. eapply meet_infimum. auto. }
    { i. eapply meet_closed. auto. }
    { eapply closure_closed. }
    { i. eapply next_closed. }
    { i. eapply next_le. auto. }
    { i. eapply next_mon. auto. }
  Qed.

  Lemma next_o_app o0 o1 P:
    eq (next_o P (Ordinal.add o0 o1)) (next_o (next_o P o0) o1).
  Proof.
    hexploit (Ordinal.rec_app next meet ge closed); eauto.
    { i. unfold ge in *. reflexivity. }
    { i. unfold ge in *. transitivity d1; auto. }
    { i. eapply meet_lowerbound. }
    { i. eapply meet_infimum. auto. }
    { i. eapply meet_closed. auto. }
    { i. eapply next_closed. }
    { i. eapply next_le. auto. }
    { i. eapply next_mon. auto. }
    { eapply closure_closed. }
    i. eapply ge_Antisymmetric in H.
    transitivity (Ordinal.rec (next_o P o0) next meet o1).
    { eapply H. }
    eapply orec_mon_eq. eapply le_Antisymmetric.
    { eapply closure_le. }
    { eapply closed_closure_eq. eapply next_o_closed. }
  Qed.

  Section KAPPA.
    Variable X: Type.

    Definition kappa := upper (Ordinal.kappa X).

    Lemma kappa_closed: closed kappa.
    Proof.
      eapply upper_closed.
    Qed.

    Lemma kappa_inhabited: inhabited kappa.
    Proof.
      eapply upper_inhabited.
    Qed.

    Lemma kappa_top: lt kappa top.
    Proof.
      ii. exists Ordinal.O. split; ss.
      eapply Ordinal.lt_le_lt.
      { eapply Ordinal.kappa_O. }
      { eapply IN. }
    Qed.

    Lemma kappa_next P (LT: lt kappa P): lt kappa (next P).
    Proof.
      eapply le_upper.
      2: { eapply next_closed. }
      destruct (LT (Ordinal.kappa X)).
      { unfold kappa. reflexivity. }
      des. eapply Ordinal.kappa_S in H0.
      exists (Ordinal.S x). splits; auto.
      exists x. splits; auto. eapply Ordinal.S_lt.
    Qed.

    Lemma kappa_meet (Ps: X -> t) (LT: forall x, lt kappa (Ps x))
          (CLOSED: forall x, closed (Ps x)):
      lt kappa (meet Ps).
    Proof.
      eapply le_upper.
      2: { eapply next_closed. }
      hexploit (choice (fun (x: X) (i: Ordinal.t) =>
                          Ps x i /\ Ordinal.lt i (Ordinal.kappa X))).
      { i. destruct (LT x (Ordinal.kappa X)).
        { unfold kappa. reflexivity. }
        des. eauto. }
      i. des. exists (Ordinal.join f). split.
      { ii. destruct (H a). des. eapply CLOSED; eauto.
        eapply Ordinal.join_upperbound. }
      { eapply Ordinal.kappa_join.
        { ii. eapply choice; eauto. }
        { i. eapply H. }
      }
    Qed.

    Lemma kappa_join A (Ps: A -> t) (LT: forall a, lt kappa (Ps a))
          (INHABITED: Coq.Init.Logic.inhabited A):
      lt kappa (join Ps).
    Proof.
      eapply le_upper.
      2: { eapply next_closed. }
      destruct INHABITED. destruct (LT X0 (Ordinal.kappa X)).
      { unfold kappa. reflexivity. }
      des. exists x. splits; eauto. ii. exists X0; auto.
    Qed.
  End KAPPA.
End iProp.
