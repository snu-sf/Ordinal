Require Import sflib.

Require Import Coq.Classes.RelationClasses Coq.Relations.Relation_Operators Coq.Classes.Morphisms. (* TODO: Use Morphisms *)
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.
Require Import Program.

Require Import Ordinal.

Set Implicit Arguments.
Set Primitive Projections.

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

  Definition meet A (Ps: A -> t): t :=
    fun i => forall a, Ps a i.

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

  Definition top: t := meet (False_rect _).

  Lemma top_spec P: le P top.
  Proof.
    eapply meet_infimum. i. ss.
  Qed.

  Definition next_o (P: t) (o: Ordinal.t): t := Ordinal.rec meet next P o.

  (* Lemma next_o_le (P: t) (o0 o1: Ordinal.t) (LE: Ordinal.le o0 o1): *)
  (*   le (next_o P o1) (next_o P o0). *)
  (* Proof. *)
  (*   eapply (@Ordinal.rec_le t ge meet P next); auto. *)
  (*   - eapply flip_PreOrder. eapply le_PreOrder. *)
  (*   - i. eapply meet_lowerbound. *)
  (*   - i. eapply meet_infimum. auto. *)
  (*   - i. eapply next_mon; auto. *)
  (* Qed. *)

  (* Lemma next_o_eq (P: t) (o0 o1: Ordinal.t) (EQ: Ordinal.eq o0 o1): *)
  (*   next_o P o1 = next_o P o0. *)
  (* Proof. *)
  (*   eapply le_Antisymmetric. *)
  (*   - eapply next_o_le. eapply EQ. *)
  (*   - eapply next_o_le. eapply EQ. *)
  (* Qed. *)

  (* Lemma next_o_mon P0 P1 (LE: le P0 P1) o: le (next_o P0 o) (next_o P1 o). *)
  (* Proof. *)
  (*   revert o P0 P1 LE. induction o. i. ss. *)
  (*   eapply meet_infimum. i. etransitivity; [eapply (meet_lowerbound a)|]. *)
  (*   destruct a; auto. *)
  (*   eapply meet_infimum. i. etransitivity; [eapply (meet_lowerbound a)|]. *)
  (*   eapply next_mon. eauto. *)
  (* Qed. *)
End iProp.

  (* Definition bot: t := join (False_rect _). *)

  (* Lemma bot_spec P: le bot P. *)
  (* Proof. *)
  (*   eapply join_supremum. i. ss. *)
  (* Qed. *)

  (* Definition future (P: t): t := *)
  (*   fun i1 => exists i0, P i0. *)

  (* Lemma future_mon P0 P1 (LE: le P0 P1): le (future P0) (future P1). *)
  (* Proof. *)
  (*   unfold future in *. ii. des. eauto. *)
  (* Qed. *)

  (* Lemma future_incl P: le P (future P). *)
  (* Proof. *)
  (*   unfold future. ii. eauto. *)
  (* Qed. *)

  (* Lemma meet_mon A Ps0 Ps1 (LE: forall (a: A), le (Ps0 a) (Ps1 a)): le (meet Ps0) (meet Ps1). *)
  (* Proof. *)
  (*   unfold meet in *. ii. eapply LE; eauto. *)
  (* Qed. *)

  (* Definition join A (Ps: A -> t): t := *)
  (*   fun i => exists a, Ps a i. *)

  (* Lemma join_mon A Ps0 Ps1 (LE: forall (a: A), le (Ps0 a) (Ps1 a)): le (join Ps0) (join Ps1). *)
  (* Proof. *)
  (*   unfold join in *. ii. des. eapply LE in IN. eauto. *)
  (* Qed. *)

  (* Lemma join_upperbound A (Ps: A -> t) a *)
  (*   : *)
  (*     le (Ps a) (join Ps). *)
  (* Proof. *)
  (*   unfold join. ii. eauto. *)
  (* Qed. *)

  (* Lemma join_supremum A (Ps: A -> t) P *)
  (*       (LE: forall a, le (Ps a) P) *)
  (*   : *)
  (*     le (join Ps) P. *)
  (* Proof. *)
  (*   unfold join. ii. des. eapply LE; eauto. *)
  (* Qed. *)

  (* Lemma meet_meet A (B: A -> Type) (k: forall a (b: B a), t) *)
  (*   : *)
  (*     meet (fun a => meet (k a)) = *)
  (*     meet (fun (ab: sigT B) => let (a, b) := ab in k a b). *)
  (* Proof. *)
  (*   eapply le_Antisymmetric. *)
  (*   - ii. destruct a as [a b]. eapply IN; eauto. *)
  (*   - ii. specialize (IN (existT _ a a0)). eauto. *)
  (* Qed. *)

(*   Lemma meet_join A (B: A -> Type) (k: forall a (b: B a), t) *)
(*     : *)
(*       meet (fun a => join (k a)) = *)
(*       join (fun (f: forall a, B a) => meet (fun a => k a (f a))). *)
(*   Proof. *)
(*     eapply le_Antisymmetric. *)
(*     - unfold join, meet. ii. eapply forall_exists_commute in IN; eauto. *)
(*     - unfold join, meet. ii. revert a. eapply forall_exists_commute_rev; eauto. *)
(*   Qed. *)

(*   Lemma join_meet A (B: A -> Type) (k: forall a (b: B a), t) *)
(*     : *)
(*       join (fun a => meet (k a)) = *)
(*       meet (fun (f: forall a, B a) => join (fun a => k a (f a))). *)
(*   Proof. *)
(*     eapply le_Antisymmetric. *)
(*     - unfold join, meet. ii. eapply exists_forall_commute in IN; eauto. *)
(*     - unfold join, meet. ii. eapply exists_forall_commute_rev; eauto. *)
(*   Qed. *)

(*   Lemma join_join A (B: A -> Type) (k: forall a (b: B a), t) *)
(*     : *)
(*       join (fun a => join (k a)) = *)
(*       join (fun (ab: sigT B) => let (a, b) := ab in k a b). *)
(*   Proof. *)
(*     unfold join. eapply le_Antisymmetric. *)
(*     - ii. des. exists (existT _ a a0). eauto. *)
(*     - ii. des. destruct a as [a b]. eauto. *)
(*   Qed. *)

(*   Lemma join_next A k *)
(*         (INHABITED: inhabited A) *)
(*     : *)
(*       join (fun a: A => next (k a)) = next (join k). *)
(*   Proof. *)
(*     destruct INHABITED. unfold next, join. *)
(*     eapply le_Antisymmetric. *)
(*     - ii. des. exists i0. esplits; eauto. *)
(*     - ii. des. esplits; eauto. *)
(*   Qed. *)

(*   Definition upper (o0: Index.t): t := *)
(*     fun o1 => Index.le o0 o1. *)

(*   Lemma next_upper o: upper (Index.S o) = next (upper o). *)
(*   Proof. *)
(*     unfold next, upper. eapply le_Antisymmetric. *)
(*     - ii. exists o. splits. *)
(*       + reflexivity. *)
(*       + eapply Index.lt_le_lt. *)
(*         * eapply Index.S_lt. *)
(*         * eauto. *)
(*     - ii. des. eapply Index.S_spec in IN0. *)
(*       etransitivity; eauto. eapply Index.S_spec. *)
(*       eapply Index.le_lt_lt; eauto. eapply Index.S_lt. *)
(*   Qed. *)

(*   Lemma meet_upper A (k: A -> Index.t): meet (fun a => upper (k a)) = upper (Index.join k). *)
(*   Proof. *)
(*     unfold meet, upper. eapply le_Antisymmetric. *)
(*     - ii. eapply Index.join_supremum; eauto. *)
(*     - ii. etransitivity. *)
(*       + eapply Index.join_upperbound; eauto. *)
(*       + auto. *)
(*   Qed. *)

(*   Lemma future_upper o: future (upper o) = upper Index.O. *)
(*   Proof. *)
(*     unfold future, upper. eapply le_Antisymmetric. *)
(*     - ii. eapply Index.O_bot. *)
(*     - ii. exists o. reflexivity. *)
(*   Qed. *)

(*   Lemma join_upper A (k: A -> Index.t) (INHABITED: inhabited A): *)
(*     exists o, join (fun a => upper (k a)) = upper o /\ Index.set_meet k o. *)
(*   Proof. *)
(*     unfold join, upper. *)
(*     exploit Index.set_meet_exists; eauto. i. des. esplits; eauto. clear INHABITED. *)
(*     eapply le_Antisymmetric. *)
(*     - ii. des. destruct x0. des. clarify. *)
(*       hexploit (H0 (k a)); eauto. i. etransitivity; eauto. *)
(*     - ii. destruct x0. des. clarify. eauto. *)
(*   Qed. *)

(*   Lemma closed_upper P (CLOSED: closed P) *)


(*     - ii. eapply *)


(*         in IN. eauto. *)
(*       { *)

(*       eapply Index.join_upperbound. *)

(*       des. etransitivity; eauto. eapply Index.join_upperbound. *)

(*       esplits; eauto. *)

(*       exists o. splits. *)
(*       + reflexivity. *)
(*       + eapply Index.lt_le_lt. *)
(*         * eapply Index.S_lt. *)
(*         * eauto. *)
(*     - ii. des. eapply Index.S_spec in IN0. *)
(*       etransitivity; eauto. eapply Index.S_spec. *)
(*       eapply Index.le_lt_lt; eauto. eapply Index.S_lt. *)

(*                                            next (join k)) = *)

(*                                    next (join k) = upper (Index.S o). *)
(*   Proof. *)
(*     unfold next, upper. eapply le_Antisymmetric. *)
(*     - ii. des. eapply Index.S_spec in IN0. *)
(*       etransitivity; eauto. eapply Index.S_spec. *)
(*       eapply Index.le_lt_lt; eauto. eapply Index.S_lt. *)
(*     - ii. exists o. splits. *)
(*       + reflexivity. *)
(*       + eapply Index.lt_le_lt. *)
(*         * eapply Index.S_lt. *)
(*         * eauto. *)
(*   Qed. *)

(*   Lemma upper_closed o: closed (upper o). *)
(*   Proof. *)
(*     ii. eapply LE. *)

(*   Definition closure (P: t): t := *)
(*     fun i1 => exists i0, P i0 /\ Index.le i0 i1. *)

(*   Lemma next_closed P: closed (next P). *)
(*   Proof. *)
(*     unfold closed, next in *. ii. des. esplits; eauto. eapply Index.lt_le_lt; eauto. *)
(*   Qed. *)

(*   Lemma future_closed P: closed (future P). *)
(*     unfold closed, future in *. ii. des. esplits; eauto. *)
(*   Qed. *)

(*   Lemma closure_closed P: closed (closure P). *)
(*   Proof. *)
(*     unfold closure, closed. i. des. esplits; eauto. etransitivity; eauto. *)
(*   Qed. *)

(*   Lemma closure_mon P0 P1 (LE: le P0 P1): *)
(*     le (closure P0) (closure P1). *)
(*   Proof. *)
(*     unfold closure. ii. des. esplits; eauto. *)
(*   Qed. *)

(*   Lemma closure_incl P: le P (closure P). *)
(*   Proof. *)
(*     unfold closure. ii. esplits; eauto. reflexivity. *)
(*   Qed. *)

(*   Lemma closed_closure P (CLOSED: closed P): closure P = P. *)
(*   Proof. *)
(*     eapply le_Antisymmetric. *)
(*     - ii. unfold closure in *. des. eapply CLOSED; eauto. *)
(*     - eapply closure_incl. *)
(*   Qed. *)

(*   Lemma join_closed A (Ps: A -> t) (CLOSED: forall a, closed (Ps a)): closed (join Ps). *)
(*   Proof. *)
(*     unfold join. ii. des. esplits; eauto. eapply CLOSED; eauto. *)
(*   Qed. *)

(*   Lemma top_closed: closed top. *)
(*   Proof. *)
(*     eapply meet_closed; eauto. i. ss. *)
(*   Qed. *)

(*   Lemma bot_closed: closed bot. *)
(*   Proof. *)
(*     eapply join_closed; eauto. i. ss. *)
(*   Qed. *)

(*   Lemma join_empty A k *)
(*         (INHABITED: ~ inhabited A) *)
(*     : *)
(*       @join A k = bot. *)
(*   Proof. *)
(*     eapply le_Antisymmetric. *)
(*     - eapply join_supremum. i. exfalso. eapply INHABITED. econs; eauto. *)
(*     - eapply bot_spec. *)
(*   Qed. *)

(*   Lemma meet_empty A k *)
(*         (INHABITED: ~ inhabited A) *)
(*     : *)
(*       @meet A k = top. *)
(*   Proof. *)
(*     eapply le_Antisymmetric. *)
(*     - eapply top_spec. *)
(*     - eapply meet_infimum. i. exfalso. eapply INHABITED. econs; eauto. *)
(*   Qed. *)

(*   Lemma next_meet A k *)
(*     : *)
(*       le (next (meet k)) (meet (fun a: A => next (k a))). *)
(*   Proof. *)
(*     unfold next. ii. des. exists i0. splits; auto. *)
(*   Qed. *)

(*   Lemma meet_next A k (CLOSED: forall a, closed (k a)) *)
(*     : *)
(*       le (meet (fun a: A => next (k a))) (next (meet k)) . *)
(*   Proof. *)
(*     unfold next. ii. des. exists i0. splits; auto. *)
(*   Qed. *)

(*   Lemma next_future P: future (next P) = future P. *)
(*   Proof. *)
(*     unfold next, future. eapply le_Antisymmetric. *)
(*     - ii. des. esplits; eauto. *)
(*     - ii. des. esplits; eauto. eapply (Index.S_lt). *)
(*   Qed. *)

(*   Lemma future_future P: future (future P) = future P. *)
(*   Proof. *)
(*     eapply le_Antisymmetric. *)
(*     - unfold future. ii. des. esplits; eauto. *)
(*     - eapply future_incl; eauto. *)
(*   Qed. *)

(*   Lemma join_future A k *)
(*     : *)
(*       join (fun a: A => future (k a)) = future (join k). *)
(*   Proof. *)
(*     unfold join, future. eapply le_Antisymmetric. *)
(*     - ii. des. esplits; eauto. *)
(*     - ii. des. esplits; eauto. *)
(*   Qed. *)

(*   Lemma future_meet A k *)
(*     : *)
(*       le (future (meet k)) (meet (fun a: A => future (k a))). *)
(*   Proof. *)
(*     unfold future. ii. des. esplits; eauto. *)
(*   Qed. *)

(*   Lemma meet_future A k (CLOSED: forall a, closed (k a)) *)
(*     : *)
(*       meet (fun a: A => future (k a)) = future (meet k). *)
(*   Proof. *)
(*     unfold meet, future. eapply le_Antisymmetric. *)
(*     - ii. eapply choice in IN. des. *)
(*       exists (Index.join f). i. eapply CLOSED; eauto. eapply Index.join_upperbound. *)
(*     - eapply future_meet. *)
(*   Qed. *)

(*   Fixpoint next_n (P: t) (n: nat): t := *)
(*     match n with *)
(*     | S n' => next (next_n P n') *)
(*     | 0 => P *)
(*     end. *)

(*   Lemma next_n_mon P0 P1 (LE: le P0 P1) n: le (next_n P0 n) (next_n P1 n). *)
(*   Proof. *)
(*     induction n; ss. eapply next_mon; eauto. *)
(*   Qed. *)

(*   Lemma next_n_closed P (CLOSED: closed P) n: closed (next_n P n). *)
(*   Proof. *)
(*     destruct n; ss. eapply next_closed. *)
(*   Qed. *)

(*   Lemma next_n_incl P (CLOSED: closed P) n: le (next_n P n) P. *)
(*   Proof. *)
(*     induction n; ss. etransitivity; eauto. *)
(*     eapply next_incl; eauto. eapply next_n_closed; eauto. *)
(*   Qed. *)

(*   Lemma join_next_n A k n *)
(*         (INHABITED: inhabited A) *)
(*     : *)
(*       join (fun a: A => next_n (k a) n) = next_n (join k) n. *)
(*   Proof. *)
(*     induction n; ss. *)
(*     erewrite join_next; eauto. *)
(*     erewrite IHn. auto. *)
(*   Qed. *)

(*   Lemma next_n_meet A k n *)
(*     : *)
(*       le (next_n (meet k) n) (meet (fun a: A => next_n (k a) n)). *)
(*   Proof. *)
(*     induction n; ss. etransitivity. *)
(*     - eapply next_mon; eauto. *)
(*     - eapply next_meet; eauto. *)
(*   Qed. *)

(*   Lemma next_n_future P n: future (next_n P n) = future P. *)
(*   Proof. *)
(*     induction n; ss. erewrite next_future; eauto. *)
(*   Qed. *)

(*   Lemma next_n_next P n: next_n (next P) n = next (next_n P n). *)
(*   Proof. *)
(*     induction n; ss. erewrite IHn. ss. *)
(*   Qed. *)

(*   Definition next_omega P: t := meet (next_n P). *)

(*   Lemma next_omega_mon P0 P1 (LE: le P0 P1): le (next_omega P0) (next_omega P1). *)
(*   Proof. *)
(*     eapply meet_mon; eauto. i. eapply next_n_mon; eauto. *)
(*   Qed. *)

(*   Lemma next_omega_closed P (CLOSED: closed P): closed (next_omega P). *)
(*   Proof. *)
(*     eapply meet_closed. i. eapply next_n_closed; eauto. *)
(*   Qed. *)

(*   Lemma next_omega_incl P (CLOSED: closed P): le (next_omega P) P. *)
(*   Proof. *)
(*     eapply (@meet_lowerbound nat (next_n P) 0). *)
(*   Qed. *)

(*   Lemma next_omega_next P (CLOSED: closed P): next_omega (next P) = next_omega P. *)
(*   Proof. *)
(*     eapply le_Antisymmetric. *)
(*     - eapply meet_infimum. i. etransitivity. *)
(*       + eapply (@meet_lowerbound nat (next_n (next P)) a). *)
(*       + ss. erewrite next_n_next. eapply next_incl. *)
(*         eapply next_n_closed; auto. *)
(*     - eapply meet_infimum. i. etransitivity. *)
(*       + eapply (@meet_lowerbound nat (next_n P) (S a)). *)
(*       + erewrite next_n_next. reflexivity. *)
(*   Qed. *)

(*   Lemma next_omega_future P (CLOSED: closed P): future (next_omega P) = future P. *)
(*   Proof. *)
(*     eapply le_Antisymmetric. *)
(*     - unfold next_omega. erewrite future_meet. etransitivity. *)
(*       + eapply meet_lowerbound. *)
(*       + instantiate (1:=0). ss. *)
(*     - unfold next_omega. erewrite <- meet_future. *)
(*       + eapply meet_infimum. i. rewrite next_n_future. reflexivity. *)
(*       + i. eapply next_n_closed; eauto. *)
(*   Qed. *)

(*   Lemma next_omega_meet A k *)
(*     : *)
(*       le (next_omega (meet k)) (meet (fun a: A => next_omega (k a))). *)
(*   Proof. *)
(*     eapply meet_infimum. i. eapply meet_infimum. i. etransitivity. *)
(*     - eapply meet_lowerbound. *)
(*     - etransitivity. *)
(*       + eapply next_n_meet. *)
(*       +  ss. *)
(*   Qed. *)

(*   Lemma join_next_omega A k *)
(*     : *)
(*       le (join (fun a: A => next_omega (k a))) (next_omega (join k)). *)
(*   Proof. *)
(*     destruct (classic (inhabited A)). *)
(*     - unfold next_omega. ii. erewrite <- join_next_n; eauto. *)
(*       unfold join in *. des. exists a0. eauto. *)
(*     - ii. destruct IN. exfalso. eauto. *)
(*   Qed. *)

(*   Lemma next_omega_join A k *)
(*     : *)
(*       join (fun a: A => next_omega (k a)) = next_omega (join k). *)
(*   Proof. *)
(*     unfold next_omega. eapply le_Antisymmetric. *)
(*     - eapply join_next_omega; auto. *)
(*     - destruct (classic (inhabited A)). *)
(*       2: { ii. specialize (IN 0). ss. destruct IN. exfalso. eapply H; eauto. } *)
(*       ii. *)

(*       replace (next_n (join k)) with (fun n => join (fun a => next_n (k a) n)) in IN. *)
(*       2: { extensionality n. erewrite join_next_n; eauto. } *)
(*       eapply join_mon. *)
(*       + *)


(*         next_n_meet *)
(*         eapply next_omega_meet. *)

(*       erewrite join_meet. ii. erewrite <- join_next_n. *)

(* join_next_n *)
(*      : forall (A : Type) (k : A -> t) (n : nat), *)
(*        inhabited A -> join (fun a : A => next_n (k a) n) = next_n (join k) n *)


(*       destruct H. *)
(*       unfold join. eapply NNPP. ii. *)

(*       specialize ( *)

(*       exp *)

(*       auto. *)


(*       { admit. } *)
(*       { exten *)



(*       eapply meet_mon in IN. *)
(*       2: { instantiate (1:=fun n => next_n (join k) n). i. ss. } *)
(*       setoid_rewrite <- join_next_n in IN. *)

(*       r *)

(*             join_next_n *)
(*      : forall (A : Type) (k : A -> t) (n : nat), *)
(*        inhabited A -> join (fun a : A => next_n (k a) n) = next_n (join k) n *)


(*       un *)

(*       erewrite join_meet in IN. specialie ( *)

(*       ). *)


(*       erewrite join_meet. *)



(*     erewrite <- (join_next_n k). *)

(*     unfold meet. *)

(*   Lemma meet_next_n A k n *)
(*         (INHABITED: inhabited A) *)
(*         (CLOSED: forall a, closed (k a)) *)
(*     : *)
(*       le (next_n (meet k) n) (meet (fun a: A => next_n (k a) n)). *)
(*   Proof. *)
(*     induction n; ss. etransitivity. *)
(*     - eapply next_mon; eauto. *)
(*     - eapply meet_next; eauto. *)
(*   Qed. *)


(*     f_equal. *)

(*     induction n; ss. *)
(*     erewrite join_next; eauto. *)
(*     erewrite IHn. auto. *)
(*   Qed. *)

(* next_omega next *)

(*   L *)
