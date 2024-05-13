Require Import common.IOA.
Require Import common.LTL.
Require Import common.tactic.
Require Import common.buffer.
Require Import reliable_broadcast.definitions.
Require Import Lia.
Require Import Bool.
Require Import Arith.
Require Import ssreflect.

(* ----------------------------------------
  Some definitions (might move to other files)
 ---------------------------------------- *)

Definition process_zero : Process.
  create_sig Process 0 out.
  have : count > 0 by apply Hcount. lia.
  apply out.
Defined.

(* ----------------------------------------
  Local properties
 ---------------------------------------- *)

(* -------------------- Step properties -------------------- *)

Lemma transition_step_increase :
  forall f : nat, forall proc : Process, forall st st' : BrachaRBState, forall act : BrachaRBAction,
    Transition (BrachaRBProcess f proc) st act st' -> BrachaRBStep st <= BrachaRBStep st'.
Proof.
  intros.
  induction act ;
    unfold
      Transition,
      BrachaRBProcess,
      BrachaRBTransition,
      BrachaRB_compute_transition in H ; simpl in H ; simpl_match ; (inversion H ; fail) || auto ;
    simpl_match || idtac ; repeat simpl_arith_bool ; (inversion H ; auto ; fail) || auto.
  - inversion H. rewrite H1. simpl. auto.
  - inversion H. rewrite H2. simpl. auto.
  - induction i ; repeat simpl_match ; repeat simpl_arith_bool ; inversion H ; simpl ;
      match goal with
        | [H : BrachaRBStep st = _ |- _] => rewrite H
        | _ => auto
      end ; auto.
  - repeat simpl_match ; repeat simpl_arith_bool ; inversion H ; subst st' ; simpl ; lia.
  - repeat simpl_match ; repeat simpl_arith_bool ; inversion H ; subst st' ; simpl ; lia.
Qed.

Lemma transition_step_increase_by_one :
  forall f : nat, forall proc : Process, forall st st' : BrachaRBState, forall act : BrachaRBAction,
    Transition (BrachaRBProcess f proc) st act st' -> BrachaRBStep st' <= BrachaRBStep st + 1.
Proof.
  intros.
  induction act ;
    unfold
      Transition,
      BrachaRBProcess,
      BrachaRBTransition,
      BrachaRB_compute_transition in H ; simpl in H ; simpl_match ; (inversion H ; fail) || auto ;
    simpl_match || idtac ; repeat simpl_arith_bool ; (inversion H ; auto ; fail) || auto.
  - inversion H. rewrite H1. simpl. auto.
  - inversion H. lia.
  - inversion H. rewrite H2. simpl. auto.
  - induction i ; repeat simpl_match ; repeat simpl_arith_bool ; inversion H ; simpl ;
      match goal with
        | [H : BrachaRBStep st = _ |- _] => rewrite H
        | _ => auto
      end ; auto ; lia.
  - repeat simpl_match ; repeat simpl_arith_bool ; inversion H ; subst st' ; simpl ; lia.
  - repeat simpl_match ; repeat simpl_arith_bool ; inversion H ; subst st' ; simpl ; lia.
  - inversion H. simpl. lia.
Qed.

(* -------------------- Send buffer properties -------------------- *)

Theorem transition_only_send_remove_from_send_buffer :
  forall f : nat, forall proc : Process, forall st st' : BrachaRBState, forall act : BrachaRBAction, forall pack : Packet,
    Transition (BrachaRBProcess f proc) st act st' -> (forall m : Message, act <> BrachaRBBroadcast m) ->
    BrachaRBSendBuffer st pack = true ->
    BrachaRBSendBuffer st' pack = true <-> act <> BrachaRBP2PSend proc (fst pack) (snd pack).
Proof.
  intros f p st st' act pack H Hnot_broadcast H0.
  split. intro.
  + induction act ; discriminate || auto.
    destruct pack. simpl in *.
    unfold Transition, BrachaRBProcess, BrachaRBTransition, BrachaRB_compute_transition in H.
    simpl_match ; repeat simpl_arith_bool.
    - apply process_proof_irrelevence in H2. subst p0.
      inversion H. subst st'. simpl in *. clear H.
      intro. inversion H. subst. buffer_solver.
    - intro. inversion H3. subst p0. contradiction.
    - intro. inversion H3. subst i0 p1. rewrite H0 in H2. inversion H2.
  + intro.
    unfold Transition, BrachaRBProcess, BrachaRBTransition, BrachaRB_compute_transition in H.
    induction act.
    - specialize Hnot_broadcast with m. contradiction.
    - simpl_match ; repeat simpl_arith_bool ; inversion H.
      simpl. auto.
    - destruct pack ; simpl in *. repeat simpl_match ; repeat simpl_arith_bool ;
      inversion H ; simpl ; repeat simpl_arith_bool ; auto.
    - simpl_match ; repeat simpl_arith_bool ; inversion H.
      subst st'. simpl in *. apply process_proof_irrelevence in H2. subst p.
      destruct_BrachaRBAction_eq in H1.
      destruct pack. unfold buffer_sub.
      simpl_match. inversion n0. subst. simpl in H1.
      decompose [or] H1 ; contradiction. auto.
Qed.

Theorem transition_send_not_enabled_is_not_in_buffer :
  forall f : nat, forall proc : Process, forall st : BrachaRBState, forall pack : Packet,
    (forall st' : BrachaRBState, ~Transition
                              (BrachaRBProcess f proc)
                              st
                              (BrachaRBP2PSend proc (fst pack) (snd pack))
                              st') -> BrachaRBSendBuffer st pack = false.
Proof.
  intros.
  unfold Transition, BrachaRBProcess, BrachaRBTransition, BrachaRB_compute_transition in H.
  simpl_match ; repeat simpl_arith_bool.
  specialize H with ({|
          BrachaRBStep := BrachaRBStep st;
          BrachaRBRecvBuffer := BrachaRBRecvBuffer st;
          BrachaRBRecvBufferSize := BrachaRBRecvBufferSize st;
          BrachaRBSendBuffer := buffer_sub packet_dec (BrachaRBSendBuffer st) (fst pack, snd pack)
        |}). contradiction.
  contradiction.
  destruct pack. simpl in H0. auto.
Qed.

Theorem transition_send_only_if_in_send_buffer :
   forall f : nat, forall proc : Process, forall st st' : BrachaRBState, forall (p : Process) (m : InternMessage),
     Transition (BrachaRBProcess f proc) st (BrachaRBP2PSend proc p m) st' ->
     BrachaRBSendBuffer st (p, m) = true.
Proof.
  intros.
  hnf in H. unfold BrachaRB_compute_transition in H.
  simpl_match ; inversion H.
  subst st'. clear H. repeat simpl_arith_bool.
  auto.
Qed.

(* -------------------- Recv buffer properties -------------------- *)

Lemma transition_recv_buffer_size_increase :
  forall f : nat, forall proc : Process, forall st st' : BrachaRBState, forall act : BrachaRBAction, forall m : InternMessage,
    Transition (BrachaRBProcess f proc) st act st' ->
    BrachaRBRecvBufferSize st m <= BrachaRBRecvBufferSize st' m.
Proof.
  intros.
  unfold Transition, BrachaRBProcess, BrachaRBTransition, BrachaRB_compute_transition in H.
  induction act ; repeat simpl_match ; inversion H ; subst st' ; simpl ; auto ;
    repeat simpl_match ; repeat simpl_arith_bool ; lia.
Qed.

Lemma transition_recv_buffer_increase :
  forall f : nat, forall proc : Process, forall st st' : BrachaRBState, forall act : BrachaRBAction, forall packet : Packet,
    Transition (BrachaRBProcess f proc) st act st' ->
    BrachaRBRecvBuffer st packet = true -> BrachaRBRecvBuffer st' packet = true.
Proof.
  intros.
  unfold Transition, BrachaRBProcess, BrachaRBTransition, BrachaRB_compute_transition in H.
  induction act ; repeat simpl_match ; inversion H ; repeat simpl_arith_bool ; subst ; simpl ; destruct packet ; auto ; buffer_solver.
Qed.

(* -------------------- Conditions properties -------------------- *)

Lemma transition_echo_cond_extend_future :
  forall f : nat, forall proc : Process, forall st st' : BrachaRBState, forall act : BrachaRBAction, forall m : Message,
    Transition (BrachaRBProcess f proc) st act st' ->
    ( BrachaRBStep st >= 2 /\
        (BrachaRBRecvBuffer st (process_zero, Init m) = true \/
           BrachaRBRecvBufferSize st (Echo m) >= f + (f + 0) + 1 \/
           BrachaRBRecvBufferSize st (Ready m) >= f + 1)) ->
    ( BrachaRBStep st' >= 2 /\
        (BrachaRBRecvBuffer st' (process_zero, Init m) = true \/
           BrachaRBRecvBufferSize st' (Echo m) >= f + (f + 0) + 1 \/
           BrachaRBRecvBufferSize st' (Ready m) >= f + 1)).
Proof.
  intros.
  assert (BrachaRBStep st <= BrachaRBStep st').
  apply transition_step_increase with f proc act. auto.
  destruct H0. split. lia.
  destruct H2.
  left. apply transition_recv_buffer_increase with f proc st act ; auto.
  right. destruct H2.
  left. assert (BrachaRBRecvBufferSize st (Echo m) <= BrachaRBRecvBufferSize st' (Echo m)). apply transition_recv_buffer_size_increase with f proc act ; auto. lia.
  right. assert (BrachaRBRecvBufferSize st (Ready m) <= BrachaRBRecvBufferSize st' (Ready m)). apply transition_recv_buffer_size_increase with f proc act ; auto. lia.
Qed.

Lemma transition_ready_cond_extend_future :
  forall f : nat, forall proc : Process, forall st st' : BrachaRBState, forall act : BrachaRBAction, forall m : Message,
    Transition (BrachaRBProcess f proc) st act st' ->
    (BrachaRBStep st >= 3 /\ (
                             BrachaRBRecvBufferSize st (Echo m) >= 2*f+1 \/
                               BrachaRBRecvBufferSize st (Ready m) >= f+1
                          )) ->
    (BrachaRBStep st' >= 3 /\ (
                             BrachaRBRecvBufferSize st' (Echo m) >= 2*f+1 \/
                               BrachaRBRecvBufferSize st' (Ready m) >= f+1
                          )).
Proof.
  intros.
  assert (BrachaRBStep st <= BrachaRBStep st').
  apply transition_step_increase with f proc act. auto.
  destruct H0. split. lia.
  destruct H2.
  left. assert (BrachaRBRecvBufferSize st (Echo m) <= BrachaRBRecvBufferSize st' (Echo m)). apply transition_recv_buffer_size_increase with f proc act ; auto. lia.
  right. assert (BrachaRBRecvBufferSize st (Ready m) <= BrachaRBRecvBufferSize st' (Ready m)). apply transition_recv_buffer_size_increase with f proc act ; auto. lia.
Qed.

(* ----------------------------------------
  Safety properties (derived from local)
 ---------------------------------------- *)

(* -------------------- Step properties -------------------- *)

Open Scope ltl_scope.

Theorem step_increase :
  forall f : nat, forall proc : Process,
  forall e : ExecFragmentType (A := BrachaRBProcess f proc),
    Exec e ->
    e $ 0 |= G (N (fun s => BrachaRBStep (st BrachaRBAction (BrachaRBProcess f proc) s) <=
                           BrachaRBStep (st' BrachaRBAction (BrachaRBProcess f proc) s))).
Proof.
  intros.
  unfold ltl_general, ltl_apply, ltl_now.
  intros. destruct (e j). simpl.
  case_eq opt_act ; intros ; rewrite H1 in is_well_formed.
  apply transition_step_increase with f proc a. auto.
  subst st. auto.
Qed.

Theorem step_increase_by_one :
  forall f : nat, forall proc : Process,
  forall e : ExecFragmentType (A := BrachaRBProcess f proc),
    Exec e ->
    e $ 0 |= G (N (fun s => BrachaRBStep (st' BrachaRBAction (BrachaRBProcess f proc) s) <=
                           BrachaRBStep (st BrachaRBAction (BrachaRBProcess f proc) s) + 1)).
Proof.
  intros.
  unfold ltl_general, ltl_apply, ltl_now.
  intros. destruct (e j). simpl.
  case_eq opt_act ; intros ; rewrite H1 in is_well_formed.
  apply transition_step_increase_by_one with f proc a. auto.
  subst st. lia.
Qed.

(* -------------------- Recv buffer properties -------------------- *)
Close Scope ltl_scope.

(*)

Inductive buffer_size (buff : Packet -> bool) (m : InternMessage) (size : nat) : Prop :=
  | buff_empty : size = 0 -> (forall proc : Process, buff (proc, m) = false) -> buffer_size buff m size
  | exist_packet : size > 0 -> (exists proc : Process, buff (proc, m) = true /\ buffer_size (BrachaRBBuffer_sub buff proc m) m (size - 1)) ->
                   buffer_size buff m size
.

Require Import FunctionalExtensionality.

Lemma buffer_size_add :
  forall i : nat, forall buff : Packet -> bool, forall m m' : InternMessage, forall p : Process,
    buffer_size buff m i -> m <> m' -> buffer_size (BrachaRBBuffer_add buff p m') m i.
Proof.
  induction i.
  - (* i = 0 *)
    intros. destruct H.
    apply buff_empty ; auto. intro. specialize H1 with proc.
    buffer_solver.
    lia.
  - (* induction *)
    intros. destruct H. lia.
    destruct H1.
    apply exist_packet. auto. exists x. simpl in *.
    have Heq : i - 0 = i by lia. rewrite Heq.
    assert (BrachaRBBuffer_sub (BrachaRBBuffer_add buff p m') x m = BrachaRBBuffer_add (BrachaRBBuffer_sub buff x m) p m').
    extensionality packet. destruct packet.
    unfold BrachaRBBuffer_add, BrachaRBBuffer_sub, InternMessage_dec_bool. repeat simpl_match ; auto.
    simpl in *. subst i0. contradiction.
    rewrite H2. split. destruct H1. buffer_solver. apply IHi ; auto. rewrite Heq in H1. apply H1.
Qed.

Lemma adding_to_buffer_if_in_it_dont_change_size :
  forall i : nat, forall buff : Packet -> bool, forall m m' : InternMessage, forall p : Process,
    buffer_size buff m i -> buff (p, m') = true ->
        buffer_size (BrachaRBBuffer_add buff p m') m i.
Proof.
  induction i.
   - (* i = 0 *)
    intros. destruct H.
    case_eq (InternMessage_dec m m') ; intros. subst m'.
    specialize H1 with p. rewrite H1 in H0. inversion H0.
    apply buff_empty ; auto. buffer_solver.
    lia.
  - (* induction *)
    intros. destruct H. lia.
    destruct H1.
    apply exist_packet. auto. exists x. simpl in *.
    have Heq : i - 0 = i by lia. rewrite Heq in H1. rewrite Heq. clear Heq.
    assert (BrachaRBBuffer_sub (BrachaRBBuffer_add buff p m') x m = BrachaRBBuffer_sub buff x m).
    buffer_solver.
    rewrite H2. split. buffer_solver. apply H1.
Qed.

Lemma adding_to_buffer_if_not_in_it_change_size :
  forall i : nat, forall buff : Packet -> bool, forall m m' : InternMessage, forall p : Process,
    buffer_size buff m i -> buff (p, m') = false ->
        buffer_size (BrachaRBBuffer_add buff p m') m (if InternMessage_dec_bool m m' then i + 1 else i).
Proof.
  induction i.
   - (* i = 0 *)
    intros. unfold InternMessage_dec_bool. destruct H.
    case_eq (InternMessage_dec m m') ; intros. subst m'.
    apply exist_packet. auto.
    exists p. split. buffer_solver. apply buff_empty. lia.
    intro. specialize H1 with proc.
    buffer_solver.
    apply buffer_size_add ; auto. apply buff_empty ; auto.
    lia.
  - (* induction *)
    intros. unfold InternMessage_dec_bool. destruct H. lia.
    destruct H1.
    apply exist_packet. repeat simpl_match ; lia. exists x. simpl in *.
    have Heq : i - 0 = i by lia. rewrite Heq in H1.
    case_eq (InternMessage_dec m m') ; intros. subst m'.
    split. buffer_solver. apply exist_packet. lia. exists p.
    assert (BrachaRBBuffer_sub (BrachaRBBuffer_sub (BrachaRBBuffer_add buff p m) x m) p m = BrachaRBBuffer_sub buff x m).
    extensionality packet. destruct packet.
    unfold BrachaRBBuffer_add, BrachaRBBuffer_sub, InternMessage_dec_bool.
    repeat simpl_match ; simpl in * ; contradiction || auto ; repeat simpl_arith_bool ; apply process_proof_irrelevence in H3 || inversion H3.
    simpl in *. subst i0 s. auto.
    rewrite H3. have Htmp : S (i + 1) - 1 - 1 = i by lia. rewrite Htmp. clear Htmp.
    assert (BrachaRBBuffer_sub (BrachaRBBuffer_add buff p m) x m = BrachaRBBuffer_add (BrachaRBBuffer_sub buff x m) p m).
    extensionality packet. destruct packet.
    unfold BrachaRBBuffer_add, BrachaRBBuffer_sub, InternMessage_dec_bool.
    repeat simpl_match ; simpl in * ; contradiction || auto ; repeat simpl_arith_bool ;
      apply process_proof_irrelevence in H4 || inversion H3.
    simpl in *. subst i0 s. apply process_proof_irrelevence in H5. subst x. destruct H1. rewrite H1 in H0.
    inversion H0. split. rewrite H4. buffer_solver. apply H1.
    have Htmp : S i - 1 = i by lia. rewrite Htmp. split. buffer_solver.
    specialize IHi with (BrachaRBBuffer_sub buff x m) m m' p.
    assert (BrachaRBBuffer_sub (BrachaRBBuffer_add buff p m') x m = BrachaRBBuffer_add (BrachaRBBuffer_sub buff x m) p m').
    extensionality packet. destruct packet.
    unfold BrachaRBBuffer_add, BrachaRBBuffer_sub, InternMessage_dec_bool.
    repeat simpl_match ; simpl in * ; contradiction || auto ; repeat simpl_arith_bool ;
      apply process_proof_irrelevence in H4 || inversion H3.
    simpl in *. subst i0 s. auto.
    subst i0 s. auto.
    rewrite H3. unfold InternMessage_dec_bool in IHi. rewrite H2 in IHi. apply IHi.
    apply H1. buffer_solver.
Qed.

Theorem size_of_buffer_then_exists_set_of_proc :
  forall i : nat, forall buff : Packet -> bool, forall m : InternMessage, forall p : Process,
    buffer_size buff m i ->
    exists sset : nat -> Process,
      (forall n : nat, n < i -> buff (sset n, m) = true) /\
      forall n m : nat, n < m < i -> sset n <> sset m.
Proof.
  induction i ; intros.
  - (* i = 0 *)
    exists (fun n => process_zero).
    split ; lia.
  - (* induction *)
    destruct H. lia.
    destruct H0. have tmp : S i - 1 = i by lia. rewrite tmp in H0. clear tmp.
    edestruct IHi.
    apply p. apply H0.
    exists (fun n => if n =? i then x else (x0 n)). split.
    {
      intros. simpl_match ; simpl_arith_bool.
      apply H0. destruct H1.
      specialize H1 with n. have : n < i by lia. intro. apply H1 in H5.
      unfold BrachaRBBuffer_sub in H5. simpl_match. inversion H5. apply H5.
    }
    intros. repeat simpl_match ; repeat simpl_arith_bool ; subst. lia.
    destruct H1. specialize H1 with m0. have tmp : m0 < i by lia. apply H1 in tmp.
    intro. destruct H5. buffer_solver.
    destruct H1. specialize H1 with n. have tmp : n < i by lia. apply H1 in tmp.
    intro. rewrite H5 in tmp. buffer_solver.
    apply H1. lia.
Qed.*)

Open Scope ltl_scope.

Require Import FunctionalExtensionality.

Lemma adding_to_buffer_if_not_in_it_change_size :
  forall i : nat, forall buff : buffer Packet, forall m m' : InternMessage, forall p : Process,
    buffer_size Process_dec (fun q => buff (q, m)) i -> buff (p, m') = false ->
        buffer_size Process_dec (fun q => buffer_add packet_dec buff (p, m') (q, m)) (if InternMessage_dec_bool m m' then i + 1 else i).
Proof.
  intros.
  unfold InternMessage_dec_bool.
  destruct InternMessage_dec with m m'. subst.
  assert ( (fun q : Process => buffer_add packet_dec buff (p, m') (q, m')) = buffer_add Process_dec (fun q => buff (q, m')) p).
  apply functional_extensionality. intro x.
  unfold buffer_add. repeat simpl_match ; auto.
  inversion n0. contradiction.
  subst. contradiction.
  rewrite H1. have tmp : i+1 = S i by lia. rewrite tmp. clear tmp.
  apply buffer_some. auto. auto.
  assert ((fun q : Process => buffer_add packet_dec buff (p, m') (q, m)) = (fun q : Process => buff (q, m))).
  apply functional_extensionality. intro x.
  erewrite buffer_add_keep_other_unchaged ; auto. intro. apply n. inversion H1. auto.
  rewrite H1. auto.
Qed.

Theorem recv_buffer_size_is_size_of_recv_buffer :
  forall f : nat, forall proc : Process, forall m : InternMessage,
  forall e : ExecFragmentType (A := BrachaRBProcess f proc),
    Exec e ->
    e $ 0 |= G (N (fun s => let (st, act, st', _) := s in
                         buffer_size Process_dec (fun p => BrachaRBRecvBuffer st (p, m)) (BrachaRBRecvBufferSize st m))).
Proof.
  intros.
  destruct H as [H Hstart].
  unfold ltl_general, ltl_apply, ltl_now.
  induction j.
  - (* j = 0 *)
    intro. destruct (e 0). simpl in *.
    unfold BrachaRBStart in Hstart. subst st. simpl.
    apply buffer_empty.
  - (* induction *)
    intro.
    unfold ExecFragment in H. specialize H with j.
    have Htmp : S j = j + 1 by lia. rewrite Htmp. clear Htmp.
    destruct (e (j+1)).
    simpl in H. subst st. clear is_well_formed st' opt_act.
    destruct (e j).
    simpl in *. assert (j >= 0). lia. apply IHj in H. clear IHj.
    case_eq opt_act ; intros ; rewrite H1 in is_well_formed ; clear H1 ; cycle 1.
    subst st ; auto.
    induction a ; unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed.
    + repeat simpl_match ; inversion is_well_formed ; subst st' ; simpl ; auto.
    + repeat simpl_match ; inversion is_well_formed ; subst st' ; simpl ; auto.
    + induction i ;
        repeat simpl_match ; inversion is_well_formed ; subst st' ; simpl ; auto ;
        try (rewrite buffer_add_in_buffer_invariant ; auto ; fail) ; apply adding_to_buffer_if_not_in_it_change_size ; auto.
    + repeat simpl_match ; inversion is_well_formed ; subst st' ; simpl ; auto.
Qed.

(* ----------------------------------------
  Past properties
 ---------------------------------------- *)

Close Scope ltl_scope.

Theorem in_recv_buffer_then_have_recv :
  forall f : nat, forall proc : Process, forall m : InternMessage, forall p : Process,
    past_property_st_act
      (BrachaRBProcess f proc)
      (fun st => BrachaRBRecvBuffer st (p, m) = true)
      (fun act => act = BrachaRBP2PRecv proc p m)
.
Proof.
  unfold past_property_st_act.
  intros.
  assert (
      forall j : nat,
        (exists k : nat, k >= i - j /\ k < i /\
                    (opt_act BrachaRBAction (BrachaRBProcess f proc) (e k)) = Some (BrachaRBP2PRecv proc p m)) \/
          (BrachaRBRecvBuffer (st BrachaRBAction (BrachaRBProcess f proc) (e (i - j))) (p, m) = true)
    ).
  induction j.
  - (* case i *)
    right. have Heq : i - 0 = i by lia. rewrite Heq. auto.
  - (* induction *)
    destruct H as [H Hstart]. unfold ExecFragment in H. specialize H with (i - S j).
    destruct IHj. left. destruct H1. exists x. intuition. lia.
    case_eq (i - j =? 0) ; intro Heq ; simpl_arith_bool.
    unfold Start, BrachaRBProcess, BrachaRBStart in Hstart.
    rewrite Heq in H1. destruct (e 0). simpl in *. rewrite Hstart in H1. simpl in H1.
    unfold empty_buffer in H1. inversion H1.
    case_eq (opt_act BrachaRBAction (BrachaRBProcess f proc) (e (i - S j))) ; [intros act Hopt | intro Hopt].
    case_eq act ; intros.
    + (* broadcast *)
      right.
      destruct (e (i - S j)). simpl in *.
      rewrite H in is_well_formed. rewrite Hopt H2 in is_well_formed.
      assert (Htmp : i - S j + 1 = i - j). lia. rewrite Htmp in is_well_formed ; clear Htmp.
      case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
        unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed ;
        simpl in is_well_formed ;
        simpl_match ; simpl_match || idtac ; repeat simpl_arith_bool ;
        inversion is_well_formed ; auto ; rewrite <-H7 in H1 ; auto.
    + (* deliver *)
      right.
      destruct (e (i - S j)). simpl in *.
      rewrite H in is_well_formed. rewrite Hopt H2 in is_well_formed.
      assert (Htmp : i - S j + 1 = i - j). lia. rewrite Htmp in is_well_formed ; clear Htmp.
      case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
        unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed ;
        simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ; auto ; rewrite <-H8 in H1 ; auto.
    + (* Recv, i.e. or the interesting part *)
      (* I really think it is possible to automate all of this, even at process level by usig a bunch of strategies, I have to sleep on this one *)
      case_eq (proj1_sig p0 =? proj1_sig proc) ; intro ; cycle 1.
      destruct (e (i - S j)). simpl in *. rewrite Hopt H2 in is_well_formed.
      unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed.
      repeat simpl_match ;
        match goal with
          | [H : true = false |- _] => inversion H
          | _ => auto
        end
      ; inversion is_well_formed.
      simpl_arith_bool. apply process_proof_irrelevence in H3.
      case_eq (InternMessage_dec m i0) ; case_eq (proj1_sig p =? proj1_sig p1) ; intros ; simpl_arith_bool.
      * left. exists (i - S j). intuition. lia. rewrite Hopt H2. apply process_proof_irrelevence in H4.
        subst proc p m. auto.
      * right.
        destruct (e (i - S j)). simpl in *. rewrite Hopt H2 in is_well_formed.
        unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed.
        have Htmp : i - S j + 1 = i - j by lia. rewrite Htmp in H. clear Htmp.
        rewrite <-H in H1.
        rewrite H3 in is_well_formed. simpl in is_well_formed.
        induction i0 ;
        repeat simpl_match ; repeat simpl_arith_bool ; auto ; inversion is_well_formed as [Hinv] ; rewrite <-Hinv in H1 ;
          simpl in H1
        ; unfold buffer_add, buffer_sub in H1 ; simpl_match ; repeat simpl_arith_bool ;
          simpl in * ; try inversion n0 ; subst ; contradiction || (unfold InternMessage_dec_bool in * ; simpl_match ; auto) || auto.
      * right.
        destruct (e (i - S j)). simpl in *. rewrite Hopt H2 in is_well_formed.
        unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed.
        have Htmp : i - S j + 1 = i - j by lia. rewrite Htmp in H. clear Htmp.
        rewrite <-H in H1.
        rewrite H3 in is_well_formed. simpl in is_well_formed.
        repeat simpl_match ; repeat simpl_arith_bool ; auto ; inversion is_well_formed as [Hinv] ; rewrite <-Hinv in H1 ;
          simpl in H1 ; unfold buffer_add, buffer_sub in H1 ; simpl_match ; repeat simpl_arith_bool ;
          simpl in * ; try inversion n2 ; contradiction || (unfold InternMessage_dec_bool in * ; simpl_match ; auto) || auto ; subst i0 ;
          match goal with
            | [H : false = true |- _] => inversion H
            | _ => auto
          end.
      * right.
        destruct (e (i - S j)). simpl in *. rewrite Hopt H2 in is_well_formed.
        unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed.
        have Htmp : i - S j + 1 = i - j by lia. rewrite Htmp in H. clear Htmp.
        rewrite <-H in H1.
        rewrite H3 in is_well_formed. simpl in is_well_formed.
        repeat simpl_match ; repeat simpl_arith_bool ; auto ; inversion is_well_formed as [Hinv] ; rewrite <-Hinv in H1 ;
          simpl in H1 ; unfold buffer_add, buffer_sub in H1 ; simpl_match ; repeat simpl_arith_bool ;
          simpl in * ; try inversion n2 ; contradiction || (unfold InternMessage_dec_bool in * ; simpl_match ; auto) || auto ; subst i0 ;
          match goal with
            | [H : false = true |- _] => inversion H
            | _ => auto
          end.
    + (* Send, not as fun as recv but yah know *)
      right.
      destruct (e (i - S j)). simpl in *.
      rewrite H in is_well_formed. rewrite Hopt H2 in is_well_formed.
      assert (Htmp : i - S j + 1 = i - j). lia. rewrite Htmp in is_well_formed ; clear Htmp.
      case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
        unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed ;
        simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ; auto ; rewrite <-H7 in H1 ; auto.
    + (* None *)
      right.
      destruct (e (i - S j)). simpl in *.
      rewrite H in is_well_formed. rewrite Hopt in is_well_formed.
      subst st. assert (i - S j + 1 = i - j) by lia. rewrite H2. auto.
  - specialize H1 with i. destruct H1.
    + destruct H1. exists x. exists (BrachaRBP2PRecv proc p m). intuition.
    + have Htmp : i-i = 0 by lia. rewrite Htmp in H1. clear Htmp.
      destruct H as [H Hstart]. unfold Start, BrachaRBProcess, BrachaRBStart in Hstart, H1.
      rewrite Hstart in H1. simpl in H1. unfold empty_buffer in H1. inversion H1.
Qed.

(*)
Theorem in_recv_buffer_then_have_recv :
  forall f : nat, forall proc : Process,
  forall e : ExecFragmentType (A := BrachaRBProcess f proc),
      Exec e ->
      forall i : nat, forall m : InternMessage, forall p : Process,
        BrachaRBRecvBuffer (st BrachaRBAction (BrachaRBProcess f proc) (e i)) (p, m) = true ->
        exists j : nat,
          j < i /\
            (act BrachaRBAction (BrachaRBProcess f proc) (e j)) = (BrachaRBP2PRecv proc p m).
Proof.
  intros.
  assert (
      forall j : nat,
        (exists k : nat, k >= i - j /\ k < i /\
                    (act BrachaRBAction (BrachaRBProcess f proc) (e k)) = (BrachaRBP2PRecv proc p m)) \/
          (BrachaRBRecvBuffer (st BrachaRBAction (BrachaRBProcess f proc) (e (i - j))) (p, m) = true)
    ).
  induction j.
  + (* case i *)
    right. have Heq : i - 0 = i by lia. rewrite Heq. auto.
  + (* induction *)
    destruct H as [H Hstart]. unfold ExecFragment in H. specialize H with (i - S j).
    destruct IHj. left. destruct H1. exists x. intuition. lia.
    case_eq (i - j =? 0) ; intro Heq ; simpl_arith_bool.
    unfold Start, BrachaRBProcess, BrachaRBStart in Hstart.
    rewrite Heq in H1. destruct (e 0). simpl in *. rewrite Hstart in H1. simpl in H1.
    unfold BrachaRBBuffer_empty_set in H1. inversion H1.
    case_eq (act BrachaRBAction (BrachaRBProcess f proc) (e (i - S j))) ; intros.
    - (* broadcast *)
      right.
      destruct (e (i - S j)). simpl in *.
      rewrite H in is_well_formed. rewrite H2 in is_well_formed.
      assert (Htmp : i - S j + 1 = i - j). lia. rewrite Htmp in is_well_formed ; clear Htmp.
      case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
        unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed ;
        simpl in is_well_formed ;
        simpl_match ; simpl_match || idtac ; repeat simpl_arith_bool ;
        inversion is_well_formed ; auto ; rewrite <-H7 in H1 ; auto.
    - (* deliver *)
      right.
      destruct (e (i - S j)). simpl in *.
      rewrite H in is_well_formed. rewrite H2 in is_well_formed.
      assert (Htmp : i - S j + 1 = i - j). lia. rewrite Htmp in is_well_formed ; clear Htmp.
      case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
        unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed ;
        simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ; auto ; rewrite <-H8 in H1 ; auto.
    - (* Recv, i.e. or the interesting part *)
      (* I really think it is possible to automate all of this, even at process level by usig a bunch of strategies, I have to sleep on this one *)
      case_eq (proj1_sig p0 =? proj1_sig proc) ; intro ; cycle 1.
      destruct (e (i - S j)). simpl in *. rewrite H2 in is_well_formed.
      unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed.
      repeat simpl_match ;
        match goal with
          | [H : true = false |- _] => inversion H
          | _ => auto
        end
      ; inversion is_well_formed.
      simpl_arith_bool. apply process_proof_irrelevence in H3.
      case_eq (InternMessage_dec m i0) ; case_eq (proj1_sig p =? proj1_sig p1) ; intros ; simpl_arith_bool.
      * left. exists (i - S j). intuition. lia. rewrite H2. apply process_proof_irrelevence in H4.
        subst proc p m. auto.
      * right.
        destruct (e (i - S j)). simpl in *. rewrite H2 in is_well_formed.
        unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed.
        have Htmp : i - S j + 1 = i - j by lia. rewrite Htmp in H. clear Htmp.
        rewrite <-H in H1.
        rewrite H3 in is_well_formed. simpl in is_well_formed.
        induction i0 ;
        repeat simpl_match ; repeat simpl_arith_bool ; auto ; inversion is_well_formed as [Hinv] ; rewrite <-Hinv in H1 ;
          simpl in H1 ; unfold BrachaRBBuffer_add, BrachaRBBuffer_sub in H1 ; simpl_match ; repeat simpl_arith_bool ;
          simpl in * ; contradiction || (unfold InternMessage_dec_bool in * ; simpl_match ; auto) || auto.
      * right.
        destruct (e (i - S j)). simpl in *. rewrite H2 in is_well_formed.
        unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed.
        have Htmp : i - S j + 1 = i - j by lia. rewrite Htmp in H. clear Htmp.
        rewrite <-H in H1.
        rewrite H3 in is_well_formed. simpl in is_well_formed.
        repeat simpl_match ; repeat simpl_arith_bool ; auto ; inversion is_well_formed as [Hinv] ; rewrite <-Hinv in H1 ;
          simpl in H1 ; unfold BrachaRBBuffer_add, BrachaRBBuffer_sub in H1 ; simpl_match ; repeat simpl_arith_bool ;
          simpl in * ; contradiction || (unfold InternMessage_dec_bool in * ; simpl_match ; auto) || auto ; subst i0 ;
          match goal with
            | [H : false = true |- _] => inversion H
            | _ => auto
          end.
      * right.
        destruct (e (i - S j)). simpl in *. rewrite H2 in is_well_formed.
        unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed.
        have Htmp : i - S j + 1 = i - j by lia. rewrite Htmp in H. clear Htmp.
        rewrite <-H in H1.
        rewrite H3 in is_well_formed. simpl in is_well_formed.
        repeat simpl_match ; repeat simpl_arith_bool ; auto ; inversion is_well_formed as [Hinv] ; rewrite <-Hinv in H1 ;
          simpl in H1 ; unfold BrachaRBBuffer_add, BrachaRBBuffer_sub in H1 ; simpl_match ; repeat simpl_arith_bool ;
          simpl in * ; contradiction || (unfold InternMessage_dec_bool in * ; simpl_match ; auto) || auto ; subst i0 ;
          match goal with
            | [H : false = true |- _] => inversion H
            | _ => auto
          end.
    - (* Send, not as fun as recv but yah know *)
      right.
      destruct (e (i - S j)). simpl in *.
      rewrite H in is_well_formed. rewrite H2 in is_well_formed.
      assert (Htmp : i - S j + 1 = i - j). lia. rewrite Htmp in is_well_formed ; clear Htmp.
      case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
        unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed ;
        simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ; auto ; rewrite <-H7 in H1 ; auto.
  + specialize H1 with i. destruct H1.
    - destruct H1. exists x. intuition.
    - have Htmp : i-i = 0 by lia. rewrite Htmp in H1. clear Htmp.
      destruct H as [H Hstart]. unfold Start, BrachaRBProcess, BrachaRBStart in Hstart, H1.
      rewrite Hstart in H1. simpl in H1. unfold BrachaRBBuffer_empty_set in H1. inversion H1.
Qed.*)

Theorem send_init_then_broadcast_before :
  forall f : nat, forall proc : Process, forall m : Message, forall p : Process,
    past_property_act_act
      (BrachaRBProcess f proc)
      (fun act => act = BrachaRBP2PSend process_zero p (Init m))
      (fun act => act = BrachaRBBroadcast m)
.
Proof.
  unfold past_property_act_act.
  intros.
  destruct H as [H Hstart].
  case_eq (proj1_sig proc) ; intros.
  {
    assert (proj1_sig proc = proj1_sig process_zero). auto.
    apply process_proof_irrelevence in H3. subst proc.
    clear H2.
    assert (
        forall j : nat,
          (exists k : nat, k >= i - j /\ k < i /\
            (opt_act BrachaRBAction (BrachaRBProcess f process_zero) (e k)) = Some (BrachaRBBroadcast m)) \/
            (BrachaRBSendBuffer
               (st BrachaRBAction (BrachaRBProcess f process_zero) (e (i - j)))
               (p, Init m) = true)
      ).
    induction j.
    - (* j = 0 *)
      assert (i - 0 = i). lia. rewrite H2. clear H2.
      destruct (e i). simpl in H0 |- *. subst opt_act act.
      apply transition_send_only_if_in_send_buffer in is_well_formed.
      right. auto.
    - (* induction *)
      destruct IHj.
      left. destruct H2. exists x. intuition. lia.
      hnf in H. specialize H with (i - S j).
      case_eq (i - j) ; intros.
      rewrite H3 in H2. assert (i - S j = 0) by lia. rewrite H4. clear H4.
      right ; auto.
      assert (i - S j + 1 = i - j) by lia. rewrite H4 in H. clear H4.
      case_eq (opt_act BrachaRBAction (BrachaRBProcess f process_zero) (e (i - S j))) ;
        [intros act' Hopt | intro Hopt].
      case_eq act' ; intros ; subst act'.
      + case_eq (Message_dec m0 m) ; intros.
        subst m0. left. exists (i - S j). intuition. lia.
        right. destruct (e (i - S j)). simpl. simpl in H, H3, Hopt.
        subst opt_act act. hnf in is_well_formed. unfold BrachaRB_compute_transition in is_well_formed.
        simpl in is_well_formed. subst st'. simpl_match ; inversion is_well_formed.
        rewrite <-H5 in H2. simpl in H2. repeat simpl_arith_bool ; auto.
        unfold InternMessage_dec_bool in H1.
        simpl_match ; inversion H1 ; inversion n2 ; subst m0 ; contradiction.
        auto.
      + right.
        destruct (e (i - S j)).
        simpl in *. subst opt_act act. subst st'.
        hnf in is_well_formed. unfold BrachaRB_compute_transition in is_well_formed.
        simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed.
        rewrite <-H6 in H2. simpl in H2. auto.
      + right.
        destruct (e (i - S j)).
        simpl in *. subst opt_act act. rewrite <-H in H2. clear H.
        hnf in is_well_formed. unfold BrachaRB_compute_transition in is_well_formed.
        induction i0 ; repeat simpl_match ; repeat simpl_arith_bool ;
          inversion is_well_formed ; subst st' ; auto ;
          simpl in H2 ; repeat simpl_arith_bool ; auto ;
          unfold InternMessage_dec_bool in H2 ; simpl_match ; inversion H2 ; inversion n1.
      + right.
        destruct (e (i - S j)).
        simpl in *. subst opt_act act. rewrite <-H in H2. clear H.
        hnf in is_well_formed. unfold BrachaRB_compute_transition in is_well_formed.
        induction i0 ; repeat simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ;
          subst st' ; auto ; simpl in H2 ; unfold buffer_sub, InternMessage_dec_bool in H2 ;
          repeat simpl_match ; repeat simpl_arith_bool ; simpl in * ;
          try (inversion n1 ; subst m) ; try (apply process_proof_irrelevence in H4 ; subst p1) ;
          auto ; inversion H2.
      + right.
        destruct (e (i - S j)).
        simpl in *. subst opt_act. subst st'. subst st. auto.
    - specialize H2 with i. destruct H2. destruct H2. exists x. exists (BrachaRBBroadcast m). intuition.
      assert (i - i = 0) by lia. subst act. rewrite H3 in H2. clear H3.
      destruct (e 0). simpl in *. hnf in Hstart. subst st. simpl in H2.
      unfold empty_buffer in H2. inversion H2.
  }
  {
    destruct (e i).
    simpl in *. subst opt_act act. hnf in is_well_formed. unfold BrachaRB_compute_transition in is_well_formed.
    simpl_match ; inversion is_well_formed ; subst st'.
    repeat simpl_arith_bool. rewrite H2 in H0. simpl in H0. lia.
  }
Qed.

(*)
Lemma send_init_then_broadcast_before :
  forall f : nat, forall proc : Process,
  forall e : ExecFragmentType (A := BrachaRBProcess f proc),
    Exec e ->
    forall i : nat, forall m : Message, forall p : Process,
      act BrachaRBAction (BrachaRBProcess f proc) (e i) = BrachaRBP2PSend process_zero p (Init m) ->
      exists j : nat, j < i /\ act BrachaRBAction (BrachaRBProcess f proc) (e j) = BrachaRBBroadcast m.
Proof.
  intros.
  destruct H as [H Hstart].
  case_eq (proj1_sig proc) ; intros.
  {
    assert (proj1_sig proc = proj1_sig process_zero). auto. apply process_proof_irrelevence in H2. subst proc.
    clear H1.
    assert (
        forall j : nat,
          (exists k : nat, k >= i - j /\ k < i /\
                      (act BrachaRBAction (BrachaRBProcess f process_zero) (e k)) = BrachaRBBroadcast m) \/
            (BrachaRBSendBuffer (st BrachaRBAction (BrachaRBProcess f process_zero) (e (i - j))) (p, Init m) = true
          )
      ).
    induction j.
    - (* j = 0 *)
      assert (i - 0 = i). lia. rewrite H1. clear H1.
      destruct (e i). simpl in H0. subst act. simpl.
      apply transition_send_only_if_in_send_buffer in is_well_formed.
      right. auto.
    - (* induction *)
      destruct IHj.
      left. destruct H1. exists x. intuition. lia.
      hnf in H. specialize H with (i - S j).
      case_eq (i - j) ; intros.
      rewrite H2 in H1. assert (i - S j = 0) by lia. rewrite H3. clear H3.
      right ; auto.
      assert (i - S j + 1 = i - j) by lia. rewrite H3 in H. clear H3.
      case_eq (act BrachaRBAction (BrachaRBProcess f process_zero) (e (i - S j))) ; intros.
      + case_eq (Message_dec m0 m) ; intros.
        subst m0. left. exists (i - S j). intuition. lia.
        right. destruct (e (i - S j)). simpl. simpl in H, H3.
        subst act. hnf in is_well_formed. unfold BrachaRB_compute_transition in is_well_formed.
        simpl in is_well_formed. subst st'. simpl_match ; inversion is_well_formed.
        rewrite <-H5 in H1. simpl in H1. repeat simpl_arith_bool ; auto.
        unfold InternMessage_dec_bool in H1. simpl_match ; inversion H1 ; inversion n2 ; subst m0 ; contradiction.
        auto.
      + right.
        destruct (e (i - S j)).
        simpl in *. subst act. subst st'.
        hnf in is_well_formed. unfold BrachaRB_compute_transition in is_well_formed.
        simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed.
        rewrite <-H6 in H1. simpl in H1. auto.
      + right.
        destruct (e (i - S j)).
        simpl in *. subst act. rewrite <-H in H1. clear H.
        hnf in is_well_formed. unfold BrachaRB_compute_transition in is_well_formed.
        induction i0 ; repeat simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ; subst st' ; auto ;
        simpl in H1 ; repeat simpl_arith_bool ; auto ; unfold InternMessage_dec_bool in H1 ; simpl_match ; inversion H1 ; inversion n1.
      + right.
        destruct (e (i - S j)).
        simpl in *. subst act. rewrite <-H in H1. clear H.
        hnf in is_well_formed. unfold BrachaRB_compute_transition in is_well_formed.
        induction i0 ; repeat simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ; subst st' ; auto ;
        simpl in H1 ; unfold BrachaRBBuffer_sub, InternMessage_dec_bool in H1 ; repeat simpl_match ; repeat simpl_arith_bool ; simpl in * ;
        try (inversion n1 ; subst m) ; try (apply process_proof_irrelevence in H4 ; subst p1) ; auto ; inversion H4.
    - specialize H1 with i. destruct H1. destruct H1. exists x. intuition.
      assert (i - i = 0) by lia. rewrite H2 in H1. clear H2.
      destruct (e 0). simpl in *. hnf in Hstart. subst st. simpl in H1. unfold BrachaRBBuffer_empty_set in H1. inversion H1.
  }
  {
    destruct (e i).
    simpl in *. subst act. hnf in is_well_formed. unfold BrachaRB_compute_transition in is_well_formed.
    simpl_match ; inversion is_well_formed ; subst st'.
    repeat simpl_arith_bool. rewrite H1 in H0. simpl in H0. lia.
  }
Qed.*)

Theorem send_echo_then_condition_satisfied :
  forall f : nat, forall proc : Process,
  forall e : ExecFragmentType (A := BrachaRBProcess f proc),
    Exec e ->
    forall i : nat, forall m : Message, forall p : Process,
      let (st, act, st', _) := (e i) in
      BrachaRBSendBuffer st (p, Echo m) = true ->
      BrachaRBStep st >= 2 /\ (
                              BrachaRBRecvBuffer st (process_zero, Init m) = true \/
                                BrachaRBRecvBufferSize st (Echo m) >= 2*f+1 \/
                                BrachaRBRecvBufferSize st (Ready m) >= f+1
                            ).
Proof.
  intros.
  destruct H as [H Hstart].
  induction i.
  - (* i = 0 *)
    unfold Start, BrachaRBProcess, BrachaRBStart in Hstart.
    destruct (e 0). simpl in *.
    subst st. simpl.
    intro. unfold empty_buffer in H0. inversion H0.
  - (* induction *)
    unfold Exec, ExecFragment in H. specialize H with i.
    have Htmp : S i = i + 1 by lia. rewrite Htmp. clear Htmp.
    destruct (e (i+1)). simpl in *.
    intro.
    rewrite <- H. destruct (e i). simpl in *.
    case_eq opt_act0 ; [intros act0 Hopt | intro Hopt] ; subst opt_act0.
    induction act0 ; simpl in *.
    + apply transition_echo_cond_extend_future with proc st0 (BrachaRBBroadcast m0) ; auto.
      apply IHi.
      subst st.
      unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed0.
      repeat simpl_match ; inversion is_well_formed0 ; subst st'0 ; try subst st' ;
        simpl in * ; repeat simpl_arith_bool ; auto ;
      unfold InternMessage_dec_bool in H0 ;
      simpl_match ; inversion n1 || inversion n0 || inversion H0 ; inversion H0.
    + apply transition_echo_cond_extend_future with proc st0 (BrachaRBDeliver p0 m0) ; auto. apply IHi.
      subst st.
      unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed0.
      repeat simpl_match ; inversion is_well_formed0 ; subst st'0 ; try subst st' ;
        simpl in * ; repeat simpl_arith_bool ; auto.
    + case_eq (BrachaRBSendBuffer st0 (p, Echo m)) ; intro.
      apply transition_echo_cond_extend_future with proc st0 (BrachaRBP2PRecv p0 p1 i0) ; auto.
      subst st.
      unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed0.
      induction i0.
      * repeat simpl_match ; inversion is_well_formed0 ; subst st'0 opt_act ; try subst st' ;
          simpl in * ; repeat simpl_arith_bool ;
          (rewrite H0 in H1 ; inversion H1) || auto ; simpl_InternMessage_dec_bool.
        {
          split. auto.
          assert (p1 = process_zero). apply process_proof_irrelevence. simpl. auto. subst p1.
          left. inversion H0. buffer_solver.
        }
        {
          split. auto. left.
          assert (p1 = process_zero). apply process_proof_irrelevence. simpl. auto. subst p1.
          inversion H0. buffer_solver.
        }
        {
          simpl_match ; simpl_InternMessage_dec_bool.
          inversion H5.
          simpl_match ; simpl_InternMessage_dec_bool.
          inversion H6.
          split. auto. left.
          assert (p1 = process_zero). apply process_proof_irrelevence. simpl. auto. subst p1.
          inversion H0. buffer_solver.
        }
        {
          simpl_match ; simpl_InternMessage_dec_bool.
          inversion H5.
          simpl_match ; simpl_InternMessage_dec_bool.
          inversion H6.
          split. auto. left.
          assert (p1 = process_zero). apply process_proof_irrelevence. simpl. auto. subst p1.
          inversion H0. buffer_solver.
        }
      * case_eq opt_act ; [intros act Hopt | intro Hopt] ; subst opt_act ;
        repeat simpl_match ; inversion is_well_formed0 ; subst ; simpl in * ; repeat simpl_arith_bool ; repeat simpl_InternMessage_dec_bool ;
        try (rewrite H0 in H1 ; inversion H1) ; inversion H0 ; split ; lia || right ; left ;
          inversion n0 || inversion n1 || inversion n2 || inversion n3 || auto ; try contradiction ;
          simpl_match ; simpl_InternMessage_dec_bool ; lia || contradiction.
      * case_eq opt_act ; [intros act Hopt | intro Hopt] ; subst opt_act ;
        repeat simpl_match ; inversion is_well_formed0 ; subst ; simpl in * ; repeat simpl_arith_bool ; repeat simpl_InternMessage_dec_bool ;
          try (rewrite H0 in H1 ; inversion H1) ; inversion H0 ; split ; lia || right ; right ;
          inversion n0 || inversion n1 || inversion n2 || inversion n3 || auto ; try contradiction ;
          simpl_match ; simpl_InternMessage_dec_bool ; lia || contradiction.
    + apply transition_echo_cond_extend_future with proc st0 (BrachaRBP2PSend p0 p1 i0) ; auto. apply IHi.
      subst st.
      unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed0.
      repeat simpl_match ; inversion is_well_formed0 ; subst st'0 ;
        simpl in * ; repeat simpl_arith_bool ; auto.
      unfold buffer_sub in H0. simpl_match. inversion H0. auto.
      subst. simpl in *. unfold buffer_sub in H0. simpl_match. inversion H0. auto.
    + subst. auto.
Qed.

Theorem send_ready_then_condition_satisfied :
  forall f : nat, forall proc : Process,
  forall e : ExecFragmentType (A := BrachaRBProcess f proc),
      Exec e ->
      forall i : nat, forall m : Message, forall p : Process,
        BrachaRBSendBuffer (st BrachaRBAction (BrachaRBProcess f proc) (e i)) (p, Ready m) = true ->
        BrachaRBStep (st BrachaRBAction (BrachaRBProcess f proc) (e i)) >= 3 /\ (
                                 BrachaRBRecvBufferSize (st BrachaRBAction (BrachaRBProcess f proc) (e i)) (Echo m) >= 2*f+1 \/
                                 BrachaRBRecvBufferSize (st BrachaRBAction (BrachaRBProcess f proc) (e i)) (Ready m) >= f+1
                              ).
Proof.
  intros.
  destruct H as [H Hstart].
  induction i.
  - (* i = 0 *)
    unfold Start, BrachaRBProcess, BrachaRBStart in Hstart.
    destruct (e 0). simpl in *.
    subst st. simpl in *.
    unfold empty_buffer in H0. inversion H0.
  - (* induction *)
    unfold Exec, ExecFragment in H. specialize H with i.
    have Htmp : S i = i + 1 by lia. rewrite Htmp in H0 |- *. clear Htmp.
    destruct (e (i+1)). simpl in *.
    rewrite <- H. destruct (e i). simpl in *.
    case_eq opt_act0 ; [intros act0 Hopt | intro Hopt] ; subst opt_act0.
    induction act0 ; simpl in *.
    + apply transition_ready_cond_extend_future with proc st0 (BrachaRBBroadcast m0) ; auto. apply IHi.
      subst st.
      unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed0.
      repeat simpl_match ; inversion is_well_formed0 ; subst ;
        simpl in * ; repeat simpl_arith_bool ; auto ;
      simpl_InternMessage_dec_bool ; inversion H0.
    + apply transition_ready_cond_extend_future with proc st0 (BrachaRBDeliver p0 m0) ; auto. apply IHi.
      subst st.
      unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed0.
      repeat simpl_match ; inversion is_well_formed0 ; subst ;
        simpl in * ; repeat simpl_arith_bool ; auto.
    + case_eq (BrachaRBSendBuffer st0 (p, Ready m)) ; intro.
      apply transition_ready_cond_extend_future with proc st0 (BrachaRBP2PRecv p0 p1 i0) ; auto.
      subst.
      unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed0.
      induction i0.
      * repeat simpl_match ; inversion is_well_formed0 ; subst ; simpl in * ; repeat simpl_arith_bool ; simpl_InternMessage_dec_bool ;
          try (rewrite H0 in H1 ; inversion H1) ; try inversion H0.
      * repeat simpl_match ; inversion is_well_formed0 ;
          subst ; simpl in * ; repeat simpl_arith_bool ; simpl_InternMessage_dec_bool ; (rewrite H0 in H1 ; inversion H1) ; inversion H0 ;
          split ; lia || left ; auto ; repeat simpl_match ; simpl_InternMessage_dec_bool ; lia || contradiction.
      * repeat simpl_match ; inversion is_well_formed0 ;
          subst ; simpl in * ; repeat simpl_arith_bool ; simpl_InternMessage_dec_bool ; (rewrite H0 in H1 ; inversion H1) ; inversion H0 ;
          split ; lia || right ; subst ; repeat simpl_match ; simpl_InternMessage_dec_bool ; try inversion H7 ; lia || contradiction.
    + apply transition_ready_cond_extend_future with proc st0 (BrachaRBP2PSend p0 p1 i0) ; auto. apply IHi.
      subst st.
      unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed0.
      repeat simpl_match ; inversion is_well_formed0 ; subst ;
        simpl in * ; repeat simpl_arith_bool ; auto.
      unfold buffer_sub in H0. simpl_match. inversion H0. auto.
      unfold buffer_sub in H0. simpl_match. inversion H0. auto.
    + subst. auto.
Qed.

Theorem deliver_then_condition_satisfied :
  forall f : nat, forall proc : Process,
  forall e : ExecFragmentType (A := BrachaRBProcess f proc),
      Exec e ->
      forall i : nat, forall m : Message, forall p : Process,
        let (st, act, st', _) := (e i) in
        act = Some (BrachaRBDeliver proc m) ->
        BrachaRBStep st = 4 /\ BrachaRBRecvBufferSize st (Ready m) >= 2*f+1.
Proof.
  intros.
  destruct H as [H Hstart].
  destruct (e i). intro. simpl in *.
  subst opt_act.
  unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed.
  repeat simpl_match ; inversion is_well_formed ; subst st' ; repeat simpl_arith_bool ; simpl in * ; lia.
Qed.

(* ----------------------------------------
  Liveness properties
 ---------------------------------------- *)

Open Scope ltl_scope.

(* -------------------- Send buffer properties -------------------- *)

Theorem message_in_send_buffer_eventually_sent :
  forall f : nat, forall proc : Process,
  forall e : ExecFragmentType (A := BrachaRBProcess f proc),
      Exec e -> FairFragment e ->
      forall i : nat, forall m : InternMessage, forall p : Process,
        BrachaRBSendBuffer (st BrachaRBAction (BrachaRBProcess f proc) (e i)) (p, m) = true ->
        e $ i |=
          F (N (fun s =>
                    (opt_act BrachaRBAction (BrachaRBProcess f proc) s) =
                    Some (BrachaRBP2PSend proc p m))).
Proof.
  intros.
  pose (BrachaRBP2PSend proc p m) as act.
  destruct_fair_exec ; unfold act in *.
  + (* will happen *)
    destruct Hineq. exists x. intuition.
  + (* case 0 *)
    intros.
    have Heq : j = i by lia. subst j.
    intuition. unfold ltl_now in H4.
    destruct (e i). simpl in *.
    unfold BrachaRBTransition, BrachaRB_compute_transition in H4.
    assert (Heq : proj1_sig proc =? proj1_sig proc = true). simpl_arith_bool. auto.
    rewrite Heq H1 in H4. simpl in H4. clear Heq.
    specialize H4 with ({|
           BrachaRBStep := BrachaRBStep st;
           BrachaRBRecvBuffer := BrachaRBRecvBuffer st;
           BrachaRBRecvBufferSize := BrachaRBRecvBufferSize st;
           BrachaRBSendBuffer := buffer_sub packet_dec (BrachaRBSendBuffer st) (p, m)
         |}).
    contradiction.
  + (* induction *)
    intros.
    destruct BrachaRBOptionAction_dec with
      (IOA.opt_act BrachaRBAction (BrachaRBProcess f proc) (e (j-1)))
      (Some (BrachaRBP2PSend proc p m)).
    exists (j-1). intuition. lia.
    destruct H as [H Hstart]. unfold ExecFragment in H. specialize H with (j - 1).
    have Htmp : j - 1 + 1 = j by lia. rewrite Htmp in H. clear Htmp.
    apply IHn with (j - 1).
    - lia.
    - intro. exists j. intuition.
    - auto.
    - destruct Hineq. destruct H3 as [H4 H5].
      unfold ltl_now in H4.
      pose (p, m) as pack.
      assert (Hbuffer_status : forall st'0 : State (BrachaRBProcess f proc), ~ Transition
                                                   (BrachaRBProcess f proc)
                                                   (st BrachaRBAction (BrachaRBProcess f proc) (e j))
                                                   (BrachaRBP2PSend proc (fst pack) (snd pack))
                                                   st'0).
      auto.
      apply transition_send_not_enabled_is_not_in_buffer in Hbuffer_status.
      split ; split || lia ; auto.
      unfold ltl_now.
      intro.
      unfold Transition, BrachaRBProcess, BrachaRBTransition, BrachaRB_compute_transition.
      have Htmp : proj1_sig proc =? proj1_sig proc = true by simpl_arith_bool ; auto.
      rewrite Htmp. clear Htmp.
      simpl.
      destruct (e (j - 1)). simpl in *.
      case_eq (BrachaRBSendBuffer st (p, m)) ; intro ; discriminate || auto.
      intro Htmp ; injection Htmp ; clear Htmp ; intros Heq.
      unfold BrachaRBTransition, BrachaRB_compute_transition in is_well_formed.
      simpl in is_well_formed.
      case_eq opt_act ; [intros act0 Hopt | intro Hopt] ; subst.
      induction act0.
      * simpl_match ; simpl_match || idtac ; inversion is_well_formed.
        rewrite <-H8 in Hbuffer_status. simpl in Hbuffer_status.
        repeat simpl_arith_bool. unfold pack in H7. rewrite H7 in H3. inversion H3.
        subst. unfold pack in Hbuffer_status. rewrite Hbuffer_status in H3. inversion H3.
      * simpl_match ; inversion is_well_formed. rewrite <-H7 in Hbuffer_status. simpl in Hbuffer_status.
        unfold pack in Hbuffer_status. rewrite Hbuffer_status in H3. inversion H3.
      * induction i0.
        {
          repeat simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ;
          rewrite <-H9 in Hbuffer_status || rewrite <-H10 in Hbuffer_status || idtac ; simpl in Hbuffer_status ; unfold pack in Hbuffer_status ;
          repeat simpl_arith_bool ; rewrite H9 in H3 || idtac ; inversion H3 ;
          rewrite Hbuffer_status in H3 ; inversion H3.
        }
        {
          repeat simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ;
          rewrite <-H9 in Hbuffer_status || rewrite <-H10 in Hbuffer_status || rewrite <-H11 in Hbuffer_status || rewrite <-H12 in Hbuffer_status || idtac
          ; simpl in Hbuffer_status ; unfold pack in Hbuffer_status ;
          repeat simpl_arith_bool ; rewrite H9 in H3 || rewrite H11 in H3 || rewrite H10 in H3 || idtac ; inversion H3 ;
          rewrite Hbuffer_status in H3 || idtac ; inversion H3.
        }
        {
          repeat simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ;
          rewrite <-H10 in Hbuffer_status || rewrite <-H11 in Hbuffer_status || rewrite <-H12 in Hbuffer_status || rewrite <-H13 in Hbuffer_status || idtac
          ; simpl in Hbuffer_status ; unfold pack in Hbuffer_status ;
          repeat simpl_arith_bool ; rewrite H9 in H3 || rewrite H11 in H3 || rewrite H10 in H3 || idtac ; inversion H3 ;
          rewrite Hbuffer_status in H3 || idtac ; inversion H3.
        }
      * simpl_match ; inversion is_well_formed. rewrite <-H7 in Hbuffer_status. simpl in Hbuffer_status.
        unfold pack in Hbuffer_status.
        repeat simpl_arith_bool. assert (p0 = proc). apply process_proof_irrelevence. auto.
        assert (BrachaRBP2PSend p0 p1 i0 <> BrachaRBP2PSend proc p m).
        intro. apply n0. rewrite H9. auto.
        destruct_BrachaRBAction_eq in H9.
        assert (buffer_sub packet_dec (BrachaRBSendBuffer st) (p1, i0) (p, m) = true). subst.
        decompose [or] H9.
        assert ((p1, i0) <> (p, m)). intro. apply H8. inversion H10. auto.
        rewrite buffer_sub_keep_other_unchaged ; auto.
        contradiction.
        assert ((p1, i0) <> (p, m)). intro. apply H10. inversion H8. auto.
        rewrite buffer_sub_keep_other_unchaged ; auto.
        rewrite Hbuffer_status in H10. inversion H10.
      * subst. unfold pack in Hbuffer_status. rewrite Hbuffer_status in H3. inversion H3.
Qed.
