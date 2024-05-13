Require Import common.IOA.
Require Import common.LTL.
Require Import common.tactic.
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
  Properties on past actions
 ---------------------------------------- *)

Theorem init_then_broadcast_before :
  forall f : nat,
  forall e : ExecFragmentType (A := BrachaRBLeader f),
      Exec e ->
      forall i : nat, forall m : Message,
        act BrachaRBAction (BrachaRBLeader f) (e i) = BrachaRBP2PSend process_zero process_zero (Init m) ->
        exists j : nat, j < i /\ act BrachaRBAction (BrachaRBLeader f) (e j) = BrachaRBBroadcast m.
Proof.
  intros.
  (* we build a goal such that we show the existance by induction *)
  assert (
      forall j : nat,
        (exists k : nat, k >= i - j /\ k < i /\ act BrachaRBAction (BrachaRBLeader f) (e k) = BrachaRBBroadcast m) \/
        (BrachaRBSendBuffer (st BrachaRBAction (BrachaRBLeader f) (e (i - j))) (process_zero, (Init m)) = true)
    ).
  induction j.
  + (* case i *)
    right. assert (i - 0 = i). lia. rewrite H1. clear H1.
    destruct (e i) ; simpl in *. rewrite H0 in is_well_formed.
    unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in is_well_formed.
    simpl_match ; inversion is_well_formed ; repeat simpl_arith_bool ; auto.
  + (* induction *)
    destruct H as [H Hstart]. unfold ExecFragment in H. specialize H with (i - S j).
    destruct IHj. left. destruct H1. exists x. intuition. lia.
    case_eq (i - j =? 0) ; intro Heq ; simpl_arith_bool.
    unfold Start, BrachaRBLeader, BrachaRBLeaderStart in Hstart.
    simpl in Hstart.
    rewrite Heq in H1. destruct (e 0). simpl in *. rewrite Hstart in H1. simpl in H1. unfold BrachaRBBuffer_empty_set in H1. inversion H1.
    case_eq (act BrachaRBAction (BrachaRBLeader f) (e (i - S j))) ; intros.
    - (* broadcast *)
      case_eq (Message_dec m0 m) ; intros.
      * left. exists (i - S j). intuition. lia. subst m0. auto.
      * right. destruct (e (i - S j)). simpl in *.
        rewrite H2 in is_well_formed.
        unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in is_well_formed.
        simpl in is_well_formed.
        simpl_match ; inversion is_well_formed ; repeat simpl_arith_bool.
        rewrite H in H6. have : i - S j + 1 = i - j by lia. intro Htmp ; rewrite Htmp in H6 ; clear Htmp.
        assert (BrachaRBSendBuffer st (process_zero, Init m) || InternMessage_dec_bool (Init m) (Init m0) =
            BrachaRBSendBuffer (IOA.st BrachaRBAction (BrachaRBLeader f) (e (i - j))) (process_zero, Init m)).
        rewrite <-H6. simpl. auto.
        unfold InternMessage_dec_bool in H5.
        simpl_match. inversion n1. subst m0. contradiction.
        rewrite orb_false_r in H5.
        rewrite H1 in H5. auto.
        rewrite H. have -> : i - S j + 1 = i - j by lia. auto.
    - (* Deliver *)
      right.
      destruct (e (i - S j)). simpl in *.
      rewrite H in is_well_formed. rewrite H2 in is_well_formed.
      assert (Htmp : i - S j + 1 = i - j). lia. rewrite Htmp in is_well_formed ; clear Htmp.
      case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool.
      * unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in is_well_formed.
        simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ; rewrite <-H8 in H1 ; simpl in H1 ; auto.
      * unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in is_well_formed.
        simpl_match ; repeat simpl_arith_bool ; contradiction || inversion is_well_formed.
    - (* Recv *)
      right.
      destruct (e (i - S j)). simpl in *.
      rewrite H in is_well_formed. rewrite H2 in is_well_formed.
      assert (Htmp : i - S j + 1 = i - j). lia. rewrite Htmp in is_well_formed ; clear Htmp.
      case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool.
      * unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in is_well_formed.
        induction i0.
        {
          rewrite H3 in is_well_formed. simpl in is_well_formed.
          simpl_match ; repeat simpl_arith_bool ;
          simplify_eq is_well_formed ; clear is_well_formed ; intro is_well_formed ;
            rewrite <-is_well_formed in H1 ; simpl in H1 ; repeat simpl_arith_bool ; auto.
          unfold InternMessage_dec_bool in H1. repeat simpl_match ; simplify_eq n0 || inversion H1.
        }
        {
          rewrite H3 in is_well_formed. simpl in is_well_formed.
          repeat simpl_match ; repeat simpl_arith_bool ;
          simplify_eq is_well_formed ; clear is_well_formed ; intro is_well_formed ;
            rewrite <-is_well_formed in H1 ; simpl in H1 ; repeat simpl_arith_bool ; auto ;
          unfold InternMessage_dec_bool in H1 ; repeat simpl_match ; simplify_eq n0 || simplify_eq n1 || inversion H1.
        }
        {
          rewrite H3 in is_well_formed. simpl in is_well_formed.
          repeat simpl_match ; repeat simpl_arith_bool ;
          simplify_eq is_well_formed ; clear is_well_formed ; intro is_well_formed ;
            rewrite <-is_well_formed in H1 ; simpl in H1 ; repeat simpl_arith_bool ; auto ;
          unfold InternMessage_dec_bool in H1 ; repeat simpl_match ; simplify_eq n0 || simplify_eq n1 || inversion H1.
        }
      * unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in is_well_formed.
        simpl_match. simpl_arith_bool. contradiction. simplify_eq is_well_formed.
    - (* Send *)
      right.
      destruct (e (i - S j)). simpl in *.
      rewrite H in is_well_formed. rewrite H2 in is_well_formed.
      assert (Htmp : i - S j + 1 = i - j). lia. rewrite Htmp in is_well_formed ; clear Htmp.
      case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool.
      * unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in is_well_formed.
        induction i0.
        {
          rewrite H3 in is_well_formed. simpl in is_well_formed. unfold BrachaRBBuffer_sub in is_well_formed.
          repeat simpl_match ; repeat simpl_arith_bool ;
          simplify_eq is_well_formed ; clear is_well_formed ; intro is_well_formed ;
            rewrite <-is_well_formed in H1 ; simpl in H1 ; repeat simpl_arith_bool ; auto.
          unfold InternMessage_dec_bool in H1. repeat simpl_match ; simplify_eq n0 || inversion H1 ; auto ; (intro ; subst m0 ; inversion H1 ; auto).
        }
        {
          rewrite H3 in is_well_formed. simpl in is_well_formed. unfold BrachaRBBuffer_sub in is_well_formed.
          repeat simpl_match ; repeat simpl_arith_bool ;
          simplify_eq is_well_formed ; clear is_well_formed ; intro is_well_formed ;
            rewrite <-is_well_formed in H1 ; simpl in H1 ; repeat simpl_arith_bool ; auto ;
          unfold InternMessage_dec_bool in H1 ; repeat simpl_match ; simplify_eq n0 || simplify_eq n1 || inversion H1 ; auto.
        }
        {
          rewrite H3 in is_well_formed. simpl in is_well_formed. unfold BrachaRBBuffer_sub in is_well_formed.
          repeat simpl_match ; repeat simpl_arith_bool ;
          simplify_eq is_well_formed ; clear is_well_formed ; intro is_well_formed ;
            rewrite <-is_well_formed in H1 ; simpl in H1 ; repeat simpl_arith_bool ; auto ;
          unfold InternMessage_dec_bool in H1 ; repeat simpl_match ; simplify_eq n0 || simplify_eq n1 || inversion H1 ; auto.
        }
      * unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in is_well_formed.
        simpl_match ; repeat simpl_arith_bool ; contradiction || simplify_eq is_well_formed.
  + (* conclusion *)
    specialize H1 with i. destruct H1.
    - destruct H1. exists x. intuition.
    - destruct H as [H Hstart]. unfold Start, BrachaRBLeaderStart in Hstart.
      unfold CompositionExtended in H1. assert (i-i = 0). lia. rewrite H2 in H1. simpl in H1. rewrite Hstart in H1.
      simpl in H1. unfold BrachaRBBuffer_empty_set in H1. inversion H2. inversion H1.
Qed.

Theorem in_recv_buffer_then_have_recv :
  forall f : nat,
  forall e : ExecFragmentType (A := BrachaRBLeader f),
      Exec e ->
      forall i : nat, forall m : InternMessage, forall p : Process,
        BrachaRBRecvBuffer (st BrachaRBAction (BrachaRBLeader f) (e i)) (p, m) = true ->
        exists j : nat,
          j < i /\
            BrachaRBAction_eq (act BrachaRBAction (BrachaRBLeader f) (e j)) (BrachaRBP2PRecv process_zero p m).
Proof.
  intros.
  assert (
      forall j : nat,
        (exists k : nat, k >= i - j /\ k < i /\ BrachaRBAction_eq (act BrachaRBAction (BrachaRBLeader f) (e k)) (BrachaRBP2PRecv process_zero p m)) \/
        (BrachaRBRecvBuffer (st BrachaRBAction (BrachaRBLeader f) (e (i - j))) (p, m) = true)
    ).
  induction j.
  + (* case i *)
    right. have Heq : i - 0 = i by lia. rewrite Heq. auto.
  + (* induction *)
    destruct H as [H Hstart]. unfold ExecFragment in H. specialize H with (i - S j).
    destruct IHj. left. destruct H1. exists x. intuition. lia.
    case_eq (i - j =? 0) ; intro Heq ; simpl_arith_bool.
    unfold Start, BrachaRBLeader, BrachaRBLeaderStart in Hstart.
    rewrite Heq in H1. destruct (e 0). simpl in *. rewrite Hstart in H1. simpl in H1. unfold BrachaRBBuffer_empty_set in H1. inversion H1.
    case_eq (act BrachaRBAction (BrachaRBLeader f) (e (i - S j))) ; intros.
    - (* broadcast *)
      right.
      destruct (e (i - S j)). simpl in *.
      rewrite H in is_well_formed. rewrite H2 in is_well_formed.
      assert (Htmp : i - S j + 1 = i - j). lia. rewrite Htmp in is_well_formed ; clear Htmp.
      case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
        unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in is_well_formed ;
        simpl in is_well_formed ;
        simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ; auto ; rewrite <-H6 in H1 ; auto.
    - (* deliver *)
      right.
      destruct (e (i - S j)). simpl in *.
      rewrite H in is_well_formed. rewrite H2 in is_well_formed.
      assert (Htmp : i - S j + 1 = i - j). lia. rewrite Htmp in is_well_formed ; clear Htmp.
      case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
        unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in is_well_formed ;
        simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ; auto ; rewrite <-H8 in H1 ; auto.
    - (* Recv, i.e. or the interesting part *)
      (* I really think it is possible to automate all of this, even at process level by usig a bunch of strategies, I have to sleep on this one *)
      case_eq (proj1_sig p0 =? 0) ; intro ; cycle 1.
      destruct (e (i - S j)). simpl in *. rewrite H2 in is_well_formed.
      unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in is_well_formed.
      repeat simpl_match ;
        match goal with
          | [H : true = false |- _] => inversion H
          | _ => auto
        end
      ; inversion is_well_formed.
      simpl_arith_bool.
      case_eq (InternMessage_dec m i0) ; case_eq (proj1_sig p =? proj1_sig p1) ; intros ; simpl_arith_bool.
      * left. exists (i - S j). intuition. lia. unfold BrachaRBAction_eq. rewrite H2. intuition.
      * right.
        destruct (e (i - S j)). simpl in *. rewrite H2 in is_well_formed.
        unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in is_well_formed.
        have Htmp : i - S j + 1 = i - j by lia. rewrite Htmp in H. clear Htmp.
        rewrite <-H in H1.
        rewrite H3 in is_well_formed. simpl in is_well_formed.
        induction i0 ;
        repeat simpl_match ; repeat simpl_arith_bool ; auto ; inversion is_well_formed as [Hinv] ; rewrite <-Hinv in H1 ;
          simpl in H1 ; unfold BrachaRBBuffer_add, BrachaRBBuffer_sub in H1 ; simpl_match ; repeat simpl_arith_bool ;
          simpl in * ; contradiction || (unfold InternMessage_dec_bool in * ; simpl_match ; auto) || auto.
      * right.
        destruct (e (i - S j)). simpl in *. rewrite H2 in is_well_formed.
        unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in is_well_formed.
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
        unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in is_well_formed.
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
        unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in is_well_formed ;
        simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ; auto ; rewrite <-H7 in H1 ; auto.
  + specialize H1 with i. destruct H1.
    - destruct H1. exists x. intuition.
    - have Htmp : i-i = 0 by lia. rewrite Htmp in H1. clear Htmp.
      destruct H as [H Hstart]. unfold Start, BrachaRBLeader, BrachaRBLeaderStart in Hstart, H1.
      rewrite Hstart in H1. simpl in H1. unfold BrachaRBBuffer_empty_set in H1. inversion H1.
Qed.

(* ----------------------------------------
  Safety properties
 ---------------------------------------- *)

Lemma transition_increase_step :
  forall f : nat, forall st st' : BrachaRBState, forall act : BrachaRBAction,
    Transition (BrachaRBLeader f) st act st' -> BrachaRBStep st <= BrachaRBStep st'.
Proof.
  intros.
  induction act ;
    unfold
      Transition,
      BrachaRBLeader,
      BrachaRBLeaderTransition,
      BrachaRB_compute_transition in H ; simpl in H ;
    simpl_match ; repeat simpl_arith_bool ; (inversion H ; auto ; fail) || auto.
  - inversion H. rewrite H0. simpl. auto.
  - inversion H. rewrite H2. simpl. auto.
  - induction i ; repeat simpl_match ; repeat simpl_arith_bool ; inversion H ; simpl ;
      match goal with
        | [H : BrachaRBStep st = _ |- _] => rewrite H
        | _ => auto
      end ; auto.
Qed.

Theorem step_numbers_increasing :
  forall f : nat,
    forall e : ExecFragmentType (A := BrachaRBLeader f),
      Exec e ->
      forall i : nat,
        BrachaRBStep (st BrachaRBAction (BrachaRBLeader f) (e i)) <=
          BrachaRBStep (st' BrachaRBAction (BrachaRBLeader f) (e i)).
Proof.
  intros. destruct (e i). simpl in *. apply transition_increase_step with f act. auto.
Qed.

Lemma transition_increase_by_one_step :
  forall f : nat, forall st st' : BrachaRBState, forall act : BrachaRBAction,
    Transition (BrachaRBLeader f) st act st' -> BrachaRBStep st' <= BrachaRBStep st + 1.
Proof.
  intros.
  induction act ;
    unfold
      Transition,
      BrachaRBLeader,
      BrachaRBLeaderTransition,
      BrachaRB_compute_transition in H ; simpl in H ;
    simpl_match ; repeat simpl_arith_bool ; (inversion H ; auto ; fail) || auto.
  - inversion H. rewrite H0. simpl. auto.
  - inversion H. lia.
  - inversion H. rewrite H2. simpl. auto.
  - induction i ; repeat simpl_match ; repeat simpl_arith_bool ; inversion H ; simpl ;
      match goal with
        | [H : BrachaRBStep st = _ |- _] => rewrite H
        | _ => auto
      end ; auto ; lia.
  - inversion H. simpl. lia.
Qed.

Theorem step_numbers_increase_by_one :
  forall f : nat,
    forall e : ExecFragmentType (A := BrachaRBLeader f),
      Exec e ->
      forall i : nat,
        BrachaRBStep (st' BrachaRBAction (BrachaRBLeader f) (e i)) <=
          BrachaRBStep (st BrachaRBAction (BrachaRBLeader f) (e i)) + 1.
Proof.
  intros. destruct (e i). simpl in *. apply transition_increase_by_one_step with f act. auto.
Qed.

Lemma only_send_remove_from_send_buffer :
  forall f : nat, forall st st' : BrachaRBState, forall act : BrachaRBAction, forall pack : Packet,
    Transition (BrachaRBLeader f) st act st' -> (forall m : Message, act <> BrachaRBBroadcast m) ->
    BrachaRBSendBuffer st pack = true -> BrachaRBSendBuffer st' pack = true <-> act <> BrachaRBP2PSend process_zero (fst pack) (snd pack).
Proof.
  intros f st st' act pack H Hnot_broadcast H0.
  split. intro.
  + induction act ; discriminate || auto.
    destruct pack. simpl in *.
    unfold Transition, BrachaRBLeader, BrachaRBLeaderTransition, BrachaRB_compute_transition in H.
    have Heq : proj1_sig process_zero = 0 by auto.
    simpl_match ; repeat simpl_arith_bool.
    assert (p = process_zero). apply process_proof_irrelevence. auto.
    rewrite H4. inversion H as [Hst]. clear H. rewrite <-Hst in H1. simpl in H1.
    unfold BrachaRBBuffer_sub in H1. simpl in H1.
    simpl_match ; repeat simpl_arith_bool. inversion H1.
    unfold InternMessage_dec_bool in H.
    simpl_match. inversion H. intro. inversion H6. contradiction.
    intro. inversion H5. rewrite H7 in H. contradiction.
    inversion H. inversion H.
  + intro.
    unfold Transition, BrachaRBLeader, BrachaRBLeaderTransition, BrachaRB_compute_transition in H.
    induction act.
    - specialize Hnot_broadcast with m. contradiction.
    - simpl_match ; repeat simpl_arith_bool ; inversion H.
      simpl. auto.
    - destruct pack ; simpl in *. repeat simpl_match ; repeat simpl_arith_bool ;
      inversion H ; simpl ; repeat simpl_arith_bool ; auto.
    - simpl_match ; repeat simpl_arith_bool ; inversion H.
      simpl. unfold BrachaRBBuffer_sub. simpl_match ; repeat simpl_arith_bool ; auto.
      destruct pack ; simpl in *. apply process_proof_irrelevence in H6. subst p0.
      assert (p = process_zero). apply process_proof_irrelevence. auto. subst p.
      unfold InternMessage_dec_bool in H4. simpl_match. subst i0. contradiction. inversion H4.
Qed.

Lemma send_not_enabled_is_not_in_buffer :
  forall f : nat, forall st : BrachaRBState, forall pack : Packet,
    (forall st' : BrachaRBState, ~Transition (BrachaRBLeader f) st (BrachaRBP2PSend process_zero (fst pack) (snd pack)) st') -> BrachaRBSendBuffer st pack = false.
Proof.
  intros.
  unfold Transition, BrachaRBLeader, BrachaRBLeaderTransition, BrachaRB_compute_transition in H.
  simpl_match ; repeat simpl_arith_bool.
  specialize H with ({|
          BrachaRBStep := BrachaRBStep st;
          BrachaRBRecvBuffer := BrachaRBRecvBuffer st;
          BrachaRBRecvBufferSize := BrachaRBRecvBufferSize st;
          BrachaRBSendBuffer := BrachaRBBuffer_sub (BrachaRBSendBuffer st) (fst pack) (snd pack)
        |}). contradiction.
  contradiction.
  destruct pack. simpl in H0. auto.
Qed.

(* ----------------------------------------
  Liveness properties
 ---------------------------------------- *)

Open Scope ltl_scope.

Theorem message_in_send_buffer_eventually_sent :
  forall f : nat,
  forall e : ExecFragmentType (A := BrachaRBLeader f),
      Exec e -> FairFragment e ->
      forall i : nat, forall m : InternMessage, forall p : Process,
        BrachaRBSendBuffer (st BrachaRBAction (BrachaRBLeader f) (e i)) (p, m) = true ->
        e $ i |=
          F (N (fun s =>
                  BrachaRBAction_eq
                    (act BrachaRBAction (BrachaRBLeader f) s)
                    (BrachaRBP2PSend process_zero p m))).
Proof.
  intros.
  pose (BrachaRBP2PSend process_zero p m) as act.
  destruct_fair_exec ; unfold act in *.
  + (* will happen *)
    destruct Hineq. exists x. intuition. unfold ltl_now in *. unfold BrachaRBAction_eq. rewrite H2. auto.
  + (* case 0 *)
    intros.
    have Heq : j = i by lia. subst j.
    intuition. unfold ltl_now in H4.
    destruct (e i). simpl in *.
    have Heq : proj1_sig process_zero = 0 by auto.
    unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in H4.
    rewrite Heq H1 in H4. simpl in H4. clear Heq.
    specialize H4 with ({|
                     BrachaRBStep := BrachaRBStep st;
                     BrachaRBRecvBuffer := BrachaRBRecvBuffer st;
                     BrachaRBRecvBufferSize := BrachaRBRecvBufferSize st;
                     BrachaRBSendBuffer := BrachaRBBuffer_sub (BrachaRBSendBuffer st) p m
                   |}).
    contradiction.
  + (* induction *)
    intros.
    assert ({BrachaRBAction_eq (IOA.act BrachaRBAction (BrachaRBLeader f) (e (j-1))) (BrachaRBP2PSend process_zero p m)}+
              {~BrachaRBAction_eq (IOA.act BrachaRBAction (BrachaRBLeader f) (e (j-1))) (BrachaRBP2PSend process_zero p m)}).
    unfold BrachaRBAction_eq.
    case (IOA.act BrachaRBAction (BrachaRBLeader f) (e (j-1))) ; auto. intros.
    case_eq ((proj1_sig p0 =? proj1_sig process_zero) && (proj1_sig p1 =? proj1_sig p) && (InternMessage_dec_bool i0 m)) ;
      intro ; repeat simpl_arith_bool.
    left. intuition.
    unfold InternMessage_dec_bool in H3. simpl_match ; inversion H3 || auto.
    right. repeat simpl_arith_bool ; intuition.
    unfold InternMessage_dec_bool in H2. simpl_match ; inversion H2 ; contradiction.
    destruct H2.
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
      assert (Hbuffer_status : forall st'0 : State (BrachaRBLeader f), ~ Transition
                                                   (BrachaRBLeader f)
                                                   (st BrachaRBAction (BrachaRBLeader f) (e j))
                                                   (BrachaRBP2PSend process_zero (fst pack) (snd pack))
                                                   st'0).
      auto.
      apply send_not_enabled_is_not_in_buffer in Hbuffer_status.
      split ; split || lia ; auto.
      unfold ltl_now.
      intro.
      unfold Transition, BrachaRBLeader, BrachaRBLeaderTransition, BrachaRB_compute_transition.
      unfold proj1_sig, process_zero. simpl.
      destruct (e (j - 1)). simpl in *.
      case_eq (BrachaRBSendBuffer st (p, m)) ; intro ; discriminate || auto.
      intro Htmp ; injection Htmp ; clear Htmp ; intros Heq.
      unfold BrachaRBLeaderTransition, BrachaRB_compute_transition in is_well_formed.
      simpl in is_well_formed. induction act0.
      * simpl_match ; inversion is_well_formed. rewrite <-H, <-H8 in Hbuffer_status. simpl in Hbuffer_status.
        repeat simpl_arith_bool. unfold pack in H7. rewrite H7 in H3. inversion H3.
        rewrite H8 in H3. rewrite <-H in Hbuffer_status. rewrite Hbuffer_status in H3. inversion H3.
      * simpl_match ; inversion is_well_formed. rewrite <-H, <-H8 in Hbuffer_status. simpl in Hbuffer_status.
        unfold pack in Hbuffer_status. rewrite Hbuffer_status in H3. inversion H3.
      * induction i0.
        {
          repeat simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ;
          rewrite <-H, <-H11 in Hbuffer_status || rewrite <-H, <-H10 in Hbuffer_status ; simpl in Hbuffer_status ; unfold pack in Hbuffer_status ;
          repeat simpl_arith_bool ; rewrite H10 in H3 || idtac ; inversion H3 ;
          rewrite Hbuffer_status in H3 ; inversion H3.
        }
        {
          repeat simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ;
          rewrite <-H, <-H11 in Hbuffer_status || rewrite <-H, <-H10 in Hbuffer_status || rewrite <-H, <-H12 in Hbuffer_status || rewrite <-H, <-H13 in Hbuffer_status
          ; simpl in Hbuffer_status ; unfold pack in Hbuffer_status ;
          repeat simpl_arith_bool ; rewrite H11 in H3 || rewrite H10 in H3 || rewrite H12 in H3 || idtac ; inversion H3 ;
          rewrite Hbuffer_status in H3 || idtac ; inversion H3.
        }
        {
          repeat simpl_match ; repeat simpl_arith_bool ; inversion is_well_formed ;
          rewrite <-H, <-H11 in Hbuffer_status || rewrite <-H, <-H14 in Hbuffer_status || rewrite <-H, <-H12 in Hbuffer_status || rewrite <-H, <-H13 in Hbuffer_status || idtac
          ; simpl in Hbuffer_status ; unfold pack in Hbuffer_status ;
          repeat simpl_arith_bool ; rewrite H11 in H3 || rewrite H10 in H3 || rewrite H12 in H3 || idtac ; inversion H3 ;
          rewrite Hbuffer_status in H3 || idtac ; inversion H3.
        }
      * simpl_match ; inversion is_well_formed. rewrite <-H, <-H8 in Hbuffer_status. simpl in Hbuffer_status.
        unfold pack in Hbuffer_status. unfold BrachaRBBuffer_sub in Hbuffer_status.
        simpl_match ; repeat simpl_arith_bool. unfold InternMessage_dec_bool in H7. simpl_match ; inversion H7. simpl in n2.
        subst i0. assert (proj1_sig p0 = proj1_sig process_zero). rewrite H6. auto. apply process_proof_irrelevence in H12.
        subst p0. simpl in H9. apply process_proof_irrelevence in H9. subst p1.
        unfold BrachaRBAction_eq in n0. simpl in n0. apply n0. auto.
        rewrite Hbuffer_status in H3. inversion H3.
        rewrite Hbuffer_status in H3. inversion H3.
Qed.
