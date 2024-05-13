Require Import common.IOA.
Require Import common.LTL.
Require Import Lia.
Require Import Arith.
Require Import common.tactic.

Set Implicit Arguments.

Section P2P.
  Variable Message : Set.
  Hypothesis Message_dec : forall m m' : Message, {m = m'}+{m <> m'}.
  Hypothesis Message_forall_dec : forall P : Message -> Prop, (forall m : Message, {P m}+{~P m}) -> {forall m : Message, P m}+{~forall m : Message, P m}.
  Variable ActionPool : Set.

  Lemma Message_dec_eq : forall m : Message, exists e : m = m,  Message_dec m m = left e.
  Proof.
    intros. case_eq (Message_dec m m) ; intros ; auto. exists e. auto. contradiction.
  Qed.

  Inductive P2PInterface : Set :=
    | P2PRecv : Message -> P2PInterface
    | P2PSend : Message -> P2PInterface.

  Variable Interface : ActionPool -> option P2PInterface.
  Hypothesis Interface_injective : forall a : P2PInterface, exists act : ActionPool, Interface act = Some(a).

  Definition P2PState :=
    Message -> nat.

  Definition P2PState_empty_set : P2PState :=
    fun m : Message => 0.

  Definition P2PState_add (st : P2PState) (m : Message) : P2PState :=
    fun m0 : Message => if Message_dec m m0 then (st m0) + 1 else st m0.

  Definition P2PState_sub (st : P2PState) (m : Message) : P2PState :=
    fun m0 : Message => if Message_dec m m0 then (st m0) - 1 else st m0.

  Lemma P2PUnusedActionLemma :
   forall act : ActionPool,
     match Interface act with
     | Some (P2PRecv _) => Output
     | Some (P2PSend _) => Input
     | None => Unused
     end = Unused ->
     forall st st' : P2PState,
       ~
         match Interface act with
         | Some (P2PRecv m) => forall m' : Message, st m' = P2PState_add st' m m'
         | Some (P2PSend m) => forall m' : Message, st' m' = P2PState_add st m m'
         | None => False
         end.
  Proof.
    intros act H st st'.
    case_eq (Interface act) ; auto. intros p Hact_eq. rewrite Hact_eq in H.
    case_eq p ; intros m Hp_eq ; rewrite Hp_eq in H ; inversion H.
  Qed.

  Definition P2P : IOADef ActionPool :=
    mkIOADef
      (fun act : ActionPool =>
        match Interface act with
         | Some (P2PRecv _) => Output
         | Some (P2PSend _) => Input
         | _ => Unused
        end)
      (fun st : P2PState => st = P2PState_empty_set)
      (fun (st : P2PState) (act : ActionPool) (st' : P2PState) =>
         match Interface act with
           | Some (P2PRecv m) => forall m' : Message, st m' = P2PState_add st' m m'
           | Some (P2PSend m) => forall m' : Message, st' m' = P2PState_add st m m'
           | _ => False
         end)
      P2PUnusedActionLemma
  .

  Definition P2P_get_next_state (st : P2PState) (act : ActionPool) :=
     match Interface act with
           | Some (P2PRecv m) => P2PState_sub st m
           | Some (P2PSend m) => P2PState_add st m
           | _ => st
     end.

  Lemma P2PTransision_dec :
    forall (st : P2PState) (act : ActionPool) (st' : P2PState), {Transition P2P st act st'}+{~Transition P2P st act st'}.
  Proof.
    intros st act st'.
    case_eq (Interface act).
    + intros p HactEq. simpl. rewrite HactEq. case_eq p ; auto with arith.
    + intro HactEq. simpl. rewrite HactEq. auto.
  Qed.

  Open Scope ltl_scope.
  Lemma P2P_only_recv_decrease :
    forall (st : P2PState) (act : ActionPool) (st' : P2PState) (m : Message),
      Transition P2P st act st' -> st m = (st' m) + 1 -> Interface act = Some(P2PRecv m).
  Proof.
    intros.
    simpl_Transition.
    + specialize H with m. cbv [P2PState_add] in H. simpl_match.
      rewrite n2 ; auto.
      lia.
    + specialize H with m. cbv [P2PState_add] in H. simpl_match ; lia.
    + contradiction.
  Qed.

  Lemma P2P_not_recv_enabled_is_0 :
    forall (st : P2PState) (act : ActionPool) (m : Message),
      Interface act = Some (P2PRecv m) -> (forall (st' : P2PState), ~Transition P2P st act st') -> st m = 0.
  Proof.
    intros.
    case_eq (st m =? 0) ; intro Heq ; simpl_arith_bool ; auto.
    specialize H0 with (P2P_get_next_state st act).
    destruct H0. cbv [P2P_get_next_state P2PState_sub P2PState_add st']. rewrite H.
    simpl_Transition ; intros ; cbv [P2PState_sub P2PState_add st'] ; inversion H ;
      repeat simpl_match ; rewrite n2 in * || idtac ;  lia.
  Qed.

  Lemma P2P_recv_enabled_is_non_0 :
    forall (st : P2PState) (act : ActionPool) (m : Message),
      Interface act = Some (P2PRecv m) -> (exists (st' : P2PState), Transition P2P st act st') -> st m > 0.
  Proof.
    intros.
    destruct H0.
    case_eq (0 <? st m) ; intro ; simpl_arith_bool. lia.
    simpl_Transition ; inversion H.
    specialize H0 with m. cbv [P2PState_add] in H0. simpl_match. lia. contradiction.
  Qed.

  Lemma P2P_zero_then_not_recv :
    forall (st : P2PState) (act : ActionPool) (st' : P2PState) (m : Message),
      st m = 0 -> Interface act = Some (P2PRecv m) -> ~ Transition P2P st act st'.
  Proof.
    intros.
    intro. simpl_Transition ; inversion H0.
    specialize H1 with m. cbv [P2PState_add] in H1.
    simpl_match ; lia || auto.
  Qed.

  Lemma P2P_only_send_increase :
    forall (st : P2PState) (act : ActionPool) (st' : P2PState) (m : Message),
      Transition P2P st act st' -> st' m = (st m) + 1 -> Interface act = Some(P2PSend m).
  Proof.
    intros. simpl_Transition.
    + specialize H with m. cbv [P2PState_add] in H. simpl_match ; lia.
    + specialize H with m. cbv [P2PState_add] in H. simpl_match ; lia || rewrite n2 ; auto.
    + contradiction.
  Qed.

  Lemma P2P_send_then_non_zero :
     forall (st : P2PState) (act : ActionPool) (st' : P2PState) (m : Message),
      Transition P2P st act st' -> Interface act = Some (P2PSend m) -> st' m > 0.
  Proof.
    intros.
    simpl_Transition ; cbv [P2PState_add] in H0 ; inversion H0. specialize H with m ; cbv [P2PState_add] in H ; simpl_match ; lia || contradiction.
  Qed.

  Lemma P2P_get_next_state_is_transition :
    forall (st : P2PState) (act : ActionPool), (exists st' : P2PState, Transition P2P st act st') -> Transition P2P st act (P2P_get_next_state st act).
  Proof.
    intros.
    simpl_Transition ; intros.
    + cbv [P2P_get_next_state P2PState_add P2PState_sub]. rewrite H0. simpl_match ; auto.
      apply P2P_recv_enabled_is_non_0 with st act n1 in H. cbv [P2P_get_next_state P2PState_add P2PState_sub]. rewrite n2 in H. lia.
      auto.
    + cbv [P2P_get_next_state P2PState_add P2PState_sub]. rewrite H0. simpl_match ; auto.
    + destruct H. simpl_Transition ; inversion H0.
  Qed.

  Lemma P2P_non_zero_recv :
    forall (e : ExecFragmentType (ActionPool := ActionPool)) (i : nat) (m : Message),
      FairFragment e ->
      ExecFragment e ->
      e $ i |= N (fun s => (st ActionPool P2P s) m > 0) ->
      e $ i |= F (N (fun s => exists act, opt_act ActionPool P2P s = Some act /\  Interface act = Some(P2PRecv m))).
  Proof.
    intros e i m H HexecFragment H0.
    assert (exists a : ActionPool, Interface a = Some(P2PRecv m)). auto.
    destruct H1.
    destruct_fair_exec.
    - destruct Hineq. exists x0. intuition. hnf in H2. hnf. exists x. rewrite H2. auto.
    - intros i x0. intros H H0 H2. intro Hinduction. assert (x0 = i). lia. subst x0.
      destruct Hinduction. destruct H4. unfold ltl_now, ltl_apply in H4, H2.
      unfold Transition, P2P in H4. simpl in H4. rewrite H1 in H4.
      destruct (e i). simpl in *. clear H0.
      specialize H4 with
        (P2PState_sub st m).
      contradict H4. intro.
      unfold P2PState_add, P2PState_sub.
      simpl_match ; (subst m ; lia) || auto.
    - intros i x0. intros H H0 H2. intro Hinduction. hnf in H2.
      specialize IHn with i (x0 - 1). hnf in HexecFragment. specialize HexecFragment with (x0 - 1).
      unfold ltl_now in IHn.
        case_eq (opt_act ActionPool P2P (e (x0 - 1))) ;
          [intro act | idtac] ; intro Hopt ; cycle 1.
        destruct (e (x0 -1)) ; simpl in *. rewrite Hopt in is_well_formed.
        subst st'. apply IHn ; auto. lia. split. lia. split.
        assert (Htmp : x0 - 1 + 1 = x0) by lia. rewrite Htmp in HexecFragment. clear Htmp.
        unfold ltl_now in Hinduction.
        destruct (e x0). subst st. simpl in *. apply Hinduction. auto.
        assert ({Interface act = Some (P2PRecv m)}+{~Interface act = Some (P2PRecv m)}).
        decide equality. decide equality.
        destruct H3.
        + exists (x0 - 1). intuition. lia. hnf. exists act. auto.
        + intuition.
          pose proof H1 as Heq_x.
          apply P2P_not_recv_enabled_is_0 with (IOA.st ActionPool P2P (e x0)) x m in H1.
          hnf in HexecFragment. assert (He : x0 - 1 + 1 = x0). lia. rewrite He in HexecFragment. clear He.
          rewrite <- HexecFragment in H1. destruct (e (x0 - 1)) eqn: Heq_e ; simpl in *.
          apply IHn ; auto ; clear IHn. lia. intuition. lia.
          clear Heq_e. rewrite Hopt in is_well_formed.
          rewrite Heq_x in H4.
          specialize H4 with m.
          induction (Interface act).
          induction a ; specialize is_well_formed with m. rewrite is_well_formed in H4.
          unfold P2PState_add in H4.
          simpl_match ; intros. subst m0. contradiction.
          rewrite H1 in H4. simpl_match.
          lia. contradiction.
          rewrite is_well_formed in H1. unfold P2PState_add in H1.
          rewrite H4 in H1. move H1 at bottom.
          simpl_match. lia. unfold P2PState_add in H1. simpl_match ; discriminate || lia || auto.
          auto.
          auto.
  Qed.

  Lemma P2P_all_messages_arrives :
    forall e : ExecFragmentType (ActionPool := ActionPool),
      Exec e -> FairFragment e ->
      forall m : Message,
        e $ 0 |= G (N (fun s => exists act, opt_act ActionPool P2P s = Some act /\
                                      Interface act = Some(P2PSend m)) -->
                    F (N (fun s => exists act, opt_act ActionPool P2P s = Some act /\
                                         Interface act = Some(P2PRecv m))) ).
    Proof.
      intros e Hexec Hfair m. intros j Hjgt0.

      destruct Hexec. intro.
      assert (
          e $ (j+1) |= F (N (fun s => exists act, opt_act ActionPool P2P s = Some act /\  Interface act = Some(P2PRecv m)))
        ). apply P2P_non_zero_recv ; auto.
      hnf in H1. destruct (e j) eqn: Heq. simpl in *.
      assert (st' m > 0). destruct H1 as [act H1].
      apply P2P_send_then_non_zero with st act ; auto.
      hnf in H ; specialize H with j. rewrite Heq in H. simpl in H. subst st'.
      hnf. destruct H1. subst opt_act. auto.
      destruct H1. auto.
      unfold ltl_now, ltl_apply.
      hnf in H ; specialize H with j. rewrite Heq in H. simpl in H. subst st'.
      auto.
      destruct H2. exists x.
      destruct H2. destruct H3.
      split ; auto. lia.
  Qed.
End P2P.
