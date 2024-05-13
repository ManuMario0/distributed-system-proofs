Require Import common.IOA.
Require Import common.LTL.
Require Import P2P.P2P.
Require Import common.tactic.
Require Import reliable_broadcast.definitions.
Require Import Lia.
Require Import Arith.

Set Implicit Arguments.

Section Normal.
  Definition Process_other_type := {n : nat | n < count /\ n > 0}.

  Inductive BrachaRBComposeType : Set :=
    | BrachaRBLeader_T : BrachaRBComposeType
    | BrachaRBOther_T : Process_other_type -> BrachaRBComposeType
    | BrachaRBNetwork_T : BrachaRBComposeType.

  Definition BrachaRBComposeType_eq (i j : BrachaRBComposeType) : Prop :=
    match (i, j) with
      | (BrachaRBOther_T p_i, BrachaRBOther_T p_j) => proj1_sig p_i = proj1_sig p_j
      | _ => i = j
    end.

  Definition BrachaRBRef (f : nat) (n : BrachaRBComposeType) : IOADef BrachaRBAction :=
    match n with
      | BrachaRBLeader_T => BrachaRBLeader f
      | BrachaRBOther_T p => BrachaRBOther f (proj1_sig p)
      | BrachaRBNetwork_T => P2PNetwork
    end.

  Ltac decompose_BrachaRBRef count i :=
    case_eq (i =? 0) ; intros ; case_eq (i <? count) ; intros ; case_eq (i =? count) ; intros.

  Lemma BrachaRBCompositionExtendedHyp (f : nat) : CompositionExtendedHyp BrachaRBComposeType_eq (BrachaRBRef f).
  Proof.
    hnf. intros. split ; intros.
    + case_eq act ; intros ; rewrite H2 in * ; simpl_ActionClass ; simpl in H1 ; inversion H1.
    + cbv [BrachaRBComposeType_eq] in H. case_eq act ; intros ; rewrite H1 in * ; simpl_ActionClass ; discriminate || idtac ;
      simpl_ActionClass ;
        (assert (proj1_sig n0 < count /\ proj1_sig n0 > 0) ; apply (proj2_sig n0) || idtac) || idtac ;
        lia || inversion H0.
  Qed.

  Definition BrachaRBFOutput (f : nat) (act : BrachaRBAction) : bool :=
    match act with
      | BrachaRBBroadcast _ => false
      | BrachaRBDeliver _ _ | BrachaRBP2PSend _ _ _  | BrachaRBP2PRecv _ _ _ => true
    end.

    Ltac _guess_compose_tac_from_action act interface out :=
      let other := fresh "other" in
      match act with
        | BrachaRBBroadcast _ =>
            match interface with
              | Input => pose BrachaRBLeader_T as out
              | Unused => pose BrachaRBNetwork_T as out
              | _ => idtac
            end
        | BrachaRBDeliver ?p _ =>
            match interface with
              | Output =>
                  case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
                  [
                    pose BrachaRBLeader_T as out |
                    create_sig Process_other_type (proj1_sig p) other ;
                    [
                      idtac |
                      pose (BrachaRBOther_T other) as out
                    ]
                  ]
              | Unused => pose BrachaRBNetwork_T as out
              | Input => idtac
            end
        | BrachaRBP2PRecv ?p ?q _ =>
            match interface with
              | Output => pose BrachaRBNetwork_T as out
              | Input =>
                  case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
                  [
                    pose BrachaRBLeader_T as out |
                    create_sig Process_other_type (proj1_sig p) other ;
                    [
                      idtac |
                      pose (BrachaRBOther_T other) as out
                    ]
                  ]
               | Unused =>
                   match count with
                     | 0 => idtac
                     | S _ =>
                         case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
                         [
                           create_sig Process_other_type 1 other ;
                           [
                             idtac |
                             pose (BrachaRBOther_T other) as out
                           ] |
                           pose BrachaRBLeader_T as out
                         ]
                    end
              end
        | BrachaRBP2PSend ?p ?q _ =>
            match interface with
              | Input => pose BrachaRBNetwork_T as out
              | Output =>
                  case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
                  [
                    pose BrachaRBLeader_T as out |
                    create_sig Process_other_type (proj1_sig p) other ;
                    [
                      idtac |
                      pose (BrachaRBOther_T other) as out
                    ]
                  ]
               | Unused =>
                   case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
                   [
                     create_sig Process_other_type 1 other ;
                     [
                       idtac |
                       pose (BrachaRBOther_T other) as out
                     ] |
                     pose BrachaRBLeader_T as out
                   ]
              end
      end.

    Ltac guess_compose_type_from_action_class :=
      let out := fresh "out" in
      match goal with
        | [|- context [ActionClass _ ?act = ?interface]] =>
            _guess_compose_tac_from_action act interface out ;
            (exists out ; simpl_ActionClass) || idtac
        | [H : context [ActionClass _ ?act = ?interface] |- _] =>
            match interface with
              | Input =>
                  _guess_compose_tac_from_action act Unused out ;
                  (specialize H with out ; simpl_ActionClass) || idtac
              | Output =>
                  _guess_compose_tac_from_action act Unused out ;
                  (specialize H with out ; simpl_ActionClass) || idtac
              | Unused =>
                  (_guess_compose_tac_from_action act Output out ;
                  (specialize H with out ; simpl_ActionClass) || idtac) ||
                  (_guess_compose_tac_from_action act Input out ;
                  (specialize H with out ; simpl_ActionClass) || idtac)
            end
      end.

  Lemma BrachaRBFOutputSpec (f : nat) :
    OutputSpec (BrachaRBRef f) (BrachaRBFOutput f).
  Proof.
    hnf. intro. split ; intro.
    + case_eq act ; intros ; rewrite H0 in H ; simpl in H ; clear H0 ; inversion H ;
      guess_compose_type_from_action_class ; lia || (split ; apply proj2_sig || lia).
    + case_eq act ; intros ; rewrite H0 in * ; simpl ; destruct H ;
        simpl_ActionClass ; inversion H ; destruct n0 ; simpl in * ; lia.
  Qed.

  Definition BrachaRBFInput (f : nat) (act : BrachaRBAction) : bool :=
    match act with
      | BrachaRBBroadcast _ | BrachaRBP2PSend _ _ _ | BrachaRBP2PRecv _ _ _ => true
      | BrachaRBDeliver _ _ => false
    end.

  Lemma BrachaRBFInputSpec (f : nat) :
    InputSpec (BrachaRBRef f) (BrachaRBFInput f).
  Proof.
    hnf. intro. split ; intro.
    + case_eq act ; intros ; rewrite H0 in H ; clear H0 ; simpl in H ; inversion H ;
      guess_compose_type_from_action_class ; lia || (split ; apply proj2_sig || lia).
    + case_eq act ; intros ; rewrite H0 in * ; simpl ; destruct H ;
        simpl_ActionClass ; inversion H ; destruct n0 ; simpl in * ; lia.
  Qed.

  Definition BrachaRBFUnused (f : nat) (act : BrachaRBAction) : bool :=
    false.

  Lemma BrachaRBFUnusedSpec (f : nat) :
    UnusedSpec (BrachaRBRef f) (BrachaRBFUnused f).
  Proof.
    hnf. intro. split ; intro.
    + case_eq act ; intros ; rewrite H0 in H ; simpl in H ; inversion H ;
      simpl_ActionClass ; destruct n0 || idtac ; simpl in * ; lia || inversion H.
    + case_eq act ; intros ; rewrite H0 in * ; simpl ; repeat simpl_arith_bool ;
      guess_compose_type_from_action_class ; inversion H || (split ; apply proj2_sig || lia).
  Qed.

  Definition BrachaRB (f : nat) : IOADef BrachaRBAction :=
    CompositionExtended
      BrachaRBLeader_T
      (BrachaRBCompositionExtendedHyp f)
      (BrachaRBFOutputSpec f)
      (BrachaRBFInputSpec f)
      (BrachaRBFUnusedSpec f)
    .

  Lemma BrachRB_first_action_broadcast (f : nat) :
    forall e : ExecFragmentType (ActionPool := BrachaRBAction),
      Exec e -> exists m : Message, act BrachaRBAction (BrachaRB 0) (e 0) = BrachaRBBroadcast m.
  Proof.
    intros. destruct H.
    case_eq (act BrachaRBAction (BrachaRB 0) (e 0)) ; intros.
    - exists m. auto.
    - hnf in H0, H.
      destruct (e 0).
      simpl in st, st'.
      simpl in H0, H1. rewrite H1 in is_well_formed.
      simpl in is_well_formed.
      guess_compose_type_from_action_class ;
        (intuition ;
         match goal with
         | [H : (_ -> _ /\ False) |- _] =>
            destruct H ; discriminate || contradiction
         end)
        ||  idtac.
      intuition ; specialize H0 with out ; hnf in H0 ; rewrite H0 in H6 ; simpl in H6.
      unfold BrachaRBLeaderTransition, BrachaRBLeader_compute_transition in H6. simpl in H6.
      simpl_match. lia. assert (None = Some (st' out)). apply H6. discriminate. inversion H8.
      split. apply proj2_sig. lia.
      intuition ; specialize H0 with out ; hnf in H0 ; rewrite H0 in H7 ; simpl in H7.
      unfold BrachaRBOtherTransition, BrachaRBOther_compute_transition in H7. simpl in H7.
      simpl_match. lia. assert (None = Some (st' out)). apply H7. discriminate. inversion H9.
    - simpl in H0. specialize H0 with BrachaRBNetwork_T.
      destruct (e 0). simpl in *.
      specialize is_well_formed with BrachaRBNetwork_T.
      intuition. clear H5.
      assert (Transition (BrachaRBRef 0 BrachaRBNetwork_T) (st BrachaRBNetwork_T) act (st' BrachaRBNetwork_T)). apply H4. rewrite H1. simpl. discriminate.
      rewrite H1 in H3. cbn [P2PNetwork BrachaRBRef CompositionExtended Transition] in H3.
      destruct p eqn : Heqp, p0 eqn : Heqp0.
      create_sig BrachaP2PCompositionType (x, x0) comp.
      specialize H3 with comp. specialize H0 with comp.
      destruct H3. destruct H6. rewrite H1 in *.
      assert (Transition (AutomatonRef (exist (fun n : nat * nat => let (p, q) := n in p < count /\ q < count) (x, x0) H5))
         (st BrachaRBNetwork_T (exist (fun n : nat * nat => let (p, q) := n in p < count /\ q < count) (x, x0) H5))
         (BrachaRBP2PRecv (exist (fun n : nat => n < count) x l) (exist (fun n : nat => n < count) x0 l0) i)
         (st' BrachaRBNetwork_T (exist (fun n : nat * nat => let (p, q) := n in p < count /\ q < count) (x, x0) H5))).
      apply H6. simpl. simpl_match ; simpl_match ; discriminate || auto. repeat simpl_arith_bool ; lia.
      assert (st BrachaRBNetwork_T (exist (fun n : nat * nat => let (p, q) := n in p < count /\ q < count) (x, x0) H5) i > 0).
      Print P2P_recv_enabled_is_non_0.
      apply P2P_recv_enabled_is_non_0 with InternMessage_dec BrachaRBAction (P2PInterface_f p p0) act.
      rewrite H1. simpl. simpl_match. auto. repeat simpl_arith_bool. rewrite Heqp in H9. simpl in H9. contradiction.
      rewrite Heqp0 in H9. simpl in H9. contradiction.
      exists ((st' BrachaRBNetwork_T (exist (fun n : nat * nat => let (p, q) := n in p < count /\ q < count) (x, x0) H5))).
      rewrite H1. rewrite Heqp, Heqp0. auto.
      assert (st BrachaRBNetwork_T (exist (fun n : nat * nat => let (p, q) := n in p < count /\ q < count) (x, x0) H5) i = P2PState_empty_set (Message:=InternMessage) i).
      cbv. unfold comp in H0. rewrite H0. auto. cbv [P2PState_empty_set] in H10. lia.
    - hnf in H0, H.
      destruct (e 0).
      simpl in st, st'.
      simpl in H0, H1. rewrite H1 in is_well_formed.
      simpl in is_well_formed.
      guess_compose_type_from_action_class  ;
        (intuition ;
         match goal with
         | [H : (_ -> _ /\ False) |- _] =>
            destruct H ; discriminate || contradiction
         end)
        ||  idtac.
      intuition ; specialize H0 with out ; hnf in H0 ; rewrite H0 in H6 ; simpl in H6.
      unfold BrachaRBLeaderTransition, BrachaRBLeader_compute_transition in H6. simpl in H6.
      simpl_match. repeat simpl_arith_bool.
      unfold BrachaRBBuffer_empty_set in H8. inversion H8.
      assert (None = Some (st' out)). apply H6. discriminate. inversion H5.
      inversion H8.
      split ; apply proj2_sig || lia.
      intuition ; specialize H0 with out ; hnf in H0 ; rewrite H0 in H7 ; simpl in H7.
      unfold BrachaRBOtherTransition, BrachaRBOther_compute_transition in H7. simpl in H7.
      simpl_match. repeat simpl_arith_bool.
      unfold BrachaRBBuffer_empty_set in H9. inversion H9.
      assert (None = Some (st' out)). apply H7. discriminate. inversion H9.
  Qed.
End Normal.
