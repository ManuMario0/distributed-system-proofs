Require Import common.IOA.
Require Import common.buffer.
Require Import common.tactic.
Require Import P2P.P2P.
Require Import Lia.
Require Import Arith.
Require Import MSets.

Module ReliableBroadcast (Message : OrderedType).
  Module Buffer := Make Message.

  Parameter NumProcess : nat.
  Parameter NumByzentine : nat.
  Parameter byzentine_limit : NumByzentine*3 <= NumProcess.

  Parameter Process : Set.
  Parameter Process_dec : forall p p' : Process, {p = p'}+{p <> p'}.

  Inductive InternMessage : Type :=
    | Init : Message.t -> InternMessage
    | Echo : Message.t -> InternMessage
    | Ready : Message.t -> InternMessage.

  Inductive BrachaRBAction : Type :=
    | BrachaRBBroadcast : Message.t -> BrachaRBAction
    | BrachaRBDeliver : Process -> Message.t -> BrachaRBAction
    | BrachaRBP2PRecv : Process -> Process -> InternMessage -> BrachaRBAction
    | BrachaRBP2PSend : Process -> Process -> InternMessage -> BrachaRBAction.

  Definition P2PInterface_f (n : Process) (m : Process) (act : BrachaRBAction) :
    option (P2PInterface InternMessage) :=
    match act with
      | BrachaRBP2PRecv i j message =>
          if (proj1_sig i =? proj1_sig n) && (proj1_sig j =? proj1_sig m) then Some (P2PRecv message) else None
      | BrachaRBP2PSend i j message =>
          if (proj1_sig i =? proj1_sig n) && (proj1_sig j =? proj1_sig m) then Some (P2PSend message) else None
      | _ => None
    end.











Require Import FunctionalExtensionality.

Parameter Message : Set.
Parameter Message_dec : forall m m' : Message, {m = m'}+{m <> m'}.
Parameter Message_forall_dec : forall P : Message -> Prop, (forall m : Message, {P m}+{~P m}) -> {forall m : Message, P m}+{~forall m : Message, P m}.

Parameter count : nat.
Parameter Hcount : count > 0.

Set Implicit Arguments.

Section RealiableBroadcast.
  Import Bool.
  Import Nat.

  Definition Process : Set := {n : nat | n < count}.

  Axiom process_proof_irrelevence :
    forall p q : Process, proj1_sig p = proj1_sig q -> p = q.

  Lemma Process_dec :
    forall p p' : Process, {p = p'}+{p <> p'}.
  Proof.
    intros.
    case_eq (proj1_sig p =? proj1_sig p') ; intro ;
    simpl_arith_bool. left. apply process_proof_irrelevence. auto.
    right. intro. subst p. contradiction.
  Qed.

  Definition process_zero : Process.
  create_sig Process 0 out.
  assert (count > 0) by apply Hcount. lia.
  apply out.
  Defined.

  Definition process_from_nat_and_prop (n : nat) (H : n < count) : Process.
    create_sig Process n out.
    apply out.
  Defined.

  Lemma forall_process_property_decidable :
  forall P : Process -> Prop,
    (forall p, {P p}+{~P p}) ->
    {forall p, P p}+{exists p, ~P p}.
  Proof.
    intros.
    assert (
        forall i : nat, {forall p, proj1_sig p < i -> P p}+{exists p, proj1_sig p < i /\ ~ P p}
      ).
    induction i.
    left. intros. lia.
    case_eq (count <=? i) ; intro ; simpl_arith_bool.
    - destruct IHi.
      left. intros. apply p. destruct p0. simpl in *. lia.
      right. destruct e. exists x. split. lia. apply H1.
    - destruct IHi.
      create_sig Process i out.
      destruct H with out.
      left. intros.
      case_eq (proj1_sig out =? proj1_sig p1) ; intro ; simpl_arith_bool.
      apply process_proof_irrelevence in H3. subst. auto.
      apply p. unfold out in H3. simpl in H3. lia.
      right. exists out. split. unfold out. simpl. lia. auto.
      right. destruct e. exists x. split. lia. apply H1.
    - specialize H0 with count.
      destruct H0.
      left. intro. apply p. destruct p0. simpl. auto.
      right. destruct e. exists x. apply H0.
  Qed.

  Inductive InternMessage : Set :=
    | Init : Message -> InternMessage
    | Echo : Message -> InternMessage
    | Ready : Message -> InternMessage.

  Lemma InternMessage_dec :
    forall m m' : InternMessage, {m = m'}+{m <> m'}.
  Proof.
    intros m m'.
    case m ; case m' ; intros m0 m'0 ; case (Message_dec m0 m'0) ; intro ; (rewrite e ; auto) || idtac ; right ; injection || discriminate ; auto.
  Qed.

  Definition InternMessage_dec_bool (m m' : InternMessage) : bool :=
    if InternMessage_dec m m' then true else false.

  Lemma InternMessage_dec_bool_true :
    forall m m' : InternMessage, InternMessage_dec_bool m m' = true -> m = m'.
  Proof.
    intros.
    unfold InternMessage_dec_bool in H.
    simpl_match. auto. inversion H.
  Qed.

  Lemma InternMessage_dec_bool_false :
    forall m m' : InternMessage, InternMessage_dec_bool m m' = false -> m <> m'.
  Proof.
    intros.
    unfold InternMessage_dec_bool in H.
    simpl_match. inversion H. auto.
  Qed.

  Inductive BrachaRBAction : Set :=
    | BrachaRBBroadcast : Message -> BrachaRBAction
    | BrachaRBDeliver : Process -> Message -> BrachaRBAction
    | BrachaRBP2PRecv : Process -> Process -> InternMessage -> BrachaRBAction
    | BrachaRBP2PSend : Process -> Process -> InternMessage -> BrachaRBAction.

  Lemma destruct_diff_BrachaRBBroadcast :
    forall m m' : Message,
      BrachaRBBroadcast m <> BrachaRBBroadcast m' -> m <> m'.
  Proof.
    intros.
    case (Message_dec m m') ; intro ; auto. subst. contradiction.
  Qed.

  Lemma destruct_diff_BrachaRBDeliver :
    forall m m' : Message, forall p p' : Process,
      BrachaRBDeliver p m <> BrachaRBDeliver p' m' -> m <> m' \/ p <> p'.
  Proof.
    intros.
    case (Message_dec m m') ; intro ; auto.
    case (Process_dec p p') ; intro ; auto. subst.
    contradiction.
  Qed.

  Lemma destruct_diff_BrachaRBP2PRecv :
    forall m m' : InternMessage, forall p p' : Process, forall q q' : Process,
      BrachaRBP2PRecv p q m <> BrachaRBP2PRecv p' q' m' -> m <> m' \/ p <> p' \/ q <> q'.
  Proof.
    intros.
    case (InternMessage_dec m m') ; intro ; auto.
    case (Process_dec p p') ; intro ; auto.
    case (Process_dec q q') ; intro ; auto. subst.
    contradiction.
  Qed.

  Lemma destruct_diff_BrachaRBP2PSend :
    forall m m' : InternMessage, forall p p' : Process, forall q q' : Process,
      BrachaRBP2PSend p q m <> BrachaRBP2PSend p' q' m' -> m <> m' \/ p <> p' \/ q <> q'.
  Proof.
    intros.
    case (InternMessage_dec m m') ; intro ; auto.
    case (Process_dec p p') ; intro ; auto.
    case (Process_dec q q') ; intro ; auto. subst.
    contradiction.
  Qed.

  Ltac destruct_BrachaRBAction_eq :=
    discriminate
      || (let H := fresh "H" in intro H ; inversion H ; clear H ; subst)
      || auto
  .

  Tactic Notation "destruct_brachaRBAction_eq" "in" ident(H) :=
    contradiction
    || apply destruct_diff_BrachaRBBroadcast in H
    || apply destruct_diff_BrachaRBDeliver in H
    || apply destruct_diff_BrachaRBP2PRecv in H
    || apply destruct_diff_BrachaRBP2PSend in H
    || (inversion H ; clear H ; subst)
  .

  Lemma BrachaRBAction_dec :
    forall act act' : BrachaRBAction, {act = act'}+{act <> act'}.
  Proof.
    induction act, act' ; (right ; discriminate) || auto.
    + destruct Message_dec with m m0. subst m. left. auto. right. intro. inversion H. contradiction.
    + case_eq (proj1_sig p =? proj1_sig p0) ; intro ; simpl_arith_bool.
      destruct Message_dec with m m0.
      left. apply process_proof_irrelevence in H. subst p0 m0. auto.
      right. intro. inversion H0. contradiction.
      right. intro. inversion H0. subst p0. contradiction.
    + destruct InternMessage_dec with i i0.
      case_eq (proj1_sig p =? proj1_sig p1) ; intro ; simpl_arith_bool.
      case_eq (proj1_sig p0 =? proj1_sig p2) ; intro ; simpl_arith_bool.
      left. apply process_proof_irrelevence in H, H0. subst i0 p1 p2. auto.
      right. intro. inversion H1. subst p0. contradiction.
      right. intro. inversion H0. subst p. contradiction.
      right. intro. inversion H. contradiction.
    + destruct InternMessage_dec with i i0.
      case_eq (proj1_sig p =? proj1_sig p1) ; intro ; simpl_arith_bool.
      case_eq (proj1_sig p0 =? proj1_sig p2) ; intro ; simpl_arith_bool.
      left. apply process_proof_irrelevence in H, H0. subst i0 p1 p2. auto.
      right. intro. inversion H1. subst p0. contradiction.
      right. intro. inversion H0. subst p. contradiction.
      right. intro. inversion H. contradiction.
  Qed.

  Lemma BrachaRBOptionAction_dec :
    forall act act' : option BrachaRBAction, {act = act'}+{act <> act'}.
  Proof.
    intros.
    case act, act' ; try (right ; discriminate).
    destruct BrachaRBAction_dec with b b0. subst. auto.
    right. intro. inversion H.  contradiction.
    auto.
  Qed.

  Definition P2PInterface_f (n : Process) (m : Process) (act : BrachaRBAction) :
    option (P2PInterface InternMessage) :=
    match act with
      | BrachaRBP2PRecv i j message => if (proj1_sig i =? proj1_sig n) && (proj1_sig j =? proj1_sig m) then Some (P2PRecv message) else None
      | BrachaRBP2PSend i j message => if (proj1_sig i =? proj1_sig n) && (proj1_sig j =? proj1_sig m) then Some (P2PSend message) else None
      | _ => None
    end.

  Definition BrachaP2PCompositionType : Set := {n : nat*nat | let (p, q) := n in (p < count) /\ (q < count)}.

  Lemma zero_is_BrachaP2PCompositionType : let (p, q) := (0, 0) in (p < count) /\ (q < count).
  Proof.
    simpl ; split ; apply Hcount.
  Qed.

  Definition BrachaP2PCompositionType_eq (a b : BrachaP2PCompositionType) : Prop := proj1_sig a = proj1_sig b.

  Lemma split_composition_type_left :
    forall i : BrachaP2PCompositionType, fst (proj1_sig i) < count.
  Proof.
    intro. destruct i. simpl. destruct x. simpl. destruct y. auto.
  Qed.

  Lemma split_composition_type_right :
    forall i : BrachaP2PCompositionType, snd (proj1_sig i) < count.
  Proof.
    intro. destruct i. simpl. destruct x. simpl. destruct y. auto.
  Qed.

  Definition AutomatonRef (i : BrachaP2PCompositionType) : IOADef BrachaRBAction :=
    P2P InternMessage_dec (
        P2PInterface_f
          (exist (fun n : nat => n < count) (fst (proj1_sig i)) (split_composition_type_left i))
          (exist (fun n : nat => n < count) (snd (proj1_sig i)) (split_composition_type_right i))
      ).

  Definition zero_of_BrachaP2PCompositionType : BrachaP2PCompositionType :=
    exist (fun i : nat*nat => let (p, q) := i in (p < count) /\ (q < count)) (0, 0) zero_is_BrachaP2PCompositionType.

  Ltac automatonref_simpl term :=
    cbv head delta [AutomatonRef] beta in term ; simpl in term.

  Lemma P2PCompositionHyp : CompositionExtendedHyp BrachaP2PCompositionType_eq AutomatonRef.
  Proof.
    hnf.
    intros i j Hdiff.
    split ; intros.
    + case_eq act ; intros ; rewrite H1 in H0 ; simpl_ActionClass ; destruct (proj1_sig i) ; simpl in H0 ; inversion H0 ; simpl_match ;
        (case_eq n2 ; intros ; rewrite H4 in H3 ; inversion H3) || inversion H3.
    + repeat simpl_ActionClass ; discriminate || idtac ;
      case_eq act ; intros ; rewrite H4 in * ; clear H5 || idtac ; simpl in * ; repeat simpl_match ; repeat simpl_arith_bool ; inversion H0 ; inversion H2 ; inversion H ;
      cbv [BrachaP2PCompositionType_eq] in Hdiff ;
      destruct (proj1_sig j) eqn: Hdestruct_j || idtac ; destruct (proj1_sig i) eqn: Hdestruct_i || idtac ; simpl in * ;
      (rewrite H5 in H6 ; rewrite H8 in H7 ; rewrite H6, H7 in Hdiff) || idtac ; auto.
  Qed.

  Definition NetworkFOutput (act : BrachaRBAction) : bool :=
    match act with
      | BrachaRBBroadcast _ | BrachaRBDeliver _ _ | BrachaRBP2PSend _ _ _ => false
      | BrachaRBP2PRecv p q _ => true
    end.

  Lemma NetworkFOutputSpec :
    OutputSpec AutomatonRef NetworkFOutput.
  Proof.
    hnf. intro. split ; intro.
    + case_eq act ; intros ; rewrite H0 in H ; simpl in H ; (inversion H ; fail) || idtac ; repeat simpl_arith_bool.
      destruct p. destruct p0.
      create_sig BrachaP2PCompositionType (x, x0) comp.
      exists comp.
      simpl_ActionClass ; inversion H2 ; lia.
    + destruct H.
      case_eq act ; intros ; rewrite H0 in * ; clear H0 ; auto ; simpl_ActionClass ; inversion H ; inversion H0.
  Qed.

  Definition NetworkFInput (act : BrachaRBAction) : bool :=
    match act with
      | BrachaRBBroadcast _ | BrachaRBDeliver _ _ | BrachaRBP2PRecv _ _ _ => false
      | BrachaRBP2PSend p q _ => true
    end.

  Lemma NetworkFInputSpec :
    InputSpec AutomatonRef NetworkFInput.
  Proof.
    hnf. intro. split ; intro.
    + case_eq act ; intros ; rewrite H0 in H ; simpl in H ; (inversion H ; fail) || idtac ; repeat simpl_arith_bool.
      destruct p. destruct p0.
      create_sig BrachaP2PCompositionType (x, x0) comp.
      exists comp.
      simpl_ActionClass ; inversion H2 ; lia.
    + destruct H.
      case_eq act ; intros ; rewrite H0 in * ; clear H0 ; auto ; simpl_ActionClass ; inversion H ; inversion H0.
  Qed.

  Definition NetworkFUnused (act : BrachaRBAction) : bool :=
    match act with
      | BrachaRBBroadcast _ | BrachaRBDeliver _ _ => true
      | BrachaRBP2PSend p q _ | BrachaRBP2PRecv p q _ => false
    end.

  Lemma NetworkFUnusedSpec :
    UnusedSpec AutomatonRef NetworkFUnused.
  Proof.
    hnf. intro. split ; intro.
    + case_eq act ; intros ; rewrite H0 in H ; simpl in H ; (inversion H ; fail) || idtac ; repeat simpl_arith_bool ; simpl_ActionClass ; intro ;
      simpl_match ; (injection H2 ; intro) || idtac ; apply negb_true_iff in H ; repeat simpl_arith_bool ; destruct i0 ; simpl in * ; rewrite H4 in y ; lia || inversion H2.
    + case_eq act ; intros ; rewrite H0 in * ; clear H0 ; auto.
      destruct p, p0.
      create_sig BrachaP2PCompositionType (x, x0) comp.
      specialize H with comp.
      simpl_ActionClass ; inversion H ; inversion H1.
      destruct p, p0.
      create_sig BrachaP2PCompositionType (x, x0) comp.
      specialize H with comp.
      simpl_ActionClass ; inversion H ; inversion H1.
  Qed.

  Definition P2PNetwork : IOADef BrachaRBAction :=
    CompositionExtended zero_of_BrachaP2PCompositionType P2PCompositionHyp NetworkFOutputSpec NetworkFInputSpec NetworkFUnusedSpec.

  Theorem NoIntern :
    forall act : BrachaRBAction, ActionClass P2PNetwork act <> Intern.
  Proof.
    intro. intuition.
    simpl in H. case_eq act ; intros ; rewrite H0 in * ; simpl in H ; inversion H ;
    case_eq ((p <? count) && (p0 <? count)) ; intro ; rewrite H1 in H ; inversion H.
  Qed.

  Definition Packet : Set :=
    Process * InternMessage.

  Lemma packet_dec :
    forall p p' : Packet, {p = p'}+{p <> p'}.
  Proof.
    intros.
    destruct p, p'.
    destruct InternMessage_dec with i i0.
    destruct Process_dec with p p0.
    subst. left. auto. right. intro. inversion H. subst. contradiction.
    right. intro. inversion H. subst. contradiction.
  Qed.
(*)
  Definition BrachaRBBuffer :=
    Packet -> bool.

  Definition BrachaRBBuffer_empty_set : BrachaRBBuffer :=
    fun m : Packet => false.

  Definition BrachaRBBuffer_add (st : BrachaRBBuffer) (s : {n : nat | n < count}) (m : InternMessage) : BrachaRBBuffer :=
    fun m0 : Packet  => if InternMessage_dec_bool m (snd m0) && (proj1_sig (fst m0) =? proj1_sig s) then true else st m0.

  Definition BrachaRBBuffer_sub (st : BrachaRBBuffer) (s : {n : nat | n < count}) (m : InternMessage) : BrachaRBBuffer :=
    fun m0 : Packet => if InternMessage_dec_bool m (snd m0) && (proj1_sig (fst m0) =? proj1_sig s) then false else st m0.

  Lemma add_existing_element_invariant :
    forall buff : BrachaRBBuffer, forall (s : {n : nat | n < count}) (m : InternMessage),
      buff (s, m) = true -> BrachaRBBuffer_add buff s m = buff.
  Proof.
    intros. apply functional_extensionality_dep. intro p.
    unfold BrachaRBBuffer_add, InternMessage_dec_bool.
    case_eq (InternMessage_dec m (snd p)) ; intros ; auto.
    simpl_match ; repeat simpl_arith_bool.
    subst m. apply process_proof_irrelevence in H2.
    subst s. destruct p. auto. inversion H1. auto.
  Qed.

  Lemma add_element_invariant_when_true :
    forall buff : BrachaRBBuffer, forall (s : {n : nat | n < count}) (m : InternMessage),
      buff (s, m) = true -> forall (s' : {n : nat | n < count}) (m' : InternMessage),
        BrachaRBBuffer_add buff s' m' (s, m) = true.
  Proof.
    intros.
    unfold BrachaRBBuffer_add, InternMessage_dec_bool.
    case_eq (InternMessage_dec m (snd (s, m))) ; intros ; auto.
    case_eq (InternMessage_dec m' (snd (s, m))) ; intros ; auto.
    simpl_match ; repeat simpl_arith_bool ; auto.
  Qed.

  Lemma add_element_then_true :
    forall buff : BrachaRBBuffer, forall (s : {n : nat | n < count}) (m : InternMessage),
      BrachaRBBuffer_add buff s m (s, m) = true.
  Proof.
    intros.
    unfold BrachaRBBuffer_add, InternMessage_dec_bool.
    case_eq (InternMessage_dec m (snd (s, m))) ; intros ; auto.
    simpl_match ; repeat simpl_arith_bool ; auto.
    inversion H0.
  Qed.

  Lemma sub_element_then_else_unchanged :
    forall buff : BrachaRBBuffer, forall (s : {n : nat | n < count}) (m : InternMessage), forall p : Packet,
      (s <> fst p \/ m <> snd p) ->
      BrachaRBBuffer_sub buff s m p = buff p.
  Proof.
    intros.
    destruct H ;
    unfold BrachaRBBuffer_sub, InternMessage_dec_bool ;
    case (InternMessage_dec m (snd p)) ; intro ; auto ;
    simpl_match ; repeat simpl_arith_bool ; auto ;
    apply process_proof_irrelevence in H1 ; subst ; contradiction.
  Qed.

  Lemma sub_not_existing_element_invariant :
    forall buff : BrachaRBBuffer, forall (s : {n : nat | n < count}) (m : InternMessage),
      buff (s, m) = false -> BrachaRBBuffer_sub buff s m = buff.
  Proof.
    intros. apply functional_extensionality_dep. intro.
    unfold BrachaRBBuffer_sub, InternMessage_dec_bool.
    case_eq (InternMessage_dec m (snd x)) ; intros ; auto.
    simpl_match ; repeat simpl_arith_bool ; auto.
    subst m. apply process_proof_irrelevence in H2.
    subst s. destruct x. auto.
  Qed.

  Lemma sub_element_then_false :
    forall buff : BrachaRBBuffer, forall (s : {n : nat | n < count}) (m : InternMessage),
      BrachaRBBuffer_sub buff s m (s, m) = false.
  Proof.
    intros.
    unfold BrachaRBBuffer_sub, InternMessage_dec_bool.
    case_eq (InternMessage_dec m (snd (s, m))) ; intros ; try contradiction.
    simpl_match ; repeat simpl_arith_bool ; auto.
    inversion H0. contradiction.
  Qed.

  Lemma sub_element_invariant_when_false :
    forall buff : BrachaRBBuffer, forall (s : {n : nat | n < count}) (m : InternMessage),
      buff (s, m) = false -> forall (s' : {n : nat | n < count}) (m' : InternMessage),
        BrachaRBBuffer_sub buff s' m' (s, m) = false.
  Proof.
    intros.
    unfold BrachaRBBuffer_sub, InternMessage_dec_bool.
    case_eq (InternMessage_dec m' (snd (s, m))) ; intros ; auto.
    simpl_match ; repeat simpl_arith_bool ; auto.
  Qed.

  Lemma add_element_then_else_unchanged :
    forall buff : BrachaRBBuffer, forall (s : {n : nat | n < count}) (m : InternMessage), forall p : Packet,
      (s <> fst p \/ m <> snd p) ->
      BrachaRBBuffer_add buff s m p = buff p.
  Proof.
    intros.
    destruct H ;
    unfold BrachaRBBuffer_add, InternMessage_dec_bool ;
    case (InternMessage_dec m (snd p)) ; intro ; auto ;
    simpl_match ; repeat simpl_arith_bool ; auto ;
    apply process_proof_irrelevence in H1 ; subst ; contradiction.
  Qed.

  Lemma empty_buffer_then_false :
    forall (s : {n : nat | n < count}) (m : InternMessage),
      BrachaRBBuffer_empty_set (s, m) = false.
  Proof.
    auto.
  Qed.

  Lemma sub_add_when_false_is_invarient :
     forall buff : BrachaRBBuffer, forall (s : {n : nat | n < count}) (m : InternMessage),
       buff (s, m) = false ->
       forall p, BrachaRBBuffer_sub (BrachaRBBuffer_add buff s m) s m p = buff p.
  Proof.
    intros.
    destruct p.
    case (InternMessage_dec m i) ; intro ;
    case (Process_dec s s0) ; intro ; subst.
    rewrite sub_element_then_false. auto.
    rewrite sub_element_then_else_unchanged ; auto.
    rewrite add_element_then_else_unchanged ; auto.
    rewrite sub_element_then_else_unchanged ; auto.
    rewrite add_element_then_else_unchanged ; auto.
    rewrite sub_element_then_else_unchanged ; auto.
    rewrite add_element_then_else_unchanged ; auto.
  Qed.

  Lemma add_sub_when_true_is_invarient :
    forall buff : BrachaRBBuffer, forall (s : {n : nat | n < count}) (m : InternMessage),
       buff (s, m) = true ->
       forall p, BrachaRBBuffer_add (BrachaRBBuffer_sub buff s m) s m p = buff p.
  Proof.
    intros.
    destruct p.
    case (InternMessage_dec m i) ; intro ;
    case (Process_dec s s0) ; intro ; subst.
    rewrite add_element_then_true. auto.
    rewrite add_element_then_else_unchanged ; auto.
    rewrite sub_element_then_else_unchanged ; auto.
    rewrite add_element_then_else_unchanged ; auto.
    rewrite sub_element_then_else_unchanged ; auto.
    rewrite add_element_then_else_unchanged ; auto.
    rewrite sub_element_then_else_unchanged ; auto.
  Qed.

  Ltac buffer_solver :=
    intros ;
    subst ; simpl in * ;
    match goal with
      | p : Packet |- _ => destruct p
      (* boolean goal solving *)
      | H : true = false |- _ => inversion H
      | H : false = true |- _ => inversion H
      (* empty buffer reduction *)
      | |- context [BrachaRBBuffer_empty_set _] =>
          rewrite empty_buffer_then_false
      | H : context [BrachaRBBuffer_empty_set _] |- _ =>
          rewrite empty_buffer_then_false in H
      (* repetition reduction *)
      | |- context [BrachaRBBuffer_add _ ?s ?t (?s, ?t)] =>
          rewrite add_element_then_true
      | |- context [BrachaRBBuffer_sub _ ?s ?t (?s, ?t)] =>
          rewrite sub_element_then_false
      | H : context [BrachaRBBuffer_add _ ?s ?t (?s, ?t)] |- _ =>
          rewrite add_element_then_true in H
      | H : context [BrachaRBBuffer_sub _ ?s ?t (?s, ?t)] |- _ =>
          rewrite sub_element_then_false in H
      (* buffer property reduction *)
      | _ : context [?buff (?s, ?m) = true] |- context [BrachaRBBuffer_add ?buff ?s ?m _] =>
          rewrite add_existing_element_invariant
      | _ : context [?buff (?s, ?m) = true] |- context [BrachaRBBuffer_add ?buff _ _ (?s, ?m)] =>
          rewrite add_element_invariant_when_true
      | _ : context [?buff (?s, ?m) = false] |- context [BrachaRBBuffer_sub ?buff ?s ?m _] =>
          rewrite sub_not_existing_element_invariant
      | _ : context [?buff (?s, ?m) = false] |- context [BrachaRBBuffer_sub ?buff _ _ (?s, ?m)] =>
          rewrite sub_element_invariant_when_false
      | _ : context [?buff (?s, ?m) = true], H : context [BrachaRBBuffer_add ?buff ?s ?m _] |- _ =>
          rewrite add_existing_element_invariant in H
      | _ : context [?buff (?s, ?m) = true], H : context [BrachaRBBuffer_add ?buff _ _ (?s, ?m)] |- _ =>
          rewrite add_element_invariant_when_true in H
      | _ : context [?buff (?s, ?m) = false], H : context [BrachaRBBuffer_sub ?buff ?s ?m _] |- _ =>
          rewrite sub_not_existing_element_invariant in H
      | _ : context [?buff (?s, ?m) = false], H : context [BrachaRBBuffer_sub ?buff _ _ (?s, ?m)] |- _ =>
          rewrite sub_element_invariant_when_false in H
      (* add and sub alternance reduction *)
      | _ : context [?buff (?s, ?m) = false] |-
          context [BrachaRBBuffer_sub (BrachaRBBuffer_add ?buff ?s ?t) ?s ?t _] =>
          rewrite sub_add_when_false_is_invarient
      | _ : context [?buff (?s, ?m) = true] |-
          context [BrachaRBBuffer_add (BrachaRBBuffer_sub ?buff ?s ?t) ?s ?t _] =>
          rewrite add_sub_when_true_is_invarient
      | _ : context [?buff (?s, ?m) = false],
          H : context [BrachaRBBuffer_sub (BrachaRBBuffer_add ?buff ?s ?t) ?s ?t _] |- _ =>
          rewrite sub_add_when_false_is_invarient in H
      | _ : context [?buff (?s, ?m) = true],
          H : context [BrachaRBBuffer_add (BrachaRBBuffer_sub ?buff ?s ?t) ?s ?t _] |- _ =>
          rewrite add_sub_when_true_is_invarient in H
      (* elements property reduction *)
      | _ : context [?s <> ?s'] |- context [BrachaRBBuffer_add _ ?s ?t (?s', ?t')] =>
          rewrite add_element_then_else_unchanged
      | _ : context [?t <> ?t'] |- context [BrachaRBBuffer_add _ ?s ?t (?s', ?t')] =>
          rewrite add_element_then_else_unchanged
      | _ : context [?s <> ?s'] |- context [BrachaRBBuffer_sub _ ?s ?t (?s', ?t')] =>
          rewrite sub_element_then_else_unchanged
      | _ : context [?t <> ?t'] |- context [BrachaRBBuffer_sub _ ?s ?t (?s', ?t')] =>
          rewrite sub_element_then_else_unchanged
      | _ : context [?s <> ?s'], H : context [BrachaRBBuffer_add _ ?s ?t (?s', ?t')] |- _ =>
          rewrite add_element_then_else_unchanged in H
      | _ : context [?t <> ?t'], H : context [BrachaRBBuffer_add _ ?s ?t (?s', ?t')] |- _ =>
          rewrite add_element_then_else_unchanged in H
      | _ : context [?s <> ?s'], H : context [BrachaRBBuffer_sub _ ?s ?t (?s', ?t')] |- _ =>
          rewrite sub_element_then_else_unchanged in H
      | _ : context [?t <> ?t'], H : context [BrachaRBBuffer_sub _ ?s ?t (?s', ?t')] |- _ =>
          rewrite sub_element_then_else_unchanged in H
    end ;
    buffer_solver || intuition ; fail
  .

  Hint Rewrite
  add_existing_element_invariant
  add_element_then_true
  sub_element_then_else_unchanged
  sub_not_existing_element_invariant
  sub_element_then_false
  add_sub_when_true_is_invarient
  sub_add_when_false_is_invarient
  empty_buffer_then_false
  : bracha_buffer.
  (*)

  Ltac buffer_solver :=
    intros ;
    autorewrite with bracha_buffer in * ;
    auto ;
    match goal with
      | H : false = true |- _ => inversion H
      | H : true = false |- _ => inversion H
    end.*)

  Lemma test_buffer_solver_contradict :
    forall (s : {n : nat | n < count}) (m : InternMessage),
      BrachaRBBuffer_empty_set (s, m) = true -> False.
  Proof.
    buffer_solver.
  Qed.

  Lemma test_buffer_solver_empty_set :
    forall (s : {n : nat | n < count}) (m : InternMessage),
      BrachaRBBuffer_empty_set (s, m) = false.
  Proof.
    buffer_solver.
  Qed.

  Lemma test_buffer_solver_add_and_sub :
    forall buff, forall (s : {n : nat | n < count}) (m : InternMessage),
      forall (s' : {n : nat | n < count}) (m' : InternMessage),
      buff (s, m) = false ->
      BrachaRBBuffer_sub (BrachaRBBuffer_add buff s m) s m (s', m') = buff (s', m').
  Proof.
    buffer_solver.
  Qed.

  Lemma test_combination :
    forall (s : {n : nat | n < count}) (m : InternMessage),
      BrachaRBBuffer_add BrachaRBBuffer_empty_set s m (s, m) = true.
  Proof.
    buffer_solver.
  Qed.
*)

  Definition BrachaRBBuffer := buffer Packet.

  Record BrachaRBState : Set :=
    mkBrachaRBState {
        BrachaRBStep : nat;
        BrachaRBRecvBuffer : BrachaRBBuffer;
        BrachaRBRecvBufferSize : InternMessage -> nat;
        BrachaRBSendBuffer : BrachaRBBuffer;
      }.

    Definition BrachaRB_compute_transition
    (f : nat) (proc : Process) (st : BrachaRBState) (act : BrachaRBAction) : option BrachaRBState :=
    match act with
      | BrachaRBBroadcast m =>
          if (proj1_sig proc =? 0) then
            if BrachaRBStep st =? 0 then
              Some {|
                BrachaRBStep := 1;
                BrachaRBRecvBuffer := BrachaRBRecvBuffer st;
                BrachaRBRecvBufferSize := BrachaRBRecvBufferSize st;
                BrachaRBSendBuffer :=
                  (fun p : Packet => let (n, im') := p in BrachaRBSendBuffer st p || (InternMessage_dec_bool im' (Init m)));
              |}
            else
              Some st
          else
            None
      | BrachaRBDeliver p m =>
          if (proj1_sig p =? proj1_sig proc) && (BrachaRBStep st =? 4) && (2*f+1 <=? BrachaRBRecvBufferSize st (Ready m)) then
            Some {|
                BrachaRBStep := 5;
                BrachaRBRecvBuffer := BrachaRBRecvBuffer st;
                BrachaRBRecvBufferSize := BrachaRBRecvBufferSize st;
                BrachaRBSendBuffer := BrachaRBSendBuffer st;
              |}
          else
            None
      | BrachaRBP2PRecv p q im =>
          if (proj1_sig p =? proj1_sig proc) then
            let recv_buffer_size :=
              if BrachaRBRecvBuffer st (q, im) then
                BrachaRBRecvBufferSize st
              else
                (fun m =>
                   if InternMessage_dec_bool m im then
                     BrachaRBRecvBufferSize st m + 1
                   else
                     BrachaRBRecvBufferSize st m
                ) in
            match im with
            | Init m =>
                  if (BrachaRBStep st =? 1) && (proj1_sig q =? 0) then
                    Some {|
                      BrachaRBStep := 2;
                      BrachaRBRecvBuffer := buffer_add packet_dec (BrachaRBRecvBuffer st) (q, im);
                      BrachaRBRecvBufferSize := recv_buffer_size;
                      BrachaRBSendBuffer := (fun m0 : Packet => let (n, im') := m0 in BrachaRBSendBuffer st m0 || (InternMessage_dec_bool im' (Echo m)));
                    |}
                  else
                    Some {|
                      BrachaRBStep := BrachaRBStep st;
                      BrachaRBRecvBuffer := buffer_add packet_dec (BrachaRBRecvBuffer st) (q, im);
                      BrachaRBRecvBufferSize := recv_buffer_size;
                      BrachaRBSendBuffer := BrachaRBSendBuffer st;
                    |}
            | Echo m =>
                  if (BrachaRBStep st =? 1) && (recv_buffer_size im =? 2*f+1) then
                    Some {|
                      BrachaRBStep := 2;
                      BrachaRBRecvBuffer := buffer_add packet_dec (BrachaRBRecvBuffer st) (q, im);
                      BrachaRBRecvBufferSize := recv_buffer_size;
                      BrachaRBSendBuffer :=
                        (fun m0 : Packet => let (n, im') := m0 in BrachaRBSendBuffer st m0 || (InternMessage_dec_bool im' (Echo m)));
                    |}
                  else if (BrachaRBStep st =? 2) && (recv_buffer_size im =? 2*f+1) then
                    Some {|
                      BrachaRBStep := 3;
                      BrachaRBRecvBuffer := buffer_add packet_dec (BrachaRBRecvBuffer st) (q, im);
                      BrachaRBRecvBufferSize := recv_buffer_size;
                      BrachaRBSendBuffer :=
                        (fun m0 : Packet => let (n, im') := m0 in BrachaRBSendBuffer st m0 || (InternMessage_dec_bool im' (Ready m)));
                    |}
                  else
                    Some {|
                      BrachaRBStep := BrachaRBStep st;
                      BrachaRBRecvBuffer := buffer_add packet_dec (BrachaRBRecvBuffer st) (q, im);
                      BrachaRBRecvBufferSize := recv_buffer_size;
                      BrachaRBSendBuffer := BrachaRBSendBuffer st;
                    |}
            | Ready m =>
                if (BrachaRBStep st =? 1) && (recv_buffer_size im =? f+1) then
                    Some {|
                      BrachaRBStep := 2;
                      BrachaRBRecvBuffer := buffer_add packet_dec (BrachaRBRecvBuffer st) (q, im);
                      BrachaRBRecvBufferSize := recv_buffer_size;
                      BrachaRBSendBuffer :=
                        (fun m0 : Packet => let (n, im') := m0 in BrachaRBSendBuffer st m0 || (InternMessage_dec_bool im' (Echo m)));
                    |}
                  else if (BrachaRBStep st =? 2) && (recv_buffer_size im =? f+1) then
                    Some {|
                      BrachaRBStep := 3;
                      BrachaRBRecvBuffer := buffer_add packet_dec (BrachaRBRecvBuffer st) (q, im);
                      BrachaRBRecvBufferSize := recv_buffer_size;
                      BrachaRBSendBuffer :=
                        (fun m0 : Packet => let (n, im') := m0 in BrachaRBSendBuffer st m0 || (InternMessage_dec_bool im' (Ready m)));
                    |}
                  else if (BrachaRBStep st =? 3) && (recv_buffer_size im =? 2*f+1) then
                    Some {|
                      BrachaRBStep := 4;
                      BrachaRBRecvBuffer := buffer_add packet_dec (BrachaRBRecvBuffer st) (q, im);
                      BrachaRBRecvBufferSize := recv_buffer_size;
                      BrachaRBSendBuffer := BrachaRBSendBuffer st;
                    |}
                  else
                    Some {|
                      BrachaRBStep := BrachaRBStep st;
                      BrachaRBRecvBuffer := buffer_add packet_dec (BrachaRBRecvBuffer st) (q, im);
                      BrachaRBRecvBufferSize := recv_buffer_size;
                      BrachaRBSendBuffer := BrachaRBSendBuffer st;
                    |}
              end
            else
              None
    | BrachaRBP2PSend p q im =>
        if (proj1_sig p =? proj1_sig proc) && (BrachaRBSendBuffer st (q, im)) then
          Some {|
              BrachaRBStep := BrachaRBStep st;
              BrachaRBRecvBuffer := BrachaRBRecvBuffer st;
              BrachaRBRecvBufferSize := BrachaRBRecvBufferSize st;
              BrachaRBSendBuffer := buffer_sub packet_dec (BrachaRBSendBuffer st) (q, im);
            |}
        else
          None
  end.

  Definition BrachaRBTransition
    (f : nat) (proc : Process)
    (st : BrachaRBState) (act : BrachaRBAction) (st' : BrachaRBState) :=
    BrachaRB_compute_transition f proc st act = Some st'.

  Definition BrachaRBActionClass
    (proc : Process) (act : BrachaRBAction) : ActionType :=
    match act with
      | BrachaRBP2PRecv p p0 _ => if (proj1_sig p =? proj1_sig proc) then Input else Unused
      | BrachaRBDeliver p _ => if proj1_sig p =? proj1_sig proc then Output else Unused
      | BrachaRBP2PSend p p0 _ => if (proj1_sig p =? proj1_sig proc) then Output else Unused
      | BrachaRBBroadcast _ => if (proj1_sig proc =? 0) then Input else Unused
    end.

  Lemma BrachaRBUnusedActionProp
    (f : nat) (proc : Process) :
    forall act : BrachaRBAction, BrachaRBActionClass proc act = Unused ->
                            forall st st' : BrachaRBState, ~ BrachaRBTransition f proc st act st'.
  Proof.
    intros.
    case_eq act ; intros ; rewrite H0 in * ; clear H0 ; simpl in H ;
      unfold BrachaRBTransition ;
      unfold BrachaRB_compute_transition ;
      (inversion H ; fail) || idtac ;
      repeat simpl_match ; repeat simpl_arith_bool ; (inversion H ; fail) || idtac ; intro ;
      inversion H1 || destruct H1 ;
      lia || (inversion H2 ; fail)
    .
  Qed.

  Definition BrachaRBStart (p : Process) (st : BrachaRBState) : Prop :=
    st = {|
           BrachaRBStep := if proj1_sig p =? 0 then 0 else 1;
           BrachaRBRecvBuffer := empty_buffer (P := Packet);
           BrachaRBRecvBufferSize := (fun _ : InternMessage => 0);
           BrachaRBSendBuffer := empty_buffer (P := Packet);
          |}.

  Definition BrachaRBProcess
    (f : nat) (proc : Process) : IOADef BrachaRBAction :=
    mkIOADef
      (BrachaRBActionClass proc)
      (BrachaRBStart proc)
      (BrachaRBTransition f proc)
      (BrachaRBUnusedActionProp (proc := proc) (f := f))
  .
End RealiableBroadcast.
(*)
Hint Rewrite
  add_existing_element_invariant
  add_element_then_true
  sub_element_then_else_unchanged
  sub_not_existing_element_invariant
  sub_element_then_false
  add_sub_when_true_is_invarient
  sub_add_when_false_is_invarient
  empty_buffer_then_false
  : bracha_buffer.*)

(*)
Global Ltac buffer_solver :=
    intros ;
    autorewrite with bracha_buffer in * ;
    auto ;
    match goal with
      | H : false = true |- _ => inversion H
      | H : true = false |- _ => inversion H
    end.*)
(*)
Global Ltac buffer_solver :=
    intros ;
    subst ; simpl in * ;
    match goal with
      | p : Packet |- _ => destruct p
      (* boolean goal solving *)
      | H : true = false |- _ => inversion H
      | H : false = true |- _ => inversion H
      (* empty buffer reduction *)
      | |- context [BrachaRBBuffer_empty_set _] =>
          rewrite empty_buffer_then_false
      | H : context [BrachaRBBuffer_empty_set _] |- _ =>
          rewrite empty_buffer_then_false in H
      (* repetition reduction *)
      | |- context [BrachaRBBuffer_add _ ?s ?t (?s, ?t)] =>
          rewrite add_element_then_true
      | |- context [BrachaRBBuffer_sub _ ?s ?t (?s, ?t)] =>
          rewrite sub_element_then_false
      | H : context [BrachaRBBuffer_add _ ?s ?t (?s, ?t)] |- _ =>
          rewrite add_element_then_true in H
      | H : context [BrachaRBBuffer_sub _ ?s ?t (?s, ?t)] |- _ =>
          rewrite sub_element_then_false in H
      (* buffer property reduction *)
      | _ : context [?buff (?s, ?m) = true] |- context [BrachaRBBuffer_add ?buff ?s ?m] =>
          rewrite add_existing_element_invariant
      | _ : context [?buff (?s, ?m) = true] |- context [BrachaRBBuffer_add ?buff _ _ (?s, ?m)] =>
          rewrite add_element_invariant_when_true
      | _ : context [?buff (?s, ?m) = false] |- context [BrachaRBBuffer_sub ?buff ?s ?m] =>
          rewrite sub_not_existing_element_invariant
      | _ : context [?buff (?s, ?m) = false] |- context [BrachaRBBuffer_sub ?buff _ _ (?s, ?m)] =>
          rewrite sub_element_invariant_when_false
      | _ : context [?buff (?s, ?m) = true], H : context [BrachaRBBuffer_add ?buff ?s ?m] |- _ =>
          rewrite add_existing_element_invariant in H
      | _ : context [?buff (?s, ?m) = true], H : context [BrachaRBBuffer_add ?buff _ _ (?s, ?m)] |- _ =>
          rewrite add_element_invariant_when_true in H
      | _ : context [?buff (?s, ?m) = false], H : context [BrachaRBBuffer_sub ?buff ?s ?m] |- _ =>
          rewrite sub_not_existing_element_invariant in H
      | _ : context [?buff (?s, ?m) = false], H : context [BrachaRBBuffer_sub ?buff _ _ (?s, ?m)] |- _ =>
          rewrite sub_element_invariant_when_false in H
      (* add and sub alternance reduction *)
      | _ : context [?buff (?s, ?m) = false] |-
          context [BrachaRBBuffer_sub (BrachaRBBuffer_add ?buff ?s ?t) ?s ?t _] =>
          rewrite sub_add_when_false_is_invarient
      | _ : context [?buff (?s, ?m) = true] |-
          context [BrachaRBBuffer_add (BrachaRBBuffer_sub ?buff ?s ?t) ?s ?t _] =>
          rewrite add_sub_when_true_is_invarient
      | _ : context [?buff (?s, ?m) = false],
          H : context [BrachaRBBuffer_sub (BrachaRBBuffer_add ?buff ?s ?t) ?s ?t _] |- _ =>
          rewrite sub_add_when_false_is_invarient in H
      | _ : context [?buff (?s, ?m) = true],
          H : context [BrachaRBBuffer_add (BrachaRBBuffer_sub ?buff ?s ?t) ?s ?t _] |- _ =>
          rewrite add_sub_when_true_is_invarient in H
      (* elements property reduction *)
      | _ : context [?s <> ?s'] |- context [BrachaRBBuffer_add _ ?s ?t (?s', ?t')] =>
          rewrite add_element_then_else_unchanged
      | _ : context [?t <> ?t'] |- context [BrachaRBBuffer_add _ ?s ?t (?s', ?t')] =>
          rewrite add_element_then_else_unchanged
      | _ : context [?s <> ?s'] |- context [BrachaRBBuffer_sub _ ?s ?t (?s', ?t')] =>
          rewrite sub_element_then_else_unchanged
      | _ : context [?t <> ?t'] |- context [BrachaRBBuffer_sub _ ?s ?t (?s', ?t')] =>
          rewrite sub_element_then_else_unchanged
      | _ : context [?s <> ?s'], H : context [BrachaRBBuffer_add _ ?s ?t (?s', ?t')] |- _ =>
          rewrite add_element_then_else_unchanged in H
      | _ : context [?t <> ?t'], H : context [BrachaRBBuffer_add _ ?s ?t (?s', ?t')] |- _ =>
          rewrite add_element_then_else_unchanged in H
      | _ : context [?s <> ?s'], H : context [BrachaRBBuffer_sub _ ?s ?t (?s', ?t')] |- _ =>
          rewrite sub_element_then_else_unchanged in H
      | _ : context [?t <> ?t'], H : context [BrachaRBBuffer_sub _ ?s ?t (?s', ?t')] |- _ =>
          rewrite sub_element_then_else_unchanged in H
      (* for symetry *)
      | Hneq : context [?s' <> ?s] |- context [BrachaRBBuffer_add _ ?s ?t (?s', ?t')] =>
          apply not_eq_sym in Hneq ; rewrite add_element_then_else_unchanged
      | Hneq : context [?t' <> ?t] |- context [BrachaRBBuffer_add _ ?s ?t (?s', ?t')] =>
          apply not_eq_sym in Hneq ; rewrite add_element_then_else_unchanged
      | Hneq : context [?s' <> ?s] |- context [BrachaRBBuffer_sub _ ?s ?t (?s', ?t')] =>
          apply not_eq_sym in Hneq ; rewrite sub_element_then_else_unchanged
      | Hneq : context [?t' <> ?t] |- context [BrachaRBBuffer_sub _ ?s ?t (?s', ?t')] =>
          apply not_eq_sym in Hneq ; rewrite sub_element_then_else_unchanged
      | Hneq : context [?s' <> ?s], H : context [BrachaRBBuffer_add _ ?s ?t (?s', ?t')] |- _ =>
          apply not_eq_sym in Hneq ; rewrite add_element_then_else_unchanged in H
      | Hneq : context [?t' <> ?t], H : context [BrachaRBBuffer_add _ ?s ?t (?s', ?t')] |- _ =>
          apply not_eq_sym in Hneq ; rewrite add_element_then_else_unchanged in H
      | Hneq : context [?s' <> ?s], H : context [BrachaRBBuffer_sub _ ?s ?t (?s', ?t')] |- _ =>
          apply not_eq_sym in Hneq ; rewrite sub_element_then_else_unchanged in H
      | Hneq : context [?t' <> ?t], H : context [BrachaRBBuffer_sub _ ?s ?t (?s', ?t')] |- _ =>
          apply not_eq_sym in Hneq ; rewrite sub_element_then_else_unchanged in H
    end ;
    (intuition ; fail) || buffer_solver
  .
*)

Global Ltac destruct_BrachaRBAction_eq :=
    discriminate
      || (let H := fresh "H" in intro H ; inversion H ; clear H ; subst)
      || auto
  .

Global Tactic Notation "destruct_BrachaRBAction_eq" "in" ident(H) :=
    contradiction
    || apply destruct_diff_BrachaRBBroadcast in H
    || apply destruct_diff_BrachaRBDeliver in H
    || apply destruct_diff_BrachaRBP2PRecv in H
    || apply destruct_diff_BrachaRBP2PSend in H
    || (inversion H ; clear H ; subst)
  .

  Ltac simpl_InternMessage_dec_bool_aux :=
    match goal with
      | H : context [InternMessage_dec_bool ?m ?m' = true] |- _ =>
          apply InternMessage_dec_bool_true in H
      | H : context [InternMessage_dec_bool ?m ?m' = false] |- _ =>
          apply InternMessage_dec_bool_false in H
    end ;
    try simpl_InternMessage_dec_bool_aux.

  Global Ltac simpl_InternMessage_dec_bool :=
    try simpl_InternMessage_dec_bool_aux.
