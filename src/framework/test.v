Require Import MSets.
Require Import Arith String Ascii BinaryString Init.Byte PArray List ListSet.
Require Import framework.monad.
Require Import Lia.
Require Import common.tactic.
Require Import framework.framework.
Require Import Bool.

Module Buffer := Make String_as_OT.

Definition Message := string.

Parameter NodeCount : nat.
Definition f : nat := NodeCount / 3.
Definition Node := nat.
Definition Round := nat.

Definition InputAction : Type := (Round * Message)%type.

Inductive PacketType : Type :=
  | Init
  | Echo
  | Ready
.

Definition PartialPacket : Type :=
  PacketType*Message*Round*Node.

Open Scope list_scope.
Open Scope string_scope.

(* We delimit the round with the letter D *)
Definition serialize_partialpacket (_p : PartialPacket) : Message :=
  let '(p, m, r, src) := _p in
  match p with
    | Init => String.concat "H" ((of_nat r)::(of_nat src)::(String "I" m)::nil)
    | Echo => String.concat "H" ((of_nat r)::(of_nat src)::(String "E" m)::nil)
    | Ready => String.concat "H" ((of_nat r)::(of_nat src)::(String "R" m)::nil)
  end.

Definition serialize_packet (n : Node) (m : Message) : Message :=
  String.concat "H" ((of_nat n)::m::nil).

Fixpoint cut_on_H (input : string) : string*string :=
  match input with
    | EmptyString => (EmptyString, EmptyString)
    | String a m' =>
        if Ascii.eqb a "H" then
          (EmptyString, m')
        else
          let (prefix, residual) := cut_on_H m' in
          (String a prefix, residual)
  end.

Definition deserialize_packet (m : Message) : option (Node*Message) :=
  let (src_enc, data) := cut_on_H m in
  let src := to_nat src_enc in
  if (src <? NodeCount)%nat then Some (src, data) else None.
(*)
Definition deserialize_packet (m : Message) : option (Node*Message).
  destruct (cut_on_H m) as (dest, data) eqn: H.
  case_eq (to_nat dest <? NodeCount)%nat ; intro.
  apply PeanoNat.Nat.ltb_lt in H0.
  apply (Some (Fin.of_nat_lt H0, data)).
  apply None.
Defined.

Print deserialize_packet.*)

Lemma cut_on_H_cut_on_first_H :
  forall s s' : string, index 0 "H" s = None -> cut_on_H (s ++ String "H" s') = (s, s').
Proof.
  induction s.
  - intros.
    simpl. auto.
  - intros.
    simpl.
    assert ((a =? "H")%char = false).
    eapply index_correct3 in H ; auto.
    case_eq ((a =? "H")%char) ; auto ; intros.
    apply Ascii.eqb_eq in H0. subst. simpl in H.
    destruct s ; simpl in H ; contradiction. discriminate. rewrite H0.
    rewrite IHs ; auto.
    unfold index in H.
    case_eq (prefix "H" (String a s)) ; intro ;
    rewrite H1 in H. inversion H.
    fold index in H. case_eq (index 0 "H" s) ; intros ; auto.
    rewrite H2 in H. inversion H.
Qed.

Lemma of_pos_no_H : forall n, forall s, index 0 "H" s = None -> index 0 "H" (Raw.of_pos n s) = None.
Proof.
  induction n.
  - intros. simpl. apply IHn. simpl. rewrite H. auto.
  - intros. simpl. apply IHn. simpl. rewrite H. auto.
  - intros. simpl. rewrite H. auto.
Qed.

Lemma of_N_no_H : forall n, index 0 "H" (of_N n) = None.
Proof.
  intro. destruct n. auto. simpl.
  rewrite of_pos_no_H ; auto.
Qed.

Lemma of_nat_no_H : forall r : Round, index 0 "H" (of_nat r) = None.
Proof.
  intro. unfold of_nat. rewrite of_N_no_H. auto.
Qed.

Definition deserialize_partialpacket (m : Message) : option PartialPacket :=
  let (round_enc, tmp) := cut_on_H m in
  let (src_enc, data) := cut_on_H tmp in
  let round := to_nat round_enc in
  let src := to_nat src_enc in
  match data with
    | String a m' =>
        match a with
          | "I"%char => Some (Init, m', round, src)
          | "E"%char => Some (Echo, m', round, src)
          | "R"%char => Some (Ready, m', round, src)
          | _ => None
        end
    | _ => None
  end.

Lemma serialize_desirialize_partialpacket_id :
  forall p, deserialize_partialpacket (serialize_partialpacket p) = Some p.
Proof.
  intros.
  unfold deserialize_partialpacket, serialize_partialpacket.
  destruct p. destruct p. destruct p.
  case p ; simpl ; intros ; repeat rewrite cut_on_H_cut_on_first_H ;
    (repeat rewrite to_nat_of_nat ; auto) || apply of_nat_no_H.
Qed.

Lemma serialize_partialpacket_inj :
  forall p p', serialize_partialpacket p = serialize_partialpacket p' -> p = p'.
Proof.
  intros.
  assert (Some p = Some p').
  repeat rewrite <-serialize_desirialize_partialpacket_id.
  rewrite H ; auto. inversion H0. auto.
Qed.

Lemma serialize_deserialize_packet_id :
  forall p, forall m, p < NodeCount -> deserialize_packet (serialize_packet p m) = Some (p, m).
Proof.
  intros.
  unfold deserialize_packet, serialize_packet.
  simpl. rewrite cut_on_H_cut_on_first_H.
  rewrite to_nat_of_nat.
  case_eq (p <? NodeCount)%nat ; intros ; auto.
  apply PeanoNat.Nat.ltb_ge in H0. lia.
  apply of_nat_no_H.
Qed.

Lemma serialize_packet_inj :
  forall p p', forall m m', p < NodeCount -> p' < NodeCount -> serialize_packet p m = serialize_packet p' m' -> p = p' /\ m = m'.
Proof.
  intros.
  assert (Some (p, m) = Some (p', m')).
  repeat rewrite <-serialize_deserialize_packet_id ; auto.
  rewrite H1 ; auto. inversion H2. auto.
Qed.

Definition serialize_source_round (src : Node) (r : Round) :=
  String.concat "H" ((of_nat src)::(of_nat r)::nil).

Definition deserialize_source_round (m : Message) : option (Node*Round)%type :=
  let (src_enc, r_enc) := cut_on_H m in
  let src := to_nat src_enc in
  let r := to_nat r_enc in
  if (src <? NodeCount)%nat then Some (src, r) else None.

Lemma serialize_deserialize_source_round_id :
  forall src, forall r, src < NodeCount -> deserialize_source_round (serialize_source_round src r) = Some (src, r).
Proof.
  intros.
  unfold serialize_source_round, deserialize_source_round.
  simpl. rewrite cut_on_H_cut_on_first_H.
  repeat rewrite to_nat_of_nat.
  case_eq (src <? NodeCount)%nat ; intro ; auto.
  apply PeanoNat.Nat.ltb_ge in H0. lia.
  apply of_nat_no_H.
Qed.

Record CurrentStep : Type :=
  mkCurrentStep {
      (* source H round if the current pair is in step1,
         in theory, this buffer should only contains values where the source is itself *)
      step1 : Buffer.t ;
      (* source H round if the current pair is in step2 *)
      step2 : Buffer.t ;
      (* source H round if the current pair is in step3 *)
      step3 : Buffer.t ;
      (* source H round if the current pair is done *)
      delivered : Buffer.t ;
    }.

Record State : Type :=
  mkState {
      (* the total number of nodes in the model *)
      node_count : Node ;
      (* the id of the current node *)
      id : Node ;
      (* the buffer storing all the (pertinent) received messages, that is, messages with a pair (source, round) not in delivered buffer *)
      input_buffer : Buffer.t ;
      (* the list of buffers for the steps *)
      steps : CurrentStep ;
    }.

Definition Handler := GenHandler (Node*Message) State (Node*Round*Message) unit.

Fixpoint broadcast (m : Message) (n : Node) : Handler :=
  match n with
    | 0 => send (n, m)
    | S n' => (broadcast m n') ;; send (n, m)
  end.

Lemma broadcast_length_is_n :
  forall m, forall n, forall st,
    length (snd (runGenHandler_ignore st (broadcast m n))) = n+1.
Proof.
  intros.
  induction n.
  - unfold broadcast. monad_unfold. simpl. auto.
  - simpl. monad_unfold. destruct (broadcast m n st).
    destruct p. destruct p. simpl in *.
    rewrite app_length. rewrite IHn. simpl. lia.
Qed.

Lemma broadcast_output_only_same_type :
  forall m : Message, forall n : Node, forall st,
    forall n', {nth_error (snd (runGenHandler_ignore st (broadcast m n))) n' = Some (n', m)}+{nth_error (snd (runGenHandler_ignore st (broadcast m n))) n' = None}.
Proof.
  intros.
  induction n.
  - intros. unfold broadcast. monad_unfold.
    simpl.
    destruct n'. left. simpl. auto.
    right. simpl. destruct n' ; auto.
  - intros. simpl.
    assert (length (snd (runGenHandler_ignore st (broadcast m n))) = n+1) by apply broadcast_length_is_n.
    monad_unfold.
    destruct (broadcast m n). destruct p. destruct p. simpl in *.
    destruct IHn.
    assert (n' < length l). apply nth_error_Some. rewrite e. discriminate.
    left.
    rewrite nth_error_app1 ; auto.
    assert (n' >= length l). apply nth_error_None. auto.
    case_eq (n' =? length l)%nat ; intro ; simpl_arith_bool. subst.
    left. rewrite nth_error_app2. assert (tmp: length l - length l = 0) by lia. rewrite tmp. clear tmp.
    simpl. simpl in H. rewrite H.
    assert (S n = n + 1) by lia. rewrite H1. auto. auto.
    right.
    rewrite nth_error_app2 ; auto.
    destruct (n' - length l) eqn: Heq. lia. simpl.
    destruct n0 ; auto.
Qed.

Definition InputHandler (_m : Round*Message) : Handler :=
  s <- get ;;
  let (r, m) := _m in
  if Buffer.mem (serialize_source_round s.(id) r) s.(steps).(delivered) ||
      Buffer.mem (serialize_source_round s.(id) r) s.(steps).(step1) ||
      Buffer.mem (serialize_source_round s.(id) r) s.(steps).(step2) ||
      Buffer.mem (serialize_source_round s.(id) r) s.(steps).(step3) then
    nop
  else
    let m := serialize_partialpacket (Init, m, r, s.(id)) in
    broadcast m (NodeCount-1) ;;
    put (
        mkState
          s.(node_count)
          s.(id)
          s.(input_buffer)
          (mkCurrentStep
             (Buffer.add (serialize_source_round s.(id) r) s.(steps).(step1))
             s.(steps).(step2)
             s.(steps).(step3)
             s.(steps).(delivered)
          )
      )
.

Lemma input_handler_only_broadcast_init :
  forall r : Round, forall m : Message, forall st,
    forall n, {nth_error (snd (runGenHandler_ignore st (InputHandler (r, m)))) n =
            Some (n, serialize_partialpacket (Init, m, r, st.(id)))} +
           {nth_error (snd (runGenHandler_ignore st (InputHandler (r, m)))) n = None}.
Proof.
  intros.
  unfold InputHandler. monad_unfold.
  simpl.
  destruct (Buffer.mem (serialize_source_round (id st) r) (delivered (steps st)) || Buffer.mem (serialize_source_round (id st) r) (step1 (steps st))
       || Buffer.mem (serialize_source_round (id st) r) (step2 (steps st)) || Buffer.mem (serialize_source_round (id st) r) (step3 (steps st))).
  intros. right. destruct n ; auto.
  induction NodeCount.
  - simpl. intros. destruct n. left. simpl. auto. right. simpl.
    destruct n ; auto.
  - assert (tmp : S n0 - 1 = n0) by lia. rewrite tmp. clear tmp.
    destruct (broadcast (of_nat r ++ String "H" (of_nat (id st) ++ String "H" (String "I" m))) n0 st) eqn: Heq.
    destruct p. destruct p. simpl in *.
    edestruct broadcast_output_only_same_type with (of_nat r ++ String "H" (of_nat (id st) ++ String "H" (String "I" m))) n0 st n ;
      monad_unfold ; rewrite Heq in e ; simpl in e.
    left ; rewrite app_nil_r ; auto.
    right ; rewrite app_nil_r ; auto.
Qed.

Definition filter_on_partial_packet (m : Message) (b : Buffer.t) :=
  Buffer.filter (
      fun m' =>
        match deserialize_packet m' with
          | None => false
          | Some (src, data) =>
              data =? m
        end
    ) b.

Lemma filter_on_partial_packet_is_proper :
  forall m : Message,
    Proper (eq ==> eq)
           (fun m' =>
        match deserialize_packet m' with
          | None => false
          | Some (src, data) =>
              data =? m
        end
    ).
Proof.
  intros. hnf. intros. subst. auto.
Qed.

Definition get_round_and_source_from_message (m : Message) : Round*Node :=
  match deserialize_packet m with
    | None => (0, 0)
    | Some (src, data) =>
        match deserialize_partialpacket data with
          | None => (0, 0)
          | Some (_, _, r, src) => (r, src)
        end
  end.

Definition filter_except_round_and_source (r : Round) (src : Node) : Buffer.t -> Buffer.t :=
  Buffer.filter (
      fun m => let (r', src') := get_round_and_source_from_message m in
            negb ((r' =? r)%nat && (src' =? src)%nat)
    ).

Lemma filter_on_round_is_proper :
  forall r : Round, forall src : Node,
    Proper (eq ==> eq)
           (
      fun m => let (r', src') := get_round_and_source_from_message m in
            negb ((r' =? r)%nat && (src' =? src)%nat)
    )
.
Proof.
  intros. hnf. intros. subst. auto.
Qed.

Inductive Step :=
  | NotStarted
  | Step1
  | Step2
  | Step3
  | Delivered
.

Definition Step_ltb (s s' : Step) : bool :=
  match s, s' with
    | NotStarted, NoStarted => false
    | Step1, NotStarted | Step1, Step1 => false
    | Step2, Step2 | Step2, Step1 | Step2, NotStarted => false
    | Step3, Delivered => true
    | Step3, _ => false
    | Delivered, _ => false
    | _, _ => true
  end.

Definition Step_lt (s s' : Step) : Prop :=
  Step_ltb s s' = true.

Notation "s << s'" := (Step_lt s s') (at level 70).

Definition get_step (src : Node) (r : Round) (s : CurrentStep) : Step :=
    let m := serialize_source_round src r in
    if Buffer.mem m s.(delivered) then
      Delivered
    else if Buffer.mem m s.(step3) then
      Step3
    else if Buffer.mem m s.(step2) then
      Step2
    else if Buffer.mem m s.(step1) then
      Step1
    else
      NotStarted.

Definition increase_step (src : Node) (r : Round) (s : CurrentStep) : CurrentStep :=
  match get_step src r s with
    | NotStarted => s
    | Delivered => s
    | Step1 =>
        mkCurrentStep
          (Buffer.remove (serialize_source_round src r) s.(step1))
          (Buffer.add (serialize_source_round src r) s.(step2))
          s.(step3)
          s.(delivered)
    | Step2 =>
        mkCurrentStep
          s.(step1)
          (Buffer.remove (serialize_source_round src r) s.(step2))
          (Buffer.add (serialize_source_round src r) s.(step3))
          s.(delivered)
    | Step3 =>
        mkCurrentStep
          s.(step1)
          s.(step2)
          (Buffer.remove (serialize_source_round src r) s.(step3))
          (Buffer.add (serialize_source_round src r) s.(delivered))
  end
.

Lemma increase_step_equal_spec :
  forall (src : Node) (r : Round) (s : CurrentStep),
    match get_step src r s with
      | NotStarted => get_step src r (increase_step src r s) = NotStarted
      | Delivered => get_step src r (increase_step src r s) = Delivered
      | Step1 => get_step src r (increase_step src r s) = Step2
      | Step2 => get_step src r (increase_step src r s) = Step3
      | Step3 => get_step src r (increase_step src r s) = Delivered
    end.
Proof.
  intros.
  unfold increase_step.
  destruct (get_step src r s) eqn: Heq.
  - auto.
  - unfold get_step in *.
    simpl in *.
    destruct (Buffer.mem (serialize_source_round src r) (delivered s)). inversion Heq.
    destruct (Buffer.mem (serialize_source_round src r) (step3 s)). inversion Heq.
    assert (Buffer.mem (serialize_source_round src r) (Buffer.add (serialize_source_round src r) (step2 s)) = true).
    apply Buffer.mem_spec. apply Buffer.add_spec. auto.
    rewrite H. auto.
  - unfold get_step in *.
    simpl in *.
    destruct (Buffer.mem (serialize_source_round src r) (delivered s)). inversion Heq.
    assert (Buffer.mem (serialize_source_round src r) (Buffer.add (serialize_source_round src r) (step3 s)) = true).
    apply Buffer.mem_spec. apply Buffer.add_spec. auto.
    rewrite H. auto.
  - unfold get_step in *.
    simpl in *.
    assert (Buffer.mem (serialize_source_round src r) (Buffer.add (serialize_source_round src r) (delivered s)) = true).
    apply Buffer.mem_spec. apply Buffer.add_spec. auto.
    rewrite H. auto.
  - auto.
Qed.

Definition set_step (src : Node) (r : Round) (s : CurrentStep) (step : Step) :=
  match step with
    | NotStarted =>
        mkCurrentStep
          (Buffer.remove (serialize_source_round src r) s.(step1))
          (Buffer.remove (serialize_source_round src r) s.(step2))
          (Buffer.remove (serialize_source_round src r) s.(step3))
          (Buffer.remove (serialize_source_round src r) s.(delivered))
    | Delivered =>
        mkCurrentStep
          (Buffer.remove (serialize_source_round src r) s.(step1))
          (Buffer.remove (serialize_source_round src r) s.(step2))
          (Buffer.remove (serialize_source_round src r) s.(step3))
          (Buffer.add (serialize_source_round src r) s.(delivered))
    | Step1 =>
        mkCurrentStep
          (Buffer.add (serialize_source_round src r) s.(step1))
          (Buffer.remove (serialize_source_round src r) s.(step2))
          (Buffer.remove (serialize_source_round src r) s.(step3))
          (Buffer.remove (serialize_source_round src r) s.(delivered))
    | Step2 =>
        mkCurrentStep
          (Buffer.remove (serialize_source_round src r) s.(step1))
          (Buffer.add (serialize_source_round src r) s.(step2))
          (Buffer.remove (serialize_source_round src r) s.(step3))
          (Buffer.remove (serialize_source_round src r) s.(delivered))
    | Step3 =>
        mkCurrentStep
          (Buffer.remove (serialize_source_round src r) s.(step1))
          (Buffer.remove (serialize_source_round src r) s.(step2))
          (Buffer.add (serialize_source_round src r) s.(step3))
          (Buffer.remove (serialize_source_round src r) s.(delivered))
  end.

Lemma set_step_equal_spec :
  forall (src : Node) (r : Round) (s : CurrentStep),
    forall step : Step,
    get_step src r (set_step src r s step) = step.
Proof.
  intros.
  unfold get_step, set_step.
  destruct step ; simpl.
  - assert (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (delivered s)) <> true).
    intro. apply Buffer.mem_spec in H. apply Buffer.remove_spec in H. destruct H. contradiction.
    destruct (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (delivered s))). contradiction.
    assert (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (step3 s)) <> true).
    intro tmp. apply Buffer.mem_spec in tmp. apply Buffer.remove_spec in tmp. destruct tmp. contradiction.
    destruct (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (step3 s))). contradiction.
    assert (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (step2 s)) <> true).
    intro tmp. apply Buffer.mem_spec in tmp. apply Buffer.remove_spec in tmp. destruct tmp. contradiction.
    destruct (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (step2 s))). contradiction.
    assert (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (step1 s)) <> true).
    intro tmp. apply Buffer.mem_spec in tmp. apply Buffer.remove_spec in tmp. destruct tmp. contradiction.
    destruct (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (step1 s))). contradiction.
    auto.
  - assert (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (delivered s)) <> true).
    intro. apply Buffer.mem_spec in H. apply Buffer.remove_spec in H. destruct H. contradiction.
    destruct (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (delivered s))). contradiction.
    assert (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (step3 s)) <> true).
    intro tmp. apply Buffer.mem_spec in tmp. apply Buffer.remove_spec in tmp. destruct tmp. contradiction.
    destruct (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (step3 s))). contradiction.
    assert (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (step2 s)) <> true).
    intro tmp. apply Buffer.mem_spec in tmp. apply Buffer.remove_spec in tmp. destruct tmp. contradiction.
    destruct (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (step2 s))). contradiction.
    assert (Buffer.mem (serialize_source_round src r) (Buffer.add (serialize_source_round src r) (step1 s)) = true).
    apply Buffer.mem_spec. apply Buffer.add_spec. auto. rewrite H2. auto.
  - assert (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (delivered s)) <> true).
    intro. apply Buffer.mem_spec in H. apply Buffer.remove_spec in H. destruct H. contradiction.
    destruct (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (delivered s))). contradiction.
    assert (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (step3 s)) <> true).
    intro tmp. apply Buffer.mem_spec in tmp. apply Buffer.remove_spec in tmp. destruct tmp. contradiction.
    destruct (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (step3 s))). contradiction.
    assert (Buffer.mem (serialize_source_round src r) (Buffer.add (serialize_source_round src r) (step2 s)) = true).
    apply Buffer.mem_spec. apply Buffer.add_spec. auto. rewrite H1. auto.
  - assert (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (delivered s)) <> true).
    intro. apply Buffer.mem_spec in H. apply Buffer.remove_spec in H. destruct H. contradiction.
    destruct (Buffer.mem (serialize_source_round src r) (Buffer.remove (serialize_source_round src r) (delivered s))). contradiction.
    assert (Buffer.mem (serialize_source_round src r) (Buffer.add (serialize_source_round src r) (step3 s)) = true).
    apply Buffer.mem_spec. apply Buffer.add_spec. auto. rewrite H0. auto.
  - assert (Buffer.mem (serialize_source_round src r) (Buffer.add (serialize_source_round src r) (delivered s)) = true).
    apply Buffer.mem_spec. apply Buffer.add_spec. auto. rewrite H. auto.
Qed.

Definition set_step_no_reset (src : Node) (r : Round) (s : CurrentStep) (step : Step) :=
  match step with
    | NotStarted => s
    | Delivered =>
        mkCurrentStep
          s.(step1)
          s.(step2)
          s.(step3)
          (Buffer.add (serialize_source_round src r) s.(delivered))
    | Step1 =>
        mkCurrentStep
          (Buffer.add (serialize_source_round src r) s.(step1))
          s.(step2)
          s.(step3)
          s.(delivered)
    | Step2 =>
        mkCurrentStep
          s.(step1)
          (Buffer.add (serialize_source_round src r) s.(step2))
          s.(step3)
          s.(delivered)
    | Step3 =>
        mkCurrentStep
          s.(step1)
          s.(step2)
          (Buffer.add (serialize_source_round src r) s.(step3))
          s.(delivered)
  end.

Definition set_step_no_reset_equal_spec :
   forall (src : Node) (r : Round) (s : CurrentStep),
    forall step : Step,
    get_step src r s = NotStarted -> get_step src r (set_step_no_reset src r s step) = step.
Proof.
  intros.
  unfold set_step_no_reset, get_step in *.
  destruct step ; simpl in *.
  - auto.
  - destruct (Buffer.mem (serialize_source_round src r) (delivered s)).
    inversion H.
    destruct (Buffer.mem (serialize_source_round src r) (step3 s)).
    inversion H.
    destruct (Buffer.mem (serialize_source_round src r) (step2 s)).
    inversion H.
    assert (Buffer.mem (serialize_source_round src r) (Buffer.add (serialize_source_round src r) (step1 s)) = true).
    apply Buffer.mem_spec. apply Buffer.add_spec. auto. rewrite H0. auto.
  - destruct (Buffer.mem (serialize_source_round src r) (delivered s)).
    inversion H.
    destruct (Buffer.mem (serialize_source_round src r) (step3 s)).
    inversion H.
    assert (Buffer.mem (serialize_source_round src r) (Buffer.add (serialize_source_round src r) (step2 s)) = true).
    apply Buffer.mem_spec. apply Buffer.add_spec. auto. rewrite H0. auto.
  - destruct (Buffer.mem (serialize_source_round src r) (delivered s)).
    inversion H.
    assert (Buffer.mem (serialize_source_round src r) (Buffer.add (serialize_source_round src r) (step3 s)) = true).
    apply Buffer.mem_spec. apply Buffer.add_spec. auto. rewrite H0. auto.
  - assert (Buffer.mem (serialize_source_round src r) (Buffer.add (serialize_source_round src r) (delivered s)) = true).
    apply Buffer.mem_spec. apply Buffer.add_spec. auto. rewrite H0. auto.
Qed.

Definition get_limit (step : Step) (p : PacketType) :=
  match step with
    | Step3 =>
        match p with
          | Ready => 2*f+1
          | _ => 0
        end
    | _ =>
        match p with
          | Ready => f+1
          | Echo => (NodeCount+f+1)/2
          | _ => 0
        end
    end.

Definition RecvHandler (_m : Node*Message) : Handler :=
  s <- get ;;
  let (src, m) := _m in
  match deserialize_partialpacket m with
    | None => nop
    | Some (pm, data, r, proposer) =>
  let step := get_step proposer r s.(steps) in
  match step with
    | Delivered => nop
    | Step3 =>
        match pm with
          | Ready =>
              let next_buffer := Buffer.add (serialize_packet src m) s.(input_buffer) in
              if (Buffer.cardinal (filter_on_partial_packet m next_buffer) =? get_limit step pm)%nat then
                write_output (proposer, r, data) ;;
                put (
                    mkState
                      s.(node_count)
                      s.(id)
                      (
                        filter_except_round_and_source r proposer s.(input_buffer)
                      )
                      (set_step proposer r s.(steps) Delivered)
                  )
              else
                put (
                    mkState
                      s.(node_count)
                      s.(id)
                      next_buffer
                      s.(steps)
                  )
            | _ => nop (* Either malformed or useless packet *)
          end
      | Step2 =>
          match pm with
            | Ready | Echo =>
                let next_buffer := Buffer.add (serialize_packet src m) s.(input_buffer) in
                (* check for the different conditions *)
                if (Buffer.cardinal (filter_on_partial_packet m next_buffer) =? get_limit step pm )%nat then
                  let m_to_send := serialize_partialpacket (Ready, data, r, proposer) in
                  broadcast (m_to_send) (NodeCount-1) ;;
                  put (
                      mkState
                        s.(node_count)
                        s.(id)
                        next_buffer
                        (increase_step proposer r s.(steps))
                  )
                else
                  put (
                    mkState
                      s.(node_count)
                      s.(id)
                      next_buffer
                      s.(steps)
                  )
              | _ => nop
            end
        | Step1 | NotStarted =>
            match pm with
              | Init =>
                  match step with
                    | NotStarted =>
                      let m_to_send := serialize_partialpacket (Echo, data, r, proposer) in
                      broadcast m_to_send (NodeCount-1) ;;
                      put (
                          mkState
                            s.(node_count)
                            s.(id)
                            s.(input_buffer)
                            (set_step_no_reset proposer r s.(steps) Step2)
                        )
                      | _ => nop
                    end
              | Echo | Ready =>
                  let next_buffer := Buffer.add (serialize_packet src m) s.(input_buffer) in
                    (* check for the different conditions *)
                    if (Buffer.cardinal (filter_on_partial_packet m next_buffer) =? get_limit step pm )%nat then
                      (
                        let m_to_send := serialize_partialpacket (Echo, data, r, proposer) in
                        broadcast (m_to_send) (NodeCount-1)
                      ) ;;
                      let m_to_send := serialize_partialpacket (Ready, data, r, proposer) in
                      broadcast (m_to_send) (NodeCount-1) ;;
                      put (
                          mkState
                            s.(node_count)
                            s.(id)
                            next_buffer
                            (set_step proposer r s.(steps) Step3)
                      )
                    else
                      put (
                        mkState
                          s.(node_count)
                          s.(id)
                          next_buffer
                          s.(steps)
                      )
            end
        end end.

Opaque serialize_partialpacket.

Ltac autodestruct_broadcast :=
  match goal with
    | |- context [ broadcast ?a ?b ] =>
        let H := fresh "Heq" in destruct (broadcast a b) eqn: H
  end.

Lemma recv_never_send_init :
  forall n : Node, forall m : Message, forall st : State,
    forall m', forall r, forall n', forall i j,
      nth_error (snd (runGenHandler_ignore st (RecvHandler (n, m)))) i <> Some (j, serialize_partialpacket (Init, m', r, n')).
Proof.
  intros.
  unfold RecvHandler. monad_unfold.
  destruct (deserialize_partialpacket m) ; simpl ; cycle 1.
  destruct i ; discriminate.
  destruct p. destruct p. destruct p.
  destruct (get_step n r0 (steps st)) ; simpl ;
    try (destruct i ; discriminate) ; try destruct (_ =? _)%nat ; repeat (try autodestruct_broadcast ; repeat destruct p) ;
  simpl ; try (destruct i ; discriminate) ; rewrite app_nil_r ;
    (case_eq (i <? length l)%nat ; intro ; simpl_arith_bool ;
     [ edestruct broadcast_output_only_same_type ;
        monad_unfold ; try rewrite nth_error_app1 ; rewrite Heq in e |
       edestruct broadcast_output_only_same_type ;
        monad_unfold ; try rewrite nth_error_app2 ; rewrite Heq0 in e || rewrite Heq in e ] ;
     auto) ; simpl in e ; try rewrite e ; try discriminate ; intro Hp ; inversion Hp as [H1] ;
    apply serialize_partialpacket_inj in H0 ; inversion H0.
Qed.

Lemma buffer_monotone_before_delivering :
  forall n : Node, forall m : Message, forall p : PacketType, forall r : Round, forall src : Node, forall st : State,
    let '(_, st', _) := runGenHandler_ignore st (RecvHandler (n, serialize_partialpacket (p, m, r, src))) in
    get_step n r st'.(steps) <> Delivered ->
    Buffer.Subset (st.(input_buffer)) (st'.(input_buffer)).
Proof.
  intros.
  unfold RecvHandler in *. monad_unfold.
  rewrite serialize_desirialize_partialpacket_id.
  destruct (get_step n r (steps st)) ; try destruct (_ =? _)%nat ;
    repeat destruct p ; repeat (destruct (broadcast _ _ _) ; repeat destruct p) ;
    unfold Buffer.Subset ; auto ; intros ; try apply Buffer.add_spec ; auto.
  simpl in H.
  unfold get_step in H. simpl in H.
  assert (Buffer.mem (serialize_source_round n r)
          (Buffer.add (serialize_source_round n r) (delivered (steps st))) = true).
  apply Buffer.mem_spec. apply Buffer.add_spec. auto.
  rewrite H1 in H. contradiction.
Qed.

Lemma recv_echo_acknowledge_before_step3 :
  forall n : Node, forall m : Message, forall r : Round, forall src : Node, forall st : State,
    let '(_, st', _) := runGenHandler_ignore st (RecvHandler (n, serialize_partialpacket (Echo, m, r, src))) in
    get_step n r st'.(steps) << Step3 ->
    Buffer.In (serialize_packet n (serialize_partialpacket (Echo, m, r, src))) st'.(input_buffer).
Proof.
  intros.
  unfold RecvHandler, increase_step in *. monad_unfold.
  rewrite serialize_desirialize_partialpacket_id.
  destruct (get_step n r (steps st)) eqn: Heq ; try destruct (_ =? _)%nat ;
    repeat destruct p ; repeat (destruct (broadcast _ _ _) ; repeat destruct p) ; auto ; intros ;
    try apply Buffer.add_spec ; auto ; rewrite Heq in H ; hnf in H ; simpl in H ; inversion H.
Qed.

Opaque set_step.

Lemma recv_ready_acknowledge_before_delivered :
  forall n : Node, forall m : Message, forall r : Round, forall src : Node, forall st : State,
    let '(_, st', _) := runGenHandler_ignore st (RecvHandler (n, serialize_partialpacket (Ready, m, r, src))) in
    get_step n r st'.(steps) << Delivered ->
    Buffer.In (serialize_packet n (serialize_partialpacket (Ready, m, r, src))) st'.(input_buffer).
Proof.
  intros.
  unfold RecvHandler, increase_step in *. monad_unfold.
  rewrite serialize_desirialize_partialpacket_id.
  destruct (get_step n r (steps st)) eqn: Heq ; try destruct (_ =? _)%nat ;
    repeat destruct p ; repeat (destruct (broadcast _ _ _) ; repeat destruct p) ; auto ; intros ;
    try apply Buffer.add_spec ; auto ; simpl in * ; try rewrite set_step_equal_spec in H ; try rewrite Heq in H ;
    hnf in H ; simpl in H ; inversion H.
Qed.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Permutation.
Require Import PermutSetoid.
Require Import Equalities.
(*)
Lemma dupA_then_dup :
  forall A, forall l : list A, NoDupA eq l -> NoDup l.
Proof.
  intro A. induction l.
  - intro. apply NoDup_nil.
  - intro. inversion H.
    apply NoDup_cons. intro. apply H2.
    subst.
    revert H4.
    intro.
    induction l.

    intro. apply InA_nil. auto.
    intro. apply InA_cons. subst.
    right. apply IHl0. intro.
  intros.
  induction l

  intros.
  inversion H. subst. apply NoDup_nil.
  apply NoDup_cons. intro. apply H0.
  destruct l0. apply InA_nil. auto.

  *)

Lemma add_buffer_perm_buffer_add_element :
  forall b : Buffer.t, forall m : Buffer.elt,
    Buffer.mem m b <> true ->
    length (Buffer.elements (Buffer.add m b)) = length (m::(Buffer.elements b)).
Proof.
  intros.
  assert (permutation eq string_dec (Buffer.elements (Buffer.add m b)) (m::(Buffer.elements b))).
  apply NoDupA_equivlistA_permut.
  apply eq_equivalence.
  apply Buffer.elements_spec2w.
  apply NoDupA_cons.
  intro. apply Buffer.elements_spec1 in H0.
  apply H. apply Buffer.mem_spec. auto.
  apply Buffer.elements_spec2w.
  unfold equivlistA. intros. split ; intro.
  apply Buffer.elements_spec1 in H0. apply Buffer.add_spec in H0.
  destruct H0. subst. auto.
  apply InA_cons. right. apply Buffer.elements_spec1. auto.
  apply Buffer.elements_spec1. apply Buffer.add_spec.
  apply InA_cons in H0. destruct H0 ; auto. apply Buffer.elements_spec1 in H0. auto.
  apply permutation_Permutation in H0.
  destruct H0.
  destruct H0.
  apply Forall2_length in H1. apply Permutation_length in H0.
  rewrite H1 in H0. auto.
  apply eq_equivalence.
Qed.

Lemma add_buffer_then_stricly_bigger :
  forall b : Buffer.t, forall m : Buffer.elt,
    Buffer.mem m b <> true ->
    Buffer.cardinal (Buffer.add m b) = Buffer.cardinal b + 1.
Proof.
  intros.
  apply add_buffer_perm_buffer_add_element in H.
  simpl in H.
  repeat rewrite Buffer.cardinal_spec. lia.
Qed.

Lemma add_buffer_perm_buffer :
  forall b : Buffer.t, forall m : Buffer.elt,
    Buffer.mem m b = true ->
    length (Buffer.elements (Buffer.add m b)) = length (Buffer.elements b).
Proof.
  intros.
  assert (permutation eq string_dec (Buffer.elements (Buffer.add m b)) (Buffer.elements b)).
  apply NoDupA_equivlistA_permut.
  apply eq_equivalence.
  apply Buffer.elements_spec2w.
  apply Buffer.elements_spec2w.
  unfold equivlistA. intros. split ; intro.
  apply Buffer.elements_spec1 in H0. apply Buffer.add_spec in H0.
  destruct H0. subst. apply Buffer.mem_spec in H. apply Buffer.elements_spec1. auto.
  apply Buffer.elements_spec1. auto. apply Buffer.elements_spec1.
  apply Buffer.elements_spec1 in H0. apply Buffer.add_spec. auto.
  apply permutation_Permutation in H0.
  destruct H0.
  destruct H0.
  apply Forall2_length in H1. apply Permutation_length in H0.
  rewrite H1 in H0. auto.
  apply eq_equivalence.
Qed.

Lemma not_add_buffer_then_equal :
  forall b : Buffer.t, forall m : Buffer.elt,
    Buffer.mem m b = true ->
    Buffer.cardinal (Buffer.add m b) = Buffer.cardinal b.
Proof.
  intros.
  apply add_buffer_perm_buffer in H.
  repeat rewrite Buffer.cardinal_spec. auto.
Qed.

Lemma add_increase_then_not_in_buffer_aux :
  forall b : Buffer.t, forall m : Buffer.elt,
    length (Buffer.elements (Buffer.add m b)) > length (Buffer.elements b)
    -> Buffer.mem m b <> true.
Proof.
  intros.
  assert (NoDupA eq (m :: Buffer.elements b)).
  apply NoDupA_cons.
  intro. apply Buffer.elements_spec1 in H0.
  apply Buffer.mem_spec in H0. apply not_add_buffer_then_equal in H0.
  repeat rewrite Buffer.cardinal_spec in H0. rewrite H0 in H. lia.
  apply Buffer.elements_spec2w.
  inversion H0. subst. intro. apply H3.
  apply Buffer.elements_spec1. apply Buffer.mem_spec. auto.
Qed.

Lemma add_increase_then_not_in_buffer :
  forall b : Buffer.t, forall m : Buffer.elt,
    Buffer.cardinal (Buffer.add m b) > Buffer.cardinal b -> Buffer.mem m b <> true.
Proof.
  intros.
  apply add_increase_then_not_in_buffer_aux.
  repeat rewrite Buffer.cardinal_spec in H. auto.
Qed.

Lemma filter_add_either_add_or_not_m_not_m' :
  forall n, n < NodeCount -> forall m m' : Message, forall b : Buffer.t,
      m <> m' ->
    Buffer.cardinal (filter_on_partial_packet m (Buffer.add (serialize_packet n m') b)) =
      Buffer.cardinal (filter_on_partial_packet m b).
Proof.
  intros n H m m' b Heq.
  repeat rewrite Buffer.cardinal_spec.
   assert (
       permutation eq string_dec
                 (Buffer.elements (filter_on_partial_packet m (Buffer.add (serialize_packet n m') b)))
                 (Buffer.elements (filter_on_partial_packet m b))
     ).
   apply NoDupA_equivlistA_permut.
   apply eq_equivalence.
   apply Buffer.elements_spec2w.
   apply Buffer.elements_spec2w.
   unfold equivlistA. intro. split ; intro.
   + apply Buffer.elements_spec1 in H0. apply Buffer.elements_spec1.
     apply Buffer.filter_spec in H0. apply Buffer.filter_spec.
     apply filter_on_partial_packet_is_proper.
     split. destruct H0.
     apply Buffer.add_spec in H0. destruct H0. subst.
     rewrite serialize_deserialize_packet_id in H1. apply String.eqb_eq in H1. subst ; contradiction.
     auto. auto. apply H0. apply filter_on_partial_packet_is_proper.
    + apply Buffer.elements_spec1. apply Buffer.elements_spec1 in H0.
      apply Buffer.filter_spec in H0. apply Buffer.filter_spec.
      apply filter_on_partial_packet_is_proper. destruct H0.
      split ; auto. apply Buffer.add_spec. auto.
      apply filter_on_partial_packet_is_proper.
    + apply permutation_Permutation in H0. destruct H0.
      destruct H0. apply Forall2_length in H1.
      apply Permutation_length in H0.
      rewrite H1 in H0. auto.
      apply eq_equivalence.
Qed.

Lemma filter_add_either_add_or_not :
  forall n, n < NodeCount -> forall m m' : Message, forall b : Buffer.t,
    {Buffer.cardinal (filter_on_partial_packet m (Buffer.add (serialize_packet n m') b)) =
      Buffer.cardinal (filter_on_partial_packet m b)}+{
      Buffer.cardinal (filter_on_partial_packet m (Buffer.add (serialize_packet n m') b)) =
      Buffer.cardinal (filter_on_partial_packet m b)+1
    }.
Proof.
  intros.
  destruct (string_dec m m').
  - (* m = m' *)
    subst m'.
    destruct (Buffer.mem (serialize_packet n m) (filter_on_partial_packet m b)) eqn: Hmem.
    {
      left. apply Buffer.mem_spec, Buffer.filter_spec in Hmem.
      repeat rewrite Buffer.cardinal_spec.
      assert (permutation eq string_dec
                (Buffer.elements (filter_on_partial_packet m (Buffer.add (serialize_packet n m) b)))
                (Buffer.elements (filter_on_partial_packet m b))).
      apply NoDupA_equivlistA_permut.
      apply eq_equivalence.
      apply Buffer.elements_spec2w.
      apply Buffer.elements_spec2w.
      unfold equivlistA. intro. split ; intro.
      apply Buffer.elements_spec1.
      apply Buffer.filter_spec. apply filter_on_partial_packet_is_proper.
      apply Buffer.elements_spec1 in H0. apply Buffer.filter_spec in H0. destruct H0.
      split. apply Buffer.add_spec in H0.
      destruct H0. subst. apply Hmem. auto. auto.
      apply filter_on_partial_packet_is_proper.
      apply Buffer.elements_spec1 in H0. apply Buffer.elements_spec1.
      apply Buffer.filter_spec in H0 ; try apply Buffer.filter_spec ; try apply filter_on_partial_packet_is_proper.
      destruct H0. split. apply Buffer.add_spec. auto. auto.
      apply permutation_Permutation in H0. destruct H0.
      destruct H0. apply Forall2_length in H1.
      apply Permutation_length in H0. rewrite H1 in H0. auto.
      apply eq_equivalence. apply filter_on_partial_packet_is_proper.
    }
   {
     right.
     assert (
         permutation eq string_dec
                (Buffer.elements (filter_on_partial_packet m (Buffer.add (serialize_packet n m) b)))
                ((serialize_packet n m)::(Buffer.elements (filter_on_partial_packet m b)))
       ).
     apply NoDupA_equivlistA_permut.
     apply eq_equivalence.
     apply Buffer.elements_spec2w.
     apply NoDupA_cons. intro.
     apply not_true_iff_false in Hmem. apply Hmem.
     apply Buffer.mem_spec. apply Buffer.elements_spec1 in H0. auto.
     apply Buffer.elements_spec2w.
     unfold equivlistA. intro. split ; intro.
     apply InA_cons. destruct (string_dec x (serialize_packet n m)) ; auto. right.
     apply Buffer.elements_spec1.
     apply Buffer.filter_spec. apply filter_on_partial_packet_is_proper.
     apply Buffer.elements_spec1 in H0. apply Buffer.filter_spec in H0. destruct H0.
     split. apply Buffer.add_spec in H0.
     destruct H0. subst. contradiction. auto. auto.
     apply filter_on_partial_packet_is_proper.
     apply InA_cons in H0. destruct H0. subst.
     apply Buffer.elements_spec1. apply Buffer.filter_spec. apply filter_on_partial_packet_is_proper.
     split. apply Buffer.add_spec. auto. rewrite serialize_deserialize_packet_id. apply String.eqb_eq. auto. auto.
     apply Buffer.elements_spec1 in H0. apply Buffer.elements_spec1.
     apply Buffer.filter_spec in H0 ; try apply Buffer.filter_spec ; try apply filter_on_partial_packet_is_proper.
     destruct H0. split. apply Buffer.add_spec. auto. auto.
     apply permutation_Permutation in H0. destruct H0.
     destruct H0. apply Forall2_length in H1.
     apply Permutation_length in H0. rewrite H1 in H0. simpl in H0.
     repeat rewrite Buffer.cardinal_spec.
     assert (Datatypes.length (Buffer.elements (filter_on_partial_packet m b)) + 1 =
               S (Datatypes.length (Buffer.elements (filter_on_partial_packet m b)))) by lia.
     rewrite H2. auto.
     apply eq_equivalence.
   }
 - (* m <> m' *)
   eapply filter_add_either_add_or_not_m_not_m' in n0.
   left. apply n0. auto.
Qed.

Lemma filter_add_either_add_or_not_m_not_m'_contrapose :
  forall n, n < NodeCount -> forall m m' : Message, forall b : Buffer.t,
  Buffer.cardinal (filter_on_partial_packet m (Buffer.add (serialize_packet n m') b)) =
      Buffer.cardinal (filter_on_partial_packet m b) + 1 -> m = m'.
Proof.
  intros.
  destruct (string_dec m m'). auto.
  eapply filter_add_either_add_or_not_m_not_m' in n0. rewrite n0 in H0.
  lia. auto.
Qed.

Lemma forall2_is_eq :
  forall A, forall l l' : list A, Forall2 eq l l' -> l = l'.
Proof.
  intro. induction l.
  - induction l'.
    + auto.
    + intro. inversion H.
  - intros. inversion H. subst.
    assert (l = l'0). apply IHl. auto. subst. auto.
Qed.

Lemma permutation_is_Permutation_with_eq :
  forall l l', permutation eq string_dec l l' -> Permutation l l'.
Proof.
  intros.
  apply permutation_Permutation in H ; try apply eq_equivalence.
  destruct H. destruct H. apply forall2_is_eq in H0. subst. auto.
Qed.

Lemma recv_never_impact_other_pair :
  forall n : Node, forall m : Message, forall r r' : Round, forall src src' : Node, forall p : PacketType, forall st : State,
    let '(_, st', _) := runGenHandler_ignore st (RecvHandler (n, serialize_partialpacket (p, m, r, src))) in
    Buffer.cardinal (filter_on_partial_packet (serialize_partialpacket (p, m, r', src')) st'.(input_buffer)) <>
      Buffer.cardinal (filter_on_partial_packet (serialize_partialpacket (p, m, r', src')) st.(input_buffer)) ->
    n < NodeCount ->
    r = r' /\ src = src'.
Proof.
  intros.
  unfold RecvHandler, increase_step in *. monad_unfold.
  rewrite serialize_desirialize_partialpacket_id.
  destruct (get_step n r (steps st)) eqn: Heq ; try destruct (_ =? _)%nat ;
    repeat destruct p ; repeat (destruct (broadcast _ _ _) ; repeat destruct p) ; auto ; intros ;
    try apply Buffer.add_spec ; auto ; simpl in * ; try lia ;
    (edestruct filter_add_either_add_or_not ; try apply H0 ;
    (rewrite e in H ; lia)
    || (apply filter_add_either_add_or_not_m_not_m'_contrapose in e ; try apply serialize_partialpacket_inj in e ;
    inversion e ; auto ; fail) ; fail)
    || auto
  .
  repeat rewrite Buffer.cardinal_spec in H.
  destruct ((r' =? r)%nat && (src =? src')%nat) eqn: Heqr. repeat simpl_arith_bool ; auto.
  contradict H. apply Permutation_length.
  assert (permutation eq string_dec
         (Buffer.elements
            (filter_on_partial_packet (serialize_partialpacket (Ready, m, r', src'))
               (filter_except_round_and_source r src (input_buffer st))))
         (Buffer.elements
       (filter_on_partial_packet (serialize_partialpacket (Ready, m, r', src')) (input_buffer st)))).
  apply NoDupA_equivlistA_permut.
  apply eq_equivalence.
  apply Buffer.elements_spec2w.
  apply Buffer.elements_spec2w.
  unfold equivlistA. intro. split ; intro.
  - apply Buffer.elements_spec1. apply Buffer.elements_spec1 in H.
    apply Buffer.filter_spec in H. destruct H. apply Buffer.filter_spec in H.
    destruct H. apply Buffer.filter_spec. apply filter_on_partial_packet_is_proper.
    split ; auto. apply filter_on_round_is_proper.
    apply filter_on_partial_packet_is_proper.
  - apply Buffer.elements_spec1. apply Buffer.elements_spec1 in H.
    apply Buffer.filter_spec in H. apply Buffer.filter_spec.
    apply filter_on_partial_packet_is_proper.
    split. destruct H.
    apply Buffer.filter_spec. apply filter_on_round_is_proper.
    split. apply H. unfold get_round_and_source_from_message.
    destruct (deserialize_packet x). destruct p. apply String.eqb_eq in H1.
    subst. rewrite serialize_desirialize_partialpacket_id.
    apply negb_true_iff.
    apply andb_false_iff. repeat simpl_arith_bool. left. simpl_arith_bool. auto. right. simpl_arith_bool. auto.
    inversion H1.
    apply H. apply filter_on_partial_packet_is_proper.
  - apply permutation_is_Permutation_with_eq in H. auto.
Qed.

Lemma send_ready_satisfies_condition :
  forall n : Node, forall m : Message, forall r : Round, forall src : Node, forall p : PacketType, forall st : State,
    let '(_, _, _snd) := runGenHandler_ignore st (RecvHandler (n, serialize_partialpacket (p, m, r, src))) in
    let '(_, _, _snd') := runGenHandler_ignore st (broadacst (serialize_partialpacket (Ready, m, r, src)) NodeCount) in
    _snd' = _snd ->
    p = Echo /\ Buffer.cardinal (filter_on_partial_packet m next_buffer) = get_limit step p

Definition empty_step :=
  mkCurrentStep
    Buffer.empty
    Buffer.empty
    Buffer.empty
    Buffer.empty
.

Definition init_state (n : nat) :=
  mkState
    NodeCount
    n
    Buffer.empty
    empty_step
.

(* Now that we have written the implementation of our protocol, we have to prove that it satifies some local prop *)

Definition input_types := ((Round*Message)+(Node*Message))%type.

Definition PreRun : Type := nat -> input_types.

Definition compute_transition
      (st : State)
      (i : input_types) :=
  match i with
    | inl q =>
        runGenHandler_ignore st (InputHandler q)
    | inr q =>
        runGenHandler_ignore st (RecvHandler q)
  end.

Require Import List.
Import ListNotations.

Definition SpecializedNodeModel := @NodeAction (Round*Message) (Node*Round*Message) (Node*Message) (Round*Message).

Fixpoint out_to_model (out : list (Node*Round*Message)) : list SpecializedNodeModel :=
  match out with
    | [] => []
    | a::b => (Output a)::(out_to_model b)
  end.

Fixpoint send_to_model snd : list SpecializedNodeModel :=
  match snd with
    | [] => []
    | a::b => (Send a)::(send_to_model b)
  end.

Lemma out_of_model_no_recv :
  forall out, forall p, ~In (Recv p) (out_to_model out).
Proof.
  induction out.
  - intros. simpl. auto.
  - intros. simpl. intro. destruct H. inversion H.
    eapply IHout. apply H.
Qed.

Lemma send_to_model_no_recv :
  forall out, forall p, ~In (Recv p) (send_to_model out).
Proof.
  induction out.
  - intros. simpl. auto.
  - intros. simpl. intro. destruct H. inversion H.
    eapply IHout. apply H.
Qed.

Lemma out_of_model_no_input :
  forall out, forall p, ~In (Input p) (out_to_model out).
Proof.
  induction out.
  - intros. simpl. auto.
  - intros. simpl. intro. destruct H. inversion H.
    eapply IHout. apply H.
Qed.

Lemma send_to_model_no_input :
  forall out, forall p, ~In (Input p) (send_to_model out).
Proof.
  induction out.
  - intros. simpl. auto.
  - intros. simpl. intro. destruct H. inversion H.
    eapply IHout. apply H.
Qed.


Definition create_list_from_transition
      (st : State)
      (i : input_types) : State * list SpecializedNodeModel :=
  match i with
    | frontend q =>
        let '(_out, st', _send) := runGenHandler_ignore st (InputHandler q) in
        (st', (Input q)::(out_to_model _out) ++ (send_to_model _send))
    | backend q =>
        let '(_out, st', _send) := runGenHandler_ignore st (RecvHandler q) in
        (st', (Recv q)::(out_to_model _out) ++ (send_to_model _send))
  end.

Lemma create_list_from_transition_nth_recv :
  forall st, forall i, forall n, forall p,
    nth_error (snd (create_list_from_transition st i)) n = Some (Recv p) -> n = 0.
Proof.
  intros.
  destruct n. auto.
  destruct i.
  simpl in H. destruct (runGenHandler_ignore st (InputHandler p0)). destruct p1.
  simpl in H.
  apply nth_error_In, in_app_or in H.
  destruct H. apply out_of_model_no_recv in H. contradiction.
  apply send_to_model_no_recv in H. contradiction.
  simpl in H. destruct (runGenHandler_ignore st (RecvHandler p0)). destruct p1.
  simpl in H.
  apply nth_error_In, in_app_or in H.
  destruct H. apply out_of_model_no_recv in H. contradiction.
  apply send_to_model_no_recv in H. contradiction.
Qed.

Lemma create_list_from_transition_nth_input :
  forall st, forall i, forall n, forall p,
    nth_error (snd (create_list_from_transition st i)) n = Some (Input p) -> n = 0.
Proof.
  intros.
  destruct n. auto.
  destruct i.
  simpl in H. destruct (runGenHandler_ignore st (InputHandler p0)). destruct p1.
  simpl in H.
  apply nth_error_In, in_app_or in H.
  destruct H. apply out_of_model_no_input in H. contradiction.
  apply send_to_model_no_input in H. contradiction.
  simpl in H. destruct (runGenHandler_ignore st (RecvHandler p0)). destruct p1.
  simpl in H.
  apply nth_error_In, in_app_or in H.
  destruct H. apply out_of_model_no_input in H. contradiction.
  apply send_to_model_no_input in H. contradiction.
Qed.

Lemma create_list_from_transition_never_nil :
  forall st st' : State, forall i : input_types,
    create_list_from_transition st i <> (st', []).
Proof.
  intros.
  unfold create_list_from_transition.
  induction i.
  destruct (runGenHandler_ignore st (InputHandler a)). destruct p.
  intro. apply pair_equal_spec in H. destruct H. inversion H0.
  destruct (runGenHandler_ignore st (RecvHandler b)). destruct p.
  intro. apply pair_equal_spec in H. destruct H. inversion H0.
Qed.

Lemma create_list_from_transition_never_null :
  forall st : State, forall i : input_types,
    length (snd (create_list_from_transition st i)) <> 0.
Proof.
  intros.
  intro. apply length_zero_iff_nil in H.
  destruct (create_list_from_transition st i) eqn: Heq.
  eapply create_list_from_transition_never_nil.
  rewrite Heq. simpl in *. subst.
  Unshelve. 2: apply s. auto.
Qed.

Fixpoint create_list_of_actions
      (st : State)
      (pr : PreRun)
      (target : nat) : State * list SpecializedNodeModel :=
  match target with
    | 0 =>
        create_list_from_transition st (pr 0)
    | S target' =>
        let (st', prefix) := create_list_of_actions st pr target' in
        let (st'', res) := create_list_from_transition st' (pr target) in
        (st'', prefix ++ res)
  end.

Lemma create_list_of_action_longer_than_target :
  forall st : State, forall pr : PreRun, forall target : nat,
    length (snd (create_list_of_actions st pr target)) > target.
Proof.
  intros.
  induction target ; simpl.
  - destruct (create_list_of_actions st pr 0).
    destruct (create_list_from_transition st (pr 0)) eqn : Heq.
    assert (l0 <> []). intro. subst.
    apply create_list_from_transition_never_nil in Heq. auto.
    assert (length l0 <> 0). intro.
    apply length_zero_iff_nil in H0. contradiction. simpl.
    lia.
  - destruct (create_list_of_actions st pr target).
    destruct (create_list_from_transition s (pr (S target))) eqn : Heq. simpl.
    rewrite app_length.
    assert (l0 <> []). intro. subst.
    apply create_list_from_transition_never_nil in Heq. auto.
    assert (length l0 <> 0). intro.
    apply length_zero_iff_nil in H0. contradiction. simpl in *.
    lia.
Qed.

Lemma create_list_of_action_never_nil :
  forall st st' : State, forall pr : PreRun, forall target : nat,
    create_list_of_actions st pr target <> (st', []).
Proof.
  intros.
  destruct target ; simpl.
  - apply create_list_from_transition_never_nil.
  - destruct (create_list_of_actions st pr target).
    destruct (create_list_from_transition s (pr (S target))) eqn : Heq.
    intro. apply pair_equal_spec in H. destruct H. subst.
    apply app_eq_nil in H0. destruct H0. subst. apply create_list_from_transition_never_nil in Heq. auto.
Qed.

Lemma list_of_actions_is_revertable :
  forall st : State, forall pr : PreRun, forall target : nat,
    exists l', exists st', snd (create_list_of_actions st pr target) = l' ++ (snd (create_list_from_transition st' (pr target))).
Proof.
  destruct target.
  - simpl.
    destruct (pr 0) ; simpl.
    destruct (runGenHandler_ignore st (InputHandler p)) eqn: Heq. destruct p0 eqn: Heq0.
    subst.
    exists []. exists st. rewrite Heq. simpl. auto.
    destruct (runGenHandler_ignore st (RecvHandler p)) eqn: Heq. destruct p0 eqn: Heq0.
    subst.
    exists []. exists st. rewrite Heq. simpl. auto.
  - simpl.
    destruct (create_list_of_actions st pr target).
    destruct (create_list_from_transition s (pr (S target))) eqn: Heq.
    exists l. exists s. rewrite Heq. simpl. auto.
Qed.

Lemma list_of_actions_is_revertable_exact :
  forall st : State, forall pr : PreRun, forall target : nat,
    snd (create_list_of_actions st pr (S target)) =
      (snd (create_list_of_actions st pr target)) ++ (snd (create_list_from_transition (fst (create_list_of_actions st pr target)) (pr (S target)))).
Proof.
  intros.
  simpl. destruct (create_list_of_actions st pr target). simpl.
  destruct (create_list_from_transition s (pr (S target))). simpl.
  auto.
Qed.

Lemma list_of_actions_is_revertable_extended :
  forall st : State, forall pr : PreRun, forall target : nat, forall j : nat,
    let (_, l) := create_list_of_actions st pr target in
    j <= target ->
    exists l' l'', exists st', l = l' ++ (snd (create_list_from_transition st' (pr j))) ++ l''.
Proof.
  intros st pr.
  assert (
      forall i : nat, forall target : nat, forall j : nat,
        let (_, l) := create_list_of_actions st pr target in
        j <= target -> target - j = i ->
        exists l'' l', exists st', l = l' ++ (snd (create_list_from_transition st' (pr j))) ++ l''
    ).
  induction i.
  - intros. destruct (create_list_of_actions st pr target) eqn: Heq.
    intros. assert (target = j) by lia. subst.
    exists []. edestruct list_of_actions_is_revertable.
    destruct H1. exists x. exists x0. rewrite app_nil_r, <- H1, Heq. simpl. auto.
  - intros. destruct (create_list_of_actions st pr target) eqn: Heq.
    intros. (*)
    edestruct list_of_actions_is_revertable. rewrite Heq in H1. destruct H1.
    simpl in H1. subst.*)
    specialize IHi with (target - 1) j.
    destruct (create_list_of_actions st pr (target - 1)) eqn: Heq0.
    assert (j <= target - 1). lia. apply IHi in H1. clear IHi.
    destruct H1. destruct H1. destruct H1. simpl in Heq0.
    subst. destruct target. lia. simpl in Heq0. assert (tmp : target - 0 = target) by lia. rewrite tmp in Heq0. clear tmp.
    simpl in Heq. rewrite Heq0 in Heq.
    destruct (create_list_from_transition s0 (pr (S target))).
    apply pair_equal_spec in Heq. destruct Heq.
    exists (x ++ l0), x0. exists x1. rewrite <-H2.
    repeat rewrite app_assoc. auto. lia.
  - intros. specialize H with (target - j) target j. destruct (create_list_of_actions st pr target).
    intros. destruct H. lia. auto. destruct H. exists x0, x. auto.
Qed.


Definition get_action (pr : PreRun) (st : State) (i : nat) : option NodeAction :=
  let (_, l) := create_list_of_actions st pr i in
  nth_error l i.

Lemma get_action_is_never_error :
  forall pr : PreRun, forall st : State, forall i : nat,
    get_action pr st i <> None.
Proof.
  destruct i.
  - unfold get_action.
    assert (length (snd (create_list_of_actions st pr 0)) > 0). apply create_list_of_action_longer_than_target.
    destruct (create_list_of_actions st pr 0).
    simpl in H.
    apply nth_error_Some. apply H.
  - unfold get_action.
    assert (length (snd (create_list_of_actions st pr (S i))) > S i). apply create_list_of_action_longer_than_target.
    destruct (create_list_of_actions st pr (S i)).
    simpl in H.
    apply nth_error_Some. apply H.
Qed.

Require Import Arith.

Lemma recv_dec :
  forall p p' : Round*Message, {p = p'}+{p <> p'}.
Proof.
  intros.
  destruct p, p'.
  destruct PeanoNat.Nat.eq_dec with r r0. subst.
  destruct string_dec with m m0. subst.
  + left. auto.
  + right. intro. apply pair_equal_spec in H. destruct H. contradiction.
  + right. intro. apply pair_equal_spec in H. destruct H. contradiction.
Qed.

Lemma reverse_act :
  forall (pr : PreRun), forall st : State,
    forall i : nat, forall p,
      (get_action pr st) i = Some p ->
      exists j : nat, exists l l', exists st',
        In p (snd (create_list_from_transition st' (pr j))) /\
          snd (create_list_of_actions st pr i) = l ++ (snd (create_list_from_transition st' (pr j))) ++ l'.
Proof.
  intros pr st.
  assert (
      forall i i', forall p,
        nth_error (snd (create_list_of_actions st pr i)) i' = Some p ->
        exists j : nat, exists l l', exists st',
        In p (snd (create_list_from_transition st' (pr j))) /\ snd (create_list_of_actions st pr i) = l ++ (snd (create_list_from_transition st' (pr j))) ++ l'
    ).
  induction i.
  - intros. simpl in H.
    exists 0. simpl. destruct (pr 0) ; simpl in * ;
    exists [], [] ; exists st ; repeat split.
    + destruct (runGenHandler_ignore st (InputHandler p0)). destruct p1.
      apply nth_error_In in H. auto.
    + destruct (runGenHandler_ignore st (InputHandler p0)).
      destruct p1. simpl in *.
      rewrite app_nil_r. auto.
    + destruct (runGenHandler_ignore st (RecvHandler p0)). destruct p1.
      apply nth_error_In in H. auto.
    + destruct (runGenHandler_ignore st (RecvHandler p0)).
      destruct p1. simpl in *.
      rewrite app_nil_r. auto.
  - intros. simpl in *.
    destruct (create_list_of_actions st pr i) eqn: Heq.
    destruct (create_list_from_transition s (pr (S i))) eqn: Heq0.
    simpl in H. apply nth_error_In, in_app_or in H. destruct H.
    + apply In_nth_error in H. destruct H. simpl in *.
      specialize IHi with x p. apply IHi in H. repeat destruct H.
      exists x0, x1, (x2++l0), x3. split. apply H.
      repeat rewrite app_assoc in *.
      apply <-app_inv_tail_iff. apply H0.
    + apply In_nth_error in H.
      destruct H. simpl in *.
      exists (S i), l, [], s. split.
      eapply nth_error_In. rewrite Heq0. simpl. apply H.
      simpl. apply app_inv_head_iff.
      rewrite Heq0. simpl. rewrite app_nil_r. auto.
  - intros. eapply H.
    unfold get_action in H0.
    destruct (create_list_of_actions st pr i).
    simpl. apply H0.
Qed.

Lemma reverse_recv :
  forall (pr : PreRun), forall st : State,
    forall i : nat, forall p,
      (get_action pr st) i = Some (Recv p) ->
      exists j : nat,
        pr j = backend p.
Proof.
  intros.
  edestruct reverse_act.
  apply H.
  exists x.
  repeat destruct H0.
  apply In_nth_error in H0.
  destruct H0.
  assert (x3 = 0). eapply create_list_from_transition_nth_recv. apply H0.
  subst.
  destruct (pr x) ; simpl in *.
  destruct (runGenHandler_ignore x2 (InputHandler p0)). destruct p1. simpl in H0. inversion H0.
  destruct (runGenHandler_ignore x2 (RecvHandler p0)). destruct p1. simpl in H0. inversion H0. auto.
Qed.

Lemma reverse_send :
  forall (pr : PreRun), forall st : State,
    forall i : nat, forall p,
      (get_action pr st) i = Some (Input p) ->
      exists j : nat,
        pr j = frontend p.
Proof.
  intros.
  edestruct reverse_act.
  apply H.
  exists x.
  repeat destruct H0.
  apply In_nth_error in H0.
  destruct H0.
  assert (x3 = 0). eapply create_list_from_transition_nth_input. apply H0.
  subst.
  destruct (pr x) ; simpl in *.
  destruct (runGenHandler_ignore x2 (InputHandler p0)). destruct p1. simpl in H0. inversion H0. auto.
  destruct (runGenHandler_ignore x2 (RecvHandler p0)). destruct p1. simpl in H0. inversion H0.
Qed.

Lemma ready_satisfies_cond :
  forall pr : PreRun, forall n : Node,
    n < NodeCount ->
    forall i, forall p, forall m, forall r, get_action pr (init_state n) i = Some (Send (p, serialize_partialpacket (Ready m r))) ->

                        BrachaRBStep (st BrachaRBAction (BrachaRBProcess f proc) (e i)) >= 3 /\ (
                                 BrachaRBRecvBufferSize (st BrachaRBAction (BrachaRBProcess f proc) (e i)) (Echo m) >= 2*f+1 \/
                                 BrachaRBRecvBufferSize (st BrachaRBAction (BrachaRBProcess f proc) (e i)) (Ready m) >= f+1
                              )
                   .
Proof.
  auto.
Qed.




Open Scope nat_scope.

Fixpoint compute_action_aux (p : PreRun) (target : nat) (prerun_pointer : nat) (st : State) : option NodeAction :=
  let (tmp, _send) := compute_transition st (p prerun_pointer) in
  let (_out, st') := tmp in
  match target with
    | 0 =>
        match (p prerun_pointer) with
          | inl q => Some (Input q)
          | inr q => Some (Recv q)
        end
    | S target' =>
      if target' <? length _out then
                  Some (Output (nth (target') _out (0, 0, "")))
                else if target' - length _out <? length _send then
                      Some (Send (nth (target' - length _out) _send (0, "")))
                    else
                      compute_action_aux p (target' - length _out - length _send) (prerun_pointer + 1) st'
      end.

Definition compute_action (p : PreRun) (st : State) : Trace NodeAction :=
  fun n => compute_action_aux p n 0 st.

Fixpoint compute_state_aux (p : PreRun) (st : State) (pos : nat) (steps : nat) : State :=
  match steps with
    | 0 => st
    | S steps' =>
        let (tmp, _) := compute_transition st (p pos) in
        let (_, st') := tmp in
        compute_state_aux p st' (pos+1) steps'
  end.

Definition compute_state (p : PreRun) (st : State) (steps : nat) : State :=
  compute_state_aux p st 0 steps.

Definition empty_step :=
  mkCurrentStep
    Buffer.empty
    Buffer.empty
    Buffer.empty
    Buffer.empty
.

Definition init_state (n : nat) :=
  mkState
    NodeCount
    n
    Buffer.empty
    empty_step
.

Definition Run (n : Node) (p : PreRun) := compute_action p (init_state n).

Ltac unfold_run :=
  unfold
         Run,
         compute_action,
         compute_action_aux
.
(*)
Lemma compute_transition_is_compute_state_unfold :
  forall (n : Node) (pr : PreRun),
    forall i,
      compute_transition (compute_state pr (init_state n) i) (pr i) = compute_transition (compute_state pr (init_state n) (i+1)) (pr (i+1)).
Proof.
  intros.
  induction i.
  - unfold compute_transition, compute_state. simpl.*)

(*)
Lemma compute_action_is_compute_state :
  forall (n : Node) (pr : PreRun),
    forall i, forall inter,
      Run n pr i = compute_action_aux pr i inter (compute_state pr (init_state n) inter).
Proof.
  intros n pr i.
  induction i.
  - intros. unfold_run. unfold compute_state, compute_state_aux.



  induction inter.
  - auto.
  - rewrite IHinter. unfold compute_action_aux. destruct i.
    destruct (compute_transition (compute_state pr (init_state n) inter) (pr inter)).
    destruct p.
    destruct (compute_transition (compute_state pr (init_state n) (S inter)) (pr (S inter))).
    destruct p.
    destruct (pr inter).
    unfold Run, compute_action, compute_action_aux, compute_state, compute_state_aux in IHinter.
    simpl in IHinter.

    compute_transition (compute_state pr (init_state n) (S inter)) (pr (S inter)) = compute_transition (compute_state pr (init_state n) inter) (pr inter)


    unfold compute_state, compute_state_aux. simpl.
    destruct inter
    destruct (compute_transition (compute_state pr (init_state n)))
    unfold_run.
    destruct i ; simpl.
*)

Ltac unfold_state :=
  repeat unfold
         compute_state,
         compute_state_aux.

Tactic Notation "unfold_run" "in" hyp(H) :=
  repeat unfold
         Run,
         compute_action,
         compute_action_aux
  in H.

Tactic Notation "unfold_transition" "in" hyp(H) :=
  repeat unfold
         compute_transition in H.

Lemma reverse_recv :
  forall (n : Node) (pr : PreRun),
    let run := Run n pr in
    forall i : nat, forall p,
      run i = Some (Recv p) ->
      exists j : nat,
        pr j = backend p.
Proof.
  intros n pr run i. unfold run. clear run.
  assert (forall k, k <= i -> forall p, Run n pr k = Some (Recv p) -> exists j, pr j = backend p).
  induction i ; intros.
  - assert (k = 0) by lia. subst. exists 0. unfold_run in H0.
    destruct (compute_transition (init_state n) (pr 0)).
    destruct p0.
    destruct (pr 0) ; inversion H0. auto.
  - destruct k. eapply IHi. 2: apply H0. lia.
    unfold_run in H0.
    fold compute_action_aux in H0. simpl in H0.
    destruct (compute_transition (init_state n) (pr 0)).
    destruct p0.
    destruct (k <? length l0). inversion H0.
    destruct (k - length l0 <? length l).
    inversion H0.
    eapply IHi ; cycle 1.
    unfold_run.

Lemma send_result_of_transition :
  forall (n : Node) (pr : PreRun),
    let run := Run n pr in
    forall i : nat, forall p,
      run i = Some (Output p) ->
      exists j : nat,
        let st := compute_state pr (init_state n) j in
        let (tmp, _) := compute_transition st (pr j) in
        let (_out, _) := tmp in
        In p _out.
Proof.
  intros n pr run. unfold run in *. unfold Run, compute_action.
  assert (forall i, forall k, forall p, forall inter, k <= i ->
               compute_action_aux pr i inter (compute_state pr (init_state n) inter) = Some (Output p) ->
               exists j : nat, let st := compute_state pr (init_state n) j in let (tmp, _) := compute_transition st (pr j) in let (_out, _) := tmp in In p _out
         ).
  induction i ; intros.
  - unfold run in H0 ; unfold_run in H0. exists 0. simpl. unfold_state. assert (k = 0). lia. subst.
    destruct (compute_transition (init_state n) (pr 0)). destruct p0. destruct (pr 0) ; inversion H0.
  - destruct k. eapply IHi. 2: apply H0. lia.
    unfold run in H0 ; unfold_run in H0. simpl in H0.
    destruct (compute_transition (init_state n) (pr 0)) eqn: Htrans.
    destruct p0 eqn: Hp0.
    destruct (k <? length l0) eqn: Hlength. inversion H0. subst.
    exists 0. simpl. unfold_state. rewrite Htrans.
    apply nth_In. simpl_arith_bool. auto.
    destruct (k - length l0 <? length l). inversion H0.
    fold compute_action_aux in H0.




    fold compute_action_aux in H, IHi. simpl in H


    destruct (compute_state pr (init_state n) i).
    simpl.




  intros n pr run.
  induction i.
  - intros. exists 0. simpl.
    destruct (compute_transition (compute_state pr (init_state n) 0) (pr 0)) eqn: Heq.
    destruct p0 eqn : Heq0.
    induction l0 ; intros ; unfold run in H ; unfold_run in H ; unfold compute_state in Heq ; simpl in Heq ;
    rewrite Heq in H.
    destruct (pr 0) ; inversion H.
    destruct (pr 0) ; inversion H.
  - intros.


    
    destruct (compute_state pr (init_state n) 0). simpl.
    unfold run in H. unfold_run in H. simpl in H.
    case_eq (pr 0) ; intros ; rewrite H0 in *.
    destruct (runGenHandler_ignore (init_state n) (InputHandler p0)) in H.
    destruct p1 in H. inversion H.
    destruct (runGenHandler_ignore (init_state n) (RecvHandler p0)) in H.
    destruct p1 in H. inversion H.
  - intros. unfold run in H. unfold_run in H. simpl in H.
    destruct (pr 0) eqn: Heq0.
    destruct (runGenHandler_ignore (init_state n) (InputHandler p0)) eqn: Hrun.
    destruct p1.
    destruct (i <? length l0). inversion H.
    destruct (i - length l0 <? length l). inversion H.





  
  forall run : Run,
    forall p,
    forall i : nat,
      run.1 i = Some (Send p) ->
      exists j : nat,
        k

Lemma echo_satisfies_cond :
  forall ps : PreRun, forall n : Node,
    n < NodeCount ->
    let s := Run n ps in
    forall i, forall p, forall m, s i = Some (Send (p, m)) -> True.
Proof.
  auto.
Qed.











Fixpoint compute_pos_and_offset_from_prerun (p : PreRun) (limit : nat) (prerun_pointer : nat) (st : State) :=
  if limit =? 0 then
    (prerun_pointer, 0)
  else
    match (p prerun_pointer) with
      | left m =>
          let () := runGenHandler_ignore st InputHandler
      | right (n, m) =>.
    let shift :=


    compute_run_from_prerun_up_to_n p (
        limit -

      ) (prerun_pointer+1)

Definition get_prerun_state_from_nat (p : PreRun) (n : nat) :=


Definition run_from_prerun (p : PreRun) (n : nat) :
$
