Require Import Uint63.
Require Import PArray List ListSet.
Require Import monad.
Require Import Lia.
Require Import common.tactic.
Require Import multidim_parray.

Definition Message := list int.

Lemma message_eq_dec :
  forall m m' : Message, {m = m'}+{m <> m'}.
Proof.
  intros.
  apply list_eq_dec.
  intros.
  case_eq (x =? y)%uint63 ; intro.
  apply eqb_spec in H. auto.
  assert ((x =? y) <> true). rewrite H. discriminate.
  assert (x <> y). intro. apply H0.
  apply eqb_spec. auto. auto.
Qed.

Parameter NodeCount : nat.
Parameter f : nat.
Parameter IdType : Type.
Hypothesis eq_dec : forall p p' : IdType, {p = p'}+{p <> p'}.
Definition Node := IdType.
Definition Round := int.

Parameter MaxRound : Round.

Definition InputAction : Type := (Round * Message)%type.

Inductive PacketType : Type :=
  | Init
  | Echo
  | Ready
.

Definition PartialPacket : Type :=
  PacketType*Round*Message.

Local Open Scope uint63_scope.

Record State :=
  mkState {
    id : IdType;
    rounds : int;
    process_ids : list IdType;
    num_process : int;
    message_recv : @MultiArray (option Message);
    current_step : @MultiArray int;
  }.

Definition Handler := GenHandler (Node*Message) State (Node*Round*Message) unit.

Import ListNotations.

Fixpoint get_index_rec (pos : int) (id : IdType) (l : list IdType) :=
  match l with
    | [] => None
    | h::t =>
        if eq_dec h id then
          Some pos
        else
          get_index_rec (pos+1) id t
  end.

Definition get_index (id : IdType) (s : State) :=
  get_index_rec 0 id s.(process_ids).

Definition get_message (r : Round) (t : PacketType) (_p : IdType) (s : State) :=
  match get_index _p s with
    | None => None
    | Some p =>
        let t_unpack := match t with
                        | Init => 0
                        | Echo => 0
                        | Ready => 1
                        end in
        match get_val [r ; t_unpack ; p] s.(message_recv) with
          | None => None
          | Some a => a
        end
  end.

Definition set_message (r : Round) (t : PacketType) (_p : IdType) (m : Message) (s : State) :=
  match get_index _p s with
    | None => s
    | Some p =>
        let t_unpack := match t with
                        | Init => 0
                        | Echo => 0
                        | Ready => 1
                        end in
        mkState
          s.(id)
          s.(rounds)
          s.(process_ids)
          s.(num_process)
          (set_val (Some m) [r ; t_unpack ; p] s.(message_recv))
          s.(current_step)
  end.

Require Import ZArith.

Section Message_handler.
  Open Scope Z_scope.

  Require Import Lra.

  Variable state : State.
  Hypothesis MaxRound_not_null : to_Z MaxRound > 0.
  Hypothesis process_id_not_empty : to_Z state.(num_process) > 0.
  Hypothesis num_process_is_process_ids_length :
    to_Z state.(num_process) = Z.of_nat (length state.(process_ids)).
  Hypothesis process_and_round_not_too_big :
    size_Z (format (message_recv state)) < wB.
  Hypothesis format_is_correct :
    format (message_recv state) = [MaxRound ; 3%uint63 ; state.(num_process)].
  Hypothesis array_is_of_size_format :
    PArray.length (data (message_recv state)) = size (format (message_recv state)).

  Remark to_Z_3 : to_Z 3 = 3.
  Proof.
    cbv. auto.
  Qed.

  Remark get_index_rec_invariant :
    forall proc, forall i j : int, forall id : IdType,
      get_index_rec i id proc = Some j ->
      to_Z i + Z.of_nat (length proc) < wB ->
      0 <= to_Z i ->
      to_Z j < Z.of_nat (length proc) + to_Z i.
  Proof.
    induction proc.
    - intros.
      simpl in H. inversion H.
    - intros. simpl in H. destruct (eq_dec a id0).
      + inversion H. subst.
        assert (length (id0::proc) = length proc+1)%nat. simpl. lia.
        rewrite H2 in *. clear H2. lia.
      + assert (length (a::proc) = length proc+1)%nat. simpl. lia.
        rewrite H2 in *. clear H2.
        apply IHproc in H. rewrite add_spec in H.
        rewrite Nat2Z.inj_add in *. rewrite to_Z_1 in *. simpl in *.
        rewrite Z.mod_small in H. lia.
        assert (0 <= Z.of_nat (length proc)). apply Nat2Z.is_nonneg.
        nia.
        rewrite add_spec. rewrite Z.mod_small. rewrite to_Z_1. lia.
        rewrite to_Z_1. nia.
        rewrite add_spec. rewrite to_Z_1. rewrite Z.mod_small.
        lia. nia.
  Qed.

  Remark get_index_limited_by_length :
    forall id : IdType, forall i : int, get_index id state = Some i -> to_Z i < to_Z state.(num_process).
  Proof.
    intros.
    unfold get_index in H.
    apply get_index_rec_invariant in H.
    rewrite to_Z_0 in H. rewrite num_process_is_process_ids_length. lia.
    rewrite to_Z_0. simpl. rewrite <-num_process_is_process_ids_length.
    assert (0 <= to_Z (num_process state) < wB). apply to_Z_bounded.
    nia.
    rewrite to_Z_0. lia.
  Qed.

  Remark get_index_rec_is_not_none_if_present :
    forall l p i, In p l -> get_index_rec i p l <> None.
  Proof.
    induction l.
    - simpl. auto.
    - simpl. intros.
      destruct H.
      + subst.
        destruct (eq_dec p p). discriminate.
        contradiction.
      + destruct (eq_dec a p). discriminate.
        apply IHl. auto.
  Qed.

  Lemma get_set_message_same :
    forall r : Round, forall t : PacketType, forall p : IdType, forall m : Message,
      to_Z r < to_Z MaxRound ->
      In p state.(process_ids) ->
      get_message r t p (set_message r t p m state) = Some m.
  Proof.
    intros.
    unfold get_message, set_message, get_index.
    destruct (get_index_rec 0 p (process_ids state)) eqn: Heq.
    simpl. rewrite Heq.
    rewrite get_set_same ; auto.
    rewrite format_is_correct.
    assert (size_Z [MaxRound; 3%uint63; num_process state] =
              (to_Z MaxRound) * (to_Z 3 * to_Z (num_process state))).
    simpl. auto. rewrite H1. rewrite to_Z_3. nia.
    unfold well_formated. simpl.
    rewrite format_is_correct.
    apply <-ltb_spec in H. rewrite H.
    assert (to_Z i < to_Z (num_process state)).
    eapply get_index_limited_by_length.
    unfold get_index. apply Heq.
    apply <-ltb_spec in H1. rewrite H1.
    destruct t ; simpl ; auto.
    contradict Heq. apply get_index_rec_is_not_none_if_present. auto.
  Qed.
End Message_handler.

Definition get_step_index (r : Round) (p : int) (s : State) :=
  match get_val [r ; p] s.(current_step) with
    | None => 0
    | Some q => q
  end
.

Definition set_step_index (v : int) (r : Round) (p : int) (s : State) :=
  mkState
    s.(id)
    s.(rounds)
    s.(process_ids)
    s.(num_process)
    s.(message_recv)
    (set_val v [r ; p] s.(current_step)).

Definition get_step (r : Round) (_p : IdType) (s : State) :=
  match get_index _p s with
    | None => 0
    | Some p =>
        get_step_index r p s
  end.

Definition increase_step (r : Round) (_p : IdType) (s : State) :=
  match get_index _p s with
    | None => s
    | Some p =>
        set_step_index (get_step_index r p s + 1) r p s
  end.

Definition set_step (r : Round) (_p  : IdType) (step : int) (s : State) :=
  match get_index _p s with
    | None => s
    | Some p =>
        set_step_index step r p s
  end.

Section Step_handler.
  Open Scope Z_scope.

  Require Import Lra.

  Variable state : State.
  Hypothesis MaxRound_not_null : to_Z MaxRound > 0.
  Hypothesis process_id_not_empty : to_Z state.(num_process) > 0.
  Hypothesis num_process_is_process_ids_length :
    to_Z state.(num_process) = Z.of_nat (length state.(process_ids)).
  Hypothesis process_and_round_not_too_big :
    size_Z (format (current_step state)) < wB.
  Hypothesis format_is_correct :
    format (current_step state) = [MaxRound ; state.(num_process)].
  Hypothesis array_is_of_size_format :
    PArray.length (data (current_step state)) = size (format (current_step state)).

  Lemma get_set_step_index_same :
    forall m r p,
      to_Z r < to_Z MaxRound ->
      to_Z p < to_Z state.(num_process) ->
      get_step_index r p (set_step_index m r p state) = m.
  Proof.
    intros.
    unfold get_step_index, set_step_index.
    simpl.
    rewrite get_set_same ; auto.
    rewrite format_is_correct. simpl. nia.
    unfold well_formated. simpl.
    rewrite format_is_correct.
    apply <-ltb_spec in H. apply <-ltb_spec in H0.
    rewrite H, H0. simpl ; auto.
  Qed.

  Lemma get_set_step_same :
    forall m r p,
      to_Z r < to_Z MaxRound ->
      In p state.(process_ids) ->
      get_step r p (set_step r p m state) = m.
  Proof.
    intros.
    unfold get_step, set_step, get_index.
    destruct (get_index_rec 0 p (process_ids state)) eqn: Heq.
    simpl. rewrite Heq.
    rewrite get_set_step_index_same ; auto.
    eapply get_index_limited_by_length ; auto.
    unfold get_index. apply Heq.
    contradict Heq. apply get_index_rec_is_not_none_if_present.
    auto.
  Qed.
End Step_handler.

Open Scope monad_scope.

Fixpoint broadcast_rec (m : Message) (l : list IdType) (id : IdType) : Handler :=
  match l with
    | a::t =>
        (if eq_dec a id then
          send (a, m)
        else
          nop) ;; broadcast_rec m t id
    | [] => nop
  end
.

Definition broadcast (m : Message) (s : State) : Handler :=
  broadcast_rec m s.(process_ids) s.(id).

Definition serialize_packet (p : PartialPacket) :=
  let '(t, r, m) := p in
  match t with
    | Init => 0::r::m
    | Echo => 1::r::m
    | Ready => 2::r::m
  end
.

Definition deserialize_packet (_m : Message) :=
  match _m with
    | [] => None
    | a::[] => None
    | a::r::m =>
        if a =? 0 then
          Some (Init, r, m)
        else if a =? 1 then
          Some (Echo, r, m)
        else if a =? 2 then
          Some (Ready, r, m)
        else None
  end
.

Theorem deserialize_serialize_packet_is_id :
  forall p, deserialize_packet (serialize_packet p) = Some p.
Proof.
  intros.
  unfold deserialize_packet, serialize_packet.
  destruct p. destruct p. destruct p ; auto.
Qed.

Definition InputHandler (_m : Round*Message) : Handler :=
  s <- get ;;
  let (round, m) := _m in
  if get_step round s.(id) s =? 0 then
    (* We didn't processed this round yet *)
    (* broadcast to everyone but us *)
    broadcast (serialize_packet (Init, round, m)) s ;;
    (* Now, broadcast the echo and update our local view *)
    broadcast (serialize_packet (Echo, round, m)) s ;;
    put (set_step round s.(id) 1 (set_message round Echo s.(id) m s))
  else nop
.

Definition process_init_packet
  (n : Node)
  (r : Round)
  (m : Message)
  (s : State) : Handler :=
  if get_step r n s =? 0 then
    (* We increase current step and set our own echo to m *)
    put (set_message r Echo n m (set_step r n 1 s)) ;;
    broadcast (serialize_packet (Echo, r, m)) s
  else
    (* This packet is invalid *)
    nop
.

Definition acknowledge_recv
  (n : Node)
  (t : PacketType)
  (r : Round)
  (m : Message)
  (s : State) : Handler :=
  put (set_message r t n m s)
.

Fixpoint count_occurences_rec (r : Round) (pt : PacketType) (m : Message) (s : State) (l : list IdType) :=
  match l with
    | [] => 0
    | h::t =>
        match get_message r pt h s with
          | None => count_occurences_rec r pt m s t
          | Some m' =>
              if message_eq_dec m' m then
                1 + count_occurences_rec r pt m s t
              else
                count_occurences_rec r pt m s t
        end
  end
.

Definition count_occurences (r : Round) (pt : PacketType) (m : Message) (s : State) :=
  count_occurences_rec r pt m s s.(process_ids).

Definition RecvHandler (_m : Node*Message) : Handler :=
  s <- get ;;
  let (n, m_pack) := _m in
  match deserialize_packet m_pack with
    | None => nop
    | Some (t, r, m) =>
      match t with
        | Init =>
            process_init_packet n r m s
        | Echo =>
            acknowledge_recv n Echo r m s ;;
            let st := get_step r n s in
            (* we are interested in echos only in step 0 and 1 *)
            if (st =? 0)%uint63 then
              (* in this case, we broadcast an Echo as well as a Ready *)
              (* we also have to update the step and the network view accordingly *)

      end
  end
.
