Require Import Arith.
Require Import PArray List ListSet.
Require Import monad.
Require Import Lia.
Require Import common.tactic.

Definition Message := list nat.

Parameter NodeCount : nat.
Parameter f : nat.
Parameter IdType : Type.
Hypothesis eq_dec : forall p p' : IdType, {p = p'}+{p <> p'}.
Definition Node := IdType.
Definition Round := nat.

Parameter MaxRound : Round.

Definition InputAction : Type := (Round * Message)%type.

Inductive PacketType : Type :=
  | Init
  | Echo
  | Ready
.

Definition PartialPacket : Type :=
  PacketType*Round*Message.

Record State :=
  mkState {
    id : IdType;
    rounds : nat;
    process_ids : list IdType;
    num_process : nat;
    message_recv : array (option Message);
    current_step : array nat;
  }.

Definition Handler := GenHandler (Node*Message) State (Node*Round*Message) unit.

Import ListNotations.

Fixpoint get_index_rec (pos : nat) (id : IdType) (l : list IdType) :=
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
        s.(message_recv).[ (r * ( 3 * s.(num_process) ) + t_unpack * s.(num_process) + p) ]
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

          (PArray.set s.(message_recv) (r * ( 3 * s.(num_process) ) + t_unpack * s.(num_process) + p) (Some m))
          s.(current_step)
  end.
