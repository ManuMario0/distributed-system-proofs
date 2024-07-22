Require Import Fin.
Require Import PArray Init.Byte.
Require Import framework.monad.

(***************************************
  Definition of core objects
***************************************)

Definition fin := Fin.t.

Definition NodeSet (n : nat) := fin n.
Definition Message := array byte.

(***************************************
  Definition of trace
***************************************)

(* Main action type, it describes a simple I/O interface *)
Inductive IAction {I O : Type} :=
  | ISend : O -> IAction
  | IRecv : I -> IAction
.

(*

An action of a node is :
- either an frontend action (output something to the user/upper level protocol)
- either a backend action (output something to the network/lower level protocol)

For compatibility, we call IOutput and IInput the equivalent of ISend and IRecv
to describe the frontend interface, where IInput is and input for the protocol
and IOutput is an output of the protocol.

*)
Definition NodeAction {I O I' O'} := (@IAction I O + @IAction I' O')%type.

Notation "'frontend'" := inl.
Notation "'backend'" := inr.
Notation "'IOutput'" := IRecv.
Notation "'IInput'" := ISend.
Notation "'Send' m" := (backend (ISend m)) (at level 100).
Notation "'Recv' m" := (backend (IRecv m)) (at level 100).
Notation "'Output' m" := (frontend (IOutput m)) (at level 100).
Notation "'Input' m" := (frontend (IInput m)) (at level 100).

(* The actions of a model are actions of nodes labeled with a node identifier n *)
Definition ModelAction {I O I' O'} (n : nat) := (NodeSet n * @NodeAction I O I' O')%type.

(* A trace is a sequence of actions *)
Definition Trace (Action : Type) := nat -> option Action.

(* TransformTrace is a simple wrapper to apply functions on traces *)
Definition TransformTrace {A B : Type} (f : A -> option B) (t : Trace A) : Trace B :=
  (fun i => match t i with
           | Some a => f a
           | None => @None B
        end).

(*
  InvarientTrace states that the property P holds at every step of the trace,
  NOTE : might have to improve the definition to take the history as an input for P ...
 *)
Definition InvarientTrace {A : Type} (P : A -> Prop) (t : Trace A) : Prop :=
  forall i, match t i with
         | Some a => P a
         | _ => True
      end.

(* transform a trace on backend actions to a trace on model actions *)
Definition InterfaceTraceAsBackend {I O I' O'} {n : nat} : Trace (NodeSet n * IAction)%type -> Trace (@ModelAction I O I' O' n) :=
  TransformTrace (fun a => let '(p, node_act) := a in Some (p, backend node_act)).

(* a specification is a property on actions *)
Definition Specification (Action : Type) := Trace Action -> Prop.

(* An interface is a specification of the behaviour of an interface with multiple nodes *)
Definition Interface {I O} := forall i : nat, Specification (NodeSet i * @IAction I O)%type.

(* project the trace on the actions of one node *)
Definition ProjectTraceOnNode
  {I O I' O'}
  {n : nat}
  (p : fin n) :
  Trace (@ModelAction I O I' O' n) -> Trace (NodeAction) :=
  TransformTrace (fun a => let '(_, node_act) := a in Some (node_act)).

(* project the trace on the actions of the backend of the nodes *)
Definition ProjectTraceOnBackend
  {I O I' O'}
  {n : nat} :
  Trace (@ModelAction I O I' O' n) -> Trace (NodeSet n * IAction)%type :=
  TransformTrace (
      fun a => let '(p, node_act) := a in
            match node_act with
              | backend a' => Some (p, a')
              | _ => None
            end
    ).

(***************************************
  Now we define a intermediaire
  representation for the proofs :
  The designer have to provide two
  functions : a input handler (for the
  external interface) and a recv handler
  (for the backend interface)
***************************************)

Section local_representation.
  Import monad.
  Import Lia.

  Variable InputType OutputType RecvType SendType : Type.
  Variable State : Type.
  Definition Handler := GenHandler SendType State OutputType unit.
  Variable InputHandler : InputType -> Handler.
  Variable RecvHandler : RecvType -> Handler.

  (* We smash both inputs and recv types together *)
  Definition input_types := (InputType+RecvType)%type.

  Definition PreRun : Type := nat -> input_types.

  (* This function compute a transition given an input *)
  Definition compute_transition
    (st : State)
    (i : input_types) :=
    match i with
    | frontend q =>
        runGenHandler_ignore st (InputHandler q)
    | backend q =>
        runGenHandler_ignore st (RecvHandler q)
    end.

  Require Import List.
  Import ListNotations.

  (* this is the model of a node of our current protocol *)
  Definition SpecializedNodeModel :=
    @NodeAction OutputType InputType RecvType SendType.

  (* Transforms a list of inputs values into a list of input actions *)
  Fixpoint out_to_model (out : list OutputType) : list SpecializedNodeModel :=
    match out with
    | [] => []
    | a::b => (Output a)::(out_to_model b)
    end.

  (* Transforms a list of recv values into a list of recv actions *)
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

  (* This local function create a list of action from an action and an input *)
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
    simpl in H. destruct (runGenHandler_ignore st (InputHandler i)). destruct p0.
    simpl in H.
    apply nth_error_In, in_app_or in H.
    destruct H. apply out_of_model_no_recv in H. contradiction.
    apply send_to_model_no_recv in H. contradiction.
    simpl in H. destruct (runGenHandler_ignore st (RecvHandler r)). destruct p0.
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
    simpl in H. destruct (runGenHandler_ignore st (InputHandler i)). destruct p0.
    simpl in H.
    apply nth_error_In, in_app_or in H.
    destruct H. apply out_of_model_no_input in H. contradiction.
    apply send_to_model_no_input in H. contradiction.
    simpl in H. destruct (runGenHandler_ignore st (RecvHandler r)). destruct p0.
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

  (*
    We want to transform a list of input values in a sequence of
  *)




  (*
    from a list of input values, it creates a sequence of actions representing the
    actions of the protocol as follows :

    val1 -> val2 -> val3 -> ...
              |
              |
              |
              v
    Recv(val1) ++ output (exec Recvhandler on val1) ++ send (exec Recvhandler on val1) -> Input(val2) -> ...

  The trick here is to represent only a prefix of the run long enough to be able to get after
  a actual execution and do proof on it
   *)
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
      destruct (runGenHandler_ignore st (InputHandler i)) eqn: Heq. destruct p eqn: Heq0.
      subst.
      exists []. exists st. rewrite Heq. simpl. auto.
      destruct (runGenHandler_ignore st (RecvHandler r)) eqn: Heq. destruct p eqn: Heq0.
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
      intros.
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

  (*
    Extract the nth action from a run
  *)
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

  Import Arith.

  Hypothesis recv_dec :
    forall p p' : RecvType, {p = p'}+{p <> p'}.

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
      + destruct (runGenHandler_ignore st (InputHandler i)). destruct p0.
        apply nth_error_In in H. auto.
      + destruct (runGenHandler_ignore st (InputHandler i)).
        destruct p0. simpl in *.
        rewrite app_nil_r. auto.
      + destruct (runGenHandler_ignore st (RecvHandler r)). destruct p0.
        apply nth_error_In in H. auto.
      + destruct (runGenHandler_ignore st (RecvHandler r)).
        destruct p0. simpl in *.
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
    destruct (runGenHandler_ignore x2 (InputHandler i0)). destruct p0. simpl in H0. inversion H0.
    destruct (runGenHandler_ignore x2 (RecvHandler r)). destruct p0. simpl in H0. inversion H0. auto.
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
    destruct (runGenHandler_ignore x2 (InputHandler i0)). destruct p0. simpl in H0. inversion H0. auto.
    destruct (runGenHandler_ignore x2 (RecvHandler r)). destruct p0. simpl in H0. inversion H0.
  Qed.

End local_representation.

(***************************************
  Later work
***************************************)

(*)
Record Model (n : nat) :=
  mkModel {
      Process : Type;
      ModelSpec : Type;
      TranslateNodeSpec : Specification NodeAction -> (NodeSet n -> Process);
      Translate
      TranslateNetworkSpec : forall n : nat, Specification (ModelAction n) -> ModelSpec;
      Certificate : (NodeSet n -> Process) -> ModelSpec -> ModelSpec -> Prop;
    }.*)

(*)
Record Model :=
  mkModel {
      Certify : Specification NodeAction -> Interface -> Interface -> Prop
  }
.*)

  (*)
Arguments Process {n}.
Arguments ModelSpec {n}.
Arguments TranslateNodeSpec {n}.
Arguments TranslateNetworkSpec {n}.
Arguments Certificate {n}.*)

Module Type Protocol.
  Parameter I O I' O' : Type.
  Parameter Frontend : @Interface I O.
  Parameter Backend : @Interface I' O'.
  Parameter State : Type.
  Parameter input_handler output_handler : Type.
  Parameter Spec : Specification (@NodeAction I O I' O').
  Parameter Consistency : Type.
  (*Parameter Model : Model.
  Parameter Certification : Model.(Certify) Spec Backend Frontend.*)
  (*)
    forall n : nat, let m := Model n in
             m.(Certificate)
                     (m.(TranslateNodeSpec) Spec)
                     (m.(TranslateNetworkSpec) n (fun t => Backend n (ProjectTraceOnInterface backend t)))
                     (m.(TranslateNetworkSpec) n (fun t => Frontend n (ProjectTraceOnInterface frontend t)))
  .*)
End Protocol.


Inductive ActionClass :=
  | Intern_act
  | Output_act
  | Input_act
  | Unused_act
.

Record AIOA (ActionPool : Type) :=
  mkAIOA {
    Classifier : ActionPool -> ActionClass;
    Spec : Specification ActionPool;
    UnusedHyp :
      forall t : Trace ActionPool,
        Spec t -> InvarientTrace (fun a => Classifier a <> Unused_act) t
  }
.

Arguments Spec {ActionPool}.
Arguments Classifier {ActionPool}.

(*)

Definition AIOA_TranslateNodeSpec {I O I' O'} {n : nat} (s : Specification NodeAction) (p : NodeSet n) : AIOA (@ModelAction I O I' O' n).
  refine (
    mkAIOA
      (ModelAction n)
      (
        fun a : ModelAction n =>
          let (p', act) := a in
          if eq_dec p p' then
            match act with
              | Output _ | Send _ => Output_act
              | _ => Input_act
            end
          else Unused_act
      )
      (
        fun t : Trace (ModelAction n) =>
          (forall n, forall p', p <> p' -> forall act, t n <> Some (p', act)) /\
          s (TransformTrace
              (fun a : ModelAction n =>
                  let (p', act) := a in
                  if eq_dec p p' then
                    Some act
                  else
                    None)
              t
            )
      )
    _).
  intros.
  unfold InvarientTrace. intros.
  case_eq (t i) ; intros ; auto.
  intros. destruct m. case (eq_dec p n0) ; intros ; subst.
  case n1 ; intros ; case i0 ; intros ; discriminate.
  destruct H. specialize H with i n0 n1. apply H in n2.
  contradiction.
Defined.

Definition AIOA_from_backend_spec_to_AIOA {n : nat} (i : Interface) : AIOA (ModelAction n).
  refine (
      mkAIOA
        (ModelAction n)
        (
          fun a : ModelAction n =>
            let (_, act) := a in
            match act with
              | Send _ => Input_act
              | Recv _ => Output_act
              | _ => Unused_act
            end
        )
        (
          fun t : Trace (ModelAction n) =>
            (forall n, forall p, forall a, t n <> Some (p, frontend a)) /\
              (i n) (TransformTrace
                (fun a : ModelAction n =>
                  let (p, act) := a in
                    match act with
                      | backend ia => Some (p, ia)
                      | _ => None
                    end
                )
                t
            )
        )
        _
    ).
  intros.
  unfold InvarientTrace.
  intro. case_eq (t i0) ; auto ; intros.
  destruct m. case_eq n1 ; intros.
  - destruct H. specialize H with i0 n0 i1.
    subst. contradiction.
  - case i1 ; intro ; discriminate.
Defined.

Definition Compose
  {CompType : Type}
  {ActionPool : Type}
  (non_empty : CompType)
  (f : CompType -> AIOA ActionPool)
  (ActClassDecideable : forall c : ActionClass, forall a : ActionPool, {forall t : CompType, (f t).(Classifier) a <> c}+{exists t : CompType, (f t).(Classifier) a = c})
  : AIOA ActionPool.
  refine (
      mkAIOA
        ActionPool
        (
          fun a : ActionPool =>
            match (ActClassDecideable Output_act a, ActClassDecideable Input_act a) with
              | (right _, _) => Output_act
              | (left _, right _) => Input_act
              | _ => if (ActClassDecideable Intern_act a) then Unused_act else Intern_act
            end
        )
        (
          fun t : Trace (ActionPool) =>
            forall c : CompType, (f c).(Spec) t
        )
        _
    ).
  intros. unfold InvarientTrace.
  intro. case_eq (t i) ; auto ; intros.
  case (ActClassDecideable Output_act a) ; try discriminate ; intros.
  case (ActClassDecideable Input_act a) ; try discriminate ; intros.
  case (ActClassDecideable Intern_act a) ; try discriminate ; intros.
  assert (forall comp : CompType, InvarientTrace (fun a => Classifier (f comp) a <> Unused_act) t).
  intro. apply (UnusedHyp ActionPool). apply H.
  intro.
  case_eq (Classifier (f non_empty) a); intros.
  - eapply n1. apply H3.
  - eapply n. apply H3.
  - eapply n0. apply H3.
  - unfold InvarientTrace in H1. specialize H1 with non_empty i. rewrite H0 in H1. eapply H1. apply H3.
Defined.

Inductive CompType (n : nat) :=
  | Node : NodeSet n -> CompType n
  | Network : CompType n.

Arguments Node {n}.
Arguments Network {n}.

Definition f
  {n : nat}
  (net : AIOA (ModelAction n))
  (nodes : NodeSet n -> AIOA (ModelAction n))
  (comp : CompType n) :
  AIOA (ModelAction n) :=
  match comp with
    | Network => net
    | Node p => nodes p
  end.

Definition AIOA_from_spec
  (n : nat)











Definition Certificate :

.
*)
