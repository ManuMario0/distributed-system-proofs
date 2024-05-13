Require Import Coq.Sets.Ensembles.
Require Import RelationClasses.
Require Import List.
Require Import common.LTL.
Require Import Nat.
Require Import Arith.
Require Import Bool.
Require Import Classes.Equivalence.
Require Import Relations.Relation_Definitions.
Require Import common.tactic.
Import ListNotations.
Import Ensembles.
Require Import Lia.

Section IOA.
  Declare Scope IOADef_scope.

  Set Implicit Arguments.

  Variable ActionPool : Set.

  Inductive ActionType : Set :=
  | Intern : ActionType
  | Output : ActionType
  | Input : ActionType
  | Unused : ActionType. (* We want this one because I want to use action pools,
                            therefore some actions might not be used for a
                            particular automaton
                            It makes it also easier for the creation and the
                            specification fo the attacker
                            The definition of the interface will be more precise and the proof will
                            mostlikely be eaiser
                          *)

  Record IOADef : Type :=
    mkIOADef {
        State : Set;
        Action : Set := ActionPool;
        ActionClass : Action -> ActionType;
        Start : State -> Prop;
        Transition : State -> Action -> State -> Prop;
        UnusedActionHyp :
          forall act : ActionPool, ActionClass act = Unused -> forall st st' : State, ~ Transition st act st'
      }.

  Definition IOAType : Type := IOADef.

  Unset Implicit Arguments.

  Record ExecSection (A : IOAType) : Type :=
    mkExecSection {
        st : A.(State);
        opt_act : option (Action A);
        st' : A.(State);
        is_well_formed :
        match opt_act with
          | Some act => A.(Transition) st act st'
          | None => st = st'
        end
      }.

  Set Implicit Arguments.

  Definition ActionEnabledInState {A : IOAType} (act : Action A) (st : State A) : Prop :=
    exists st' : State A, Transition st act st'.

  Definition ActionEnabledAlways {A : IOAType} (act : Action A) : Prop :=
    forall st : State A, ActionEnabledInState act st.

  Definition InternEnabled {A : IOAType} : Prop :=
    forall act : Action A, ActionClass act = Intern -> ActionEnabledAlways act.
(*)
  Definition TaskEnabled {A : IOAType} (t : Task A) (st : State A) : Prop :=
    exists (act : Action A) (st' : State A),
      TaskClass act = t ->
      Transition st act st' ->
      ActionEnabledInState act st.*)

  Definition ExecFragmentType {A : IOAType} : Type := Run (ExecSection A).

  Definition ExecFragment {A : IOAType} (s : ExecFragmentType (A := A)) : Prop :=
    forall i : nat, st' A (s i) = st A (s (i+1)).

  Definition Exec {A : IOAType} (s : ExecFragmentType) : Prop :=
    ExecFragment s /\ Start A (st A (s 0)).

  Open Scope ltl_scope.

  Definition FairFragment {A : IOAType} (s : ExecFragmentType) : Prop :=
    forall a : Action A,
      s $ 0 |= (IM (N (fun section : ExecSection A => opt_act A section = Some a))) \/
        s $ 0 |= (IM (N (fun section : ExecSection A => forall st'0 : State A, ~ Transition (st A section) a st'0))).

  Definition Event {A : IOAType} (_act : Action A) (s : ExecFragmentType) : Prop :=
    s $ 0 |= F (N (fun section : ExecSection A => section.(opt_act A) = Some _act)).

  Close Scope ltl_scope.

  Definition CombinedAction (A B : IOAType) : Type := Action A * Action B.

  Inductive EmptyTask : Type :=
  | Emtpy : EmptyTask.

  Hypothesis eq_dec : forall A : IOAType, forall x y : Action A, {x = y} + {x <> y}.

  Lemma existence_of_first_state_dec (A : IOAType) :
    forall e : ExecFragmentType, forall P : ExecSection A -> bool, forall i : nat,
    {forall j : nat, j < i -> P (e j) = false}+{exists j : nat, j < i /\ P (e j) = true}.
  Proof.
    intros.
    induction i.
    left. lia.
    destruct IHi.
    case_eq (P (e i)) ; intros.
    right. exists i. auto.
    left. intros. case_eq (j =? i) ; intro ; simpl_arith_bool.
    subst. auto.
    apply e0. lia.
    right. destruct e0. exists x. split. lia. apply H.
  Qed.

  Lemma existence_of_first_state_for_property {A : IOAType} :
    forall e : ExecFragmentType, forall P : ExecSection A -> bool, forall i : nat,
      P (e i) = true ->
      exists i : nat, P (e i) = true /\ forall j : nat, j < i -> P (e j) = false.
  Proof.
    intros.
    assert (forall i : nat, forall k, k <= i -> P (e k) = true ->
      exists i : nat, P (e i) = true /\ forall j : nat, j < i -> P (e j) = false).
    induction i0 ; intros.
    exists k. split. auto. lia.
    destruct existence_of_first_state_dec with A e P k.
    exists k. auto.
    destruct e0. apply IHi0 with x.
    lia. apply H2.
    apply H0 with i i ; auto.
  Qed.

  Definition CompositionHyp (A B : IOAType) : Prop :=
    forall act : Action A, forall st st' : State A,
      Transition st act st' -> st <> st' -> ActionClass act = Intern -> (forall st_b st_b' : State B, ~ (Transition st_b act st_b')).

  Lemma CompositionUnusedActionHyp (A B : IOAType) :
    forall act : ActionPool,
      match ActionClass (i := A) act with
      | Intern => match ActionClass (i := B) act with
                 | Output => Output
                 | Input => Input
                 | _ => Intern
                 end
      | Output => Output
      | Input => match ActionClass (i := B) act with
                | Output => Output
                | _ => Input
                end
      | Unused => match ActionClass (i := B) act with
                 | Intern => Intern
                 | Output => Output
                 | Input => Input
                 | Unused => Unused
                 end
      end = Unused ->
      forall st st' : State A * State B,
        ~
          (let (st_A, st_B) := st in
           let (st_A', st_B') := st' in
           match ActionClass (i := A) act with
           | Intern => Transition st_A act st_A' /\ st_B = st_B' \/ Transition st_B act st_B' /\ st_A = st_A'
           | Output =>
               match ActionClass (i := B) act with
               | Input => Transition st_A act st_A' /\ Transition st_B act st_B'
               | _ => Transition st_A act st_A' /\ st_B = st_B' \/ Transition st_B act st_B' /\ st_A = st_A'
               end
           | Input =>
               match ActionClass (i := B) act with
               | Output => Transition st_A act st_A' /\ Transition st_B act st_B'
               | _ => Transition st_A act st_A' /\ st_B = st_B' \/ Transition st_B act st_B' /\ st_A = st_A'
               end
           | Unused => match ActionClass (i := B) act with
                      | Unused => False
                      | _ => Transition st_A act st_A' /\ st_B = st_B' \/ Transition st_B act st_B' /\ st_A = st_A'
                      end
           end).
  Proof.
    intros.
    case_eq (ActionClass (i := A) act) ; intros ; rewrite H0 in H.
    + case_eq (ActionClass (i := B) act) ; intro ; rewrite H1 in H ; inversion H.
    + inversion H.
    + case_eq (ActionClass (i := B) act) ; intro ; rewrite H1 in H ; inversion H.
    + case_eq (ActionClass (i := B) act) ; intro ; rewrite H1 in H ; inversion H.
      destruct st0 eqn: Hst0. destruct st'0 eqn: Hst'0. auto.
  Qed.
(*)
  Lemma CompositionInternActionHyp (A B : IOAType) :
    forall act : ActionPool,
   match ActionClass (i := A) act with
   | Intern => match ActionClass (i := B) act with
               | Output => Output
               | Input => Input
               | _ => Intern
               end
   | Output => Output
   | Input => match ActionClass (i := B) act with
              | Output => Output
              | _ => Input
              end
   | Unused => match ActionClass (i := B) act with
               | Intern => Intern
               | Output => Output
               | Input => Input
               | Unused => Unused
               end
   end = Input ->
   forall st : State A * State B,
   exists st' : State A * State B,
     let (st_A, st_B) := st in
     let (st_A', st_B') := st' in
     match ActionClass (i := A) act with
     | Intern => Transition st_A act st_A' /\ st_B = st_B' \/ Transition st_B act st_B' /\ st_A = st_A'
     | Output =>
         match ActionClass (i := B) act with
         | Input => Transition st_A act st_A' /\ Transition st_B act st_B'
         | _ => Transition st_A act st_A' /\ st_B = st_B' \/ Transition st_B act st_B' /\ st_A = st_A'
         end
     | Input =>
         match ActionClass (i := B) act with
         | Output => Transition st_A act st_A' /\ Transition st_B act st_B'
         | _ => Transition st_A act st_A' /\ st_B = st_B' \/ Transition st_B act st_B' /\ st_A = st_A'
         end
     | Unused => match ActionClass (i := B) act with
                 | Unused => False
                 | _ => Transition st_A act st_A' /\ st_B = st_B' \/ Transition st_B act st_B' /\ st_A = st_A'
                 end
     end.
  Proof.
    intros.
    case_eq (ActionClass (i := A) act0) ; intros.
    - rewrite H0 in H.
      case_eq (ActionClass (i := B) act0) ; intros ; rewrite H1 in H ; inversion H.
      assert (exists st'0 : State B, Transition (snd st0) act0 st'0).
      apply InternActionHyp. auto.
      destruct H2. exists (fst st0, x). destruct st0. right. auto.
    - rewrite H0 in H. inversion H.
    - rewrite H0 in H.
      case_eq (ActionClass (i := B) act0) ; intros ; rewrite H1 in H ; inversion H.
      assert (exists st'0 : State A, Transition (fst st0) act0 st'0).
      apply InternActionHyp. auto.
      destruct H2. exists (x, snd st0). destruct st0. left. auto.

      assert (exists st'0 : State A, Transition (fst st0) act0 st'0).
      apply InternActionHyp. auto.
      assert (exists st'0 : State B, Transition (snd st0) act0 st'0).
      apply InternActionHyp. auto.
      destruct H2, H3.
      exists (x, x0). destruct st0. left. auto.



      destruct st0.

      + rewrite H0 in H. inversion H.
      +

  Definition Composition (A B : IOAType) : IOADef :=
    mkIOADef
      (fun act : ActionPool =>
         match (ActionClass (i := A) act, ActionClass (i := B) act) with
         | (Output, _) | (_, Output) => Output
         | (Input, _) | (_, Input) => Input
         | (Unused, Unused) => Unused
         | _ => Intern
         end)
      (fun st : State A * State B =>
         let (st_A, st_B) := st in
         Start A st_A /\ Start B st_B)
      (fun (st : State A * State B) (act : ActionPool) (st' : State A * State B) =>
         let (st_A, st_B) := st in
         let (st_A', st_B') := st' in
         match (ActionClass (i := A) act, ActionClass (i := B) act) with
         | (Output, Input) | (Input, Output) => Transition st_A act st_A' /\ Transition st_B act st_B'
         | (Unused, Unused) => False
         | _ => (Transition st_A act st_A' /\ st_B = st_B') \/
                 (Transition st_B act st_B' /\ st_A = st_A')
         end)
      (CompositionUnusedActionHyp A B)
  .*)
(*)
  Lemma ProjectLeftActionLemma
    {A B : IOAType}
    (Skip : ActionPool)
    (HSkip : forall st st' : State A, (Transition A st Skip st' -> st = st') /\ Transition A st Skip st)
    (Transition_dec :
      forall (st : State A) (act : Action A) (st' : State A),
        {Transition A st act st'}+{~Transition A st act st'}) :
    forall s : ExecSection (Composition A B),
      Transition A
        (fst (st (Composition A B) s))
        (if Transition_dec (fst (st (Composition A B) s)) (act (Composition A B) s) (fst (st' (Composition A B) s)) then act (Composition A B) s else Skip)
        (fst (st' (Composition A B) s)).
  Proof.
    end.
*)
  (*
I think it is actually possible to do composition of a denombrable number of process
with some trickery on the states (type : Nat -> State (ith IOA)) and the tasks

HAHAHAHA good luck myself with the proof of projection ...
I have to find an elegant way to .. wait I've just found the solution, make Transition_dec depends on the automaton hehe
whatever
   *)
(*)
  Lemma ProjectLeftLNil
    {A B : IOADef}
    (Skip : ActionPool)
    (HSkip : forall st st' : State A, (Transition A st Skip st' -> st = st') /\ Transition A st Skip st)
    (Transition_dec : forall (st : State A) (act : Action A) (st' : State A), {Transition A st act st'}+{~Transition A st act st'}) :
    ProjectLeft (A := A) (B := B) Skip HSkip Transition_dec LNil = LNil.
  Proof.
    LList_unfold (ProjectLeft (A := A) (B := B) Skip HSkip Transition_dec LNil). simpl. auto.
  Qed.*)

  Variable SkipAction : ActionPool.

  Lemma IdIOAUnusedActionHyp :
    ActionPool -> Unused = Unused -> unit -> unit -> ~ False.
  Proof.
    auto.
  Qed.

  Definition IdIOA : IOADef :=
    mkIOADef
      (fun act : ActionPool => Unused)
      (fun st : unit => st = tt)
      (fun (st : unit) (act : ActionPool) (st' : unit) =>
         False
      )
      IdIOAUnusedActionHyp
  .

  Variable CompositionSet : Set.
  Variable NonEmpty : CompositionSet.
  Variable CompositionSet_equivalence : relation CompositionSet.
  Hypothesis CompositionSet_equivalenceHyp : equiv CompositionSet CompositionSet_equivalence.
  Hypothesis CompositionSet_dec :
    forall i j : CompositionSet, {CompositionSet_equivalence i j}+{~CompositionSet_equivalence i j}.
  Variable A : CompositionSet -> IOAType.
  Hypothesis A_is_proper :
    forall i j : CompositionSet, CompositionSet_equivalence i j -> A i = A j.

  Definition CompositionExtendedHyp : Prop :=
    forall i j : CompositionSet,
      ~ CompositionSet_equivalence i j ->
      ((forall act : Action (A i), forall st st' : State (A i),
           Transition st act st' -> ActionClass (i := (A i)) act = Intern -> forall st st' : State (A j), ~ Transition st act st') /\
         (forall act : Action (A i), ActionClass (i := (A i)) act = Output -> ~ ActionClass (i := (A j)) act = Output)
      ).

  Definition OutputSpec (f : ActionPool -> bool) : Prop :=
    forall act : ActionPool, f act = true <-> exists i : CompositionSet, ActionClass (i := (A i)) act =  Output.

  Definition InputSpec (f : ActionPool -> bool) : Prop :=
    forall act : ActionPool, f act = true <-> exists i : CompositionSet, ActionClass (i := (A i)) act = Input.

  Definition UnusedSpec (f : ActionPool -> bool) : Prop :=
    forall act : ActionPool, f act = true <-> forall i : CompositionSet, ActionClass (i := (A i)) act = Unused.

  Lemma CompositionExtendedUnusedActionHyp
    (H : CompositionExtendedHyp)
    (FOutput : ActionPool -> bool)
    (FOutputSpec : OutputSpec FOutput)
    (FInput : ActionPool -> bool)
    (FInputSpec : InputSpec FInput)
    (FUnused : ActionPool -> bool)
    (FUnusedSpec : UnusedSpec FUnused)
    :
    forall act : ActionPool,
      (if FOutput act then Output else if FInput act then Input else if FUnused act then Unused else Intern) = Unused ->
      forall st st' : forall i : CompositionSet, State (A i),
        ~
          (forall i : CompositionSet,
              (exists j : CompositionSet, ActionClass (i := (A j)) act <> Unused) /\
                (ActionClass (i := (A i)) act <> Unused -> Transition (st i) act (st' i)) /\
                (ActionClass (i := (A i)) act = Unused -> st i = st' i)).
  Proof.
    intros.
    case_eq (FOutput act) ; intros ; rewrite H1 in H0 ; inversion H0 ;
      case_eq (FInput act) ; intros ; rewrite H2 in H0 ; inversion H0.
    case_eq (FUnused act) ; intros ; rewrite H4 in H0 ; inversion H0.
    hnf. intro. specialize H6 with (i := NonEmpty). destruct H6. destruct H6.
    hnf in FUnusedSpec. specialize FUnusedSpec with act. destruct FUnusedSpec.
    rewrite H4 in H8. specialize H8 with x. assert (ActionClass (i := (A x)) act = Unused). apply H8. auto.
    contradiction.
  Qed.

  Definition CompositionExtended
    (H : CompositionExtendedHyp)
    (FOutput : ActionPool -> bool)
    (FOutputSpec : OutputSpec FOutput)
    (FInput : ActionPool -> bool)
    (FInputSpec : InputSpec FInput)
    (FUnused : ActionPool -> bool)
    (FUnusedSpec : UnusedSpec FUnused)
    : IOADef :=
    mkIOADef
      (fun act : ActionPool =>
         match (FOutput act, FInput act) with
         | (true, _) => Output
         | (false, true) => Input
         | _ => if FUnused act then Unused else Intern
         end
      )
      (fun st : forall i : CompositionSet, State (A i) =>
         forall i : CompositionSet, Start (A i) (st i))
      (fun (st : forall i : CompositionSet, State (A i)) (act : ActionPool) (st' : forall i : CompositionSet, State (A i)) =>
         forall i : CompositionSet,
           (exists j : CompositionSet, ActionClass (i := (A j)) act <> Unused) /\
             (
               (ActionClass (i := (A i)) act <> Unused -> Transition (st i) act (st' i)) /\
                 (ActionClass (i := (A i)) act = Unused -> st i = st' i)
      ))
      (CompositionExtendedUnusedActionHyp H FOutputSpec FInputSpec FUnusedSpec)
  .

  Definition is_byzentine (Original : IOAType) (Byzentine : IOAType) : Prop :=
    forall act : ActionPool, ActionClass (i := Original) act = ActionClass (i := Byzentine) act.

(*)
  FixPoint project_execution
    (H : CompositionExtendedHyp)
    (FOutput : ActionPool -> bool)
    (FOutputSpec : OutputSpec FOutput)
    (FInput : ActionPool -> bool)
    (FInputSpec : InputSpec FInput)
    (FUnused : ActionPool -> bool)
    (FUnusedSpec : UnusedSpec FUnused)
    (comp : CompositionSet)
    (act_skip : ActionPool)
    (transition_compute : State (A comp) -> ActionPool -> option (State (A comp)))
    (transition_compute_hyp : forall st st',
        Transition (i := A comp) st act_skip st' -> transition_compute st act_skip = Some st')
    (act_hyp : forall st : State (A comp), forall act : ActionPool, {st' | Transition st act st'})
    (e : ExecFragmentType (A := CompositionExtended H FOutputSpec FInputSpec FUnusedSpec))
    (i : nat) :=
    let (st, act, st', _) := (e i) in
    let (st0, act0, st'0, _) := (e (i + 1)) in
    match i with
      | 0 =>
          match (transition_compute (st comp) act) with
            | Some _ =>
                match (transition_compute (st0 comp) act0) with
                  | Some _ =>
                  | None =>
            | None =>
                match
                match (transition_compute ( comp) act0) with*)


  (*)
  Theorem project_section_exists
    (H : CompositionExtendedHyp)
    (FOutput : ActionPool -> bool)
    (FOutputSpec : OutputSpec FOutput)
    (FInput : ActionPool -> bool)
    (FInputSpec : InputSpec FInput)
    (FUnused : ActionPool -> bool)
    (FUnusedSpec : UnusedSpec FUnused) :
    forall comp : CompositionSet,
      forall e : ExecSection (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec),
        exists e' : ExecSection (A comp),
          st (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) e comp = st (A comp) e' /\
            st' (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) e comp = st (A comp) e' /\
            (
              match opt_act (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) e with
                | None => opt_act (A comp) e' = None
                | Some act =>
                    match ActionClass act with
                      | Unused => opt_act (A comp) e' = None
                      | _ => opt_act (A comp) e' = Some act
                    end
                end
            ).
  Proof.
    intros.
    case_eq (opt_act (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) e) ; intros.
    case_eq *)

  



  Definition project_execution_aux
    (H : CompositionExtendedHyp)
    (FOutput : ActionPool -> bool)
    (FOutputSpec : OutputSpec FOutput)
    (FInput : ActionPool -> bool)
    (FInputSpec : InputSpec FInput)
    (FUnused : ActionPool -> bool)
    (FUnusedSpec : UnusedSpec FUnused)
    (comp : CompositionSet)
    (e : ExecFragmentType (A := CompositionExtended H FOutputSpec FInputSpec FUnusedSpec))
    (i : nat) :
    {
      s : ExecSection (A comp) |
      st (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp = st (A comp) s /\
        st' (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp = st' (A comp) s /\
        match opt_act (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) with
                | None => opt_act (A comp) s = None
                | Some act =>
                    match ActionClass (i := A comp) act with
                      | Unused => opt_act (A comp) s = None
                      | _ => opt_act (A comp) s = Some act
                    end
                end
    }.
    case_eq (opt_act (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i)) ; intros.
    case_eq (ActionClass (i := A comp) a) ; intros ; destruct (e i) ; simpl in * ;
    (assert (is_well_formed_exist :
        match opt_act0 with
          | Some act => Transition (st0 comp) act (st'0 comp)
          | None => st0 comp = st'0 comp
        end) ;
      (rewrite H0 in is_well_formed0 |- * ;
    apply is_well_formed0 ; rewrite H1 ; discriminate) ||
    apply exist with (
      mkExecSection
        (A comp)
        (st0 comp)
        opt_act0
        (st'0 comp)
        is_well_formed_exist
      ) ; auto) || idtac.
    assert (is_well_formed_exist :
        match None with
          | Some act => Transition (st0 comp) act (st'0 comp)
          | None => st0 comp = st'0 comp
        end).
    rewrite H0 in *. apply is_well_formed0. auto.
    apply exist with (
      mkExecSection
        (A comp)
        (st0 comp)
        None
        (st'0 comp)
        is_well_formed_exist
      ). auto.

    destruct (e i). simpl in *.
    assert (is_well_formed_exist :
        match None with
          | Some act => Transition (st0 comp) act (st'0 comp)
          | None => st0 comp = st'0 comp
        end).
    rewrite H0 in *. subst st0. auto.
    apply exist with (
      mkExecSection
        (A comp)
        (st0 comp)
        None
        (st'0 comp)
        is_well_formed_exist
      ). auto.
  Qed.

  Definition project_execution
    (H : CompositionExtendedHyp)
    (FOutput : ActionPool -> bool)
    (FOutputSpec : OutputSpec FOutput)
    (FInput : ActionPool -> bool)
    (FInputSpec : InputSpec FInput)
    (FUnused : ActionPool -> bool)
    (FUnusedSpec : UnusedSpec FUnused)
    (comp : CompositionSet)
    (e : ExecFragmentType (A := CompositionExtended H FOutputSpec FInputSpec FUnusedSpec))
    (i : nat) :
    ExecSection (A comp).
    apply (proj1_sig (project_execution_aux comp e i)).
  Defined.

  Theorem project_execution_has_same_start_states
    (H : CompositionExtendedHyp)
    (FOutput : ActionPool -> bool)
    (FOutputSpec : OutputSpec FOutput)
    (FInput : ActionPool -> bool)
    (FInputSpec : InputSpec FInput)
    (FUnused : ActionPool -> bool)
    (FUnusedSpec : UnusedSpec FUnused) :
    forall comp : CompositionSet,
    forall e : ExecFragmentType,
      forall i : nat,
        st (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp =
            st (A comp) (project_execution comp e i).
  Proof.
    intros.
     apply (proj2_sig (project_execution_aux comp e i)).
  Qed.

  Theorem project_execution_has_same_end_states
    (H : CompositionExtendedHyp)
    (FOutput : ActionPool -> bool)
    (FOutputSpec : OutputSpec FOutput)
    (FInput : ActionPool -> bool)
    (FInputSpec : InputSpec FInput)
    (FUnused : ActionPool -> bool)
    (FUnusedSpec : UnusedSpec FUnused) :
    forall comp : CompositionSet,
    forall e : ExecFragmentType,
      forall i : nat,
        st' (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp =
            st' (A comp) (project_execution comp e i).
  Proof.
    intros.
     apply (proj2_sig (project_execution_aux comp e i)).
  Qed.

  Theorem project_execution_has_same_actions
    (H : CompositionExtendedHyp)
    (FOutput : ActionPool -> bool)
    (FOutputSpec : OutputSpec FOutput)
    (FInput : ActionPool -> bool)
    (FInputSpec : InputSpec FInput)
    (FUnused : ActionPool -> bool)
    (FUnusedSpec : UnusedSpec FUnused) :
    forall comp : CompositionSet,
    forall e : ExecFragmentType,
      forall i : nat,
        match opt_act (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) with
                | None => opt_act (A comp) (project_execution comp e i) = None
                | Some act =>
                    match ActionClass (i := A comp) act with
                      | Unused => opt_act (A comp) (project_execution comp e i) = None
                      | _ => opt_act (A comp) (project_execution comp e i) = Some act
                    end
                end.
  Proof.
    intros.
     apply (proj2_sig (project_execution_aux comp e i)).
  Qed.

  Theorem project_execution_exist
    (H : CompositionExtendedHyp)
    (FOutput : ActionPool -> bool)
    (FOutputSpec : OutputSpec FOutput)
    (FInput : ActionPool -> bool)
    (FInputSpec : InputSpec FInput)
    (FUnused : ActionPool -> bool)
    (FUnusedSpec : UnusedSpec FUnused) :
      forall comp : CompositionSet,
      forall e : ExecFragmentType,
        exists e' : ExecFragmentType,
          forall i : nat,
            st (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp = st (A comp) (e' i) /\
              st' (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp = st' (A comp) (e' i) /\
        match opt_act (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) with
                | None => opt_act (A comp) (e' i) = None
                | Some act =>
                    match ActionClass (i := A comp) act with
                      | Unused => opt_act (A comp) (e' i) = None
                      | _ => opt_act (A comp) (e' i) = Some act
                    end
                end.
  Proof.
    intros.
    exists (project_execution comp e).
    intros. apply (proj2_sig (project_execution_aux comp e i)).
  Qed.

  Theorem project_execution_exist_with_exec
    (H : CompositionExtendedHyp)
    (FOutput : ActionPool -> bool)
    (FOutputSpec : OutputSpec FOutput)
    (FInput : ActionPool -> bool)
    (FInputSpec : InputSpec FInput)
    (FUnused : ActionPool -> bool)
    (FUnusedSpec : UnusedSpec FUnused) :
      forall comp : CompositionSet,
      forall e : ExecFragmentType,
        Exec e ->
        exists e' : ExecFragmentType,
          Exec e' /\
            forall i : nat,
            st (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp = st (A comp) (e' i) /\
              st' (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp = st' (A comp) (e' i) /\
        match opt_act (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) with
                | None => opt_act (A comp) (e' i) = None
                | Some act =>
                    match ActionClass (i := A comp) act with
                      | Unused => opt_act (A comp) (e' i) = None
                      | _ => opt_act (A comp) (e' i) = Some act
                    end
                end.
  Proof.
    intros.
    assert (exists e' : ExecFragmentType,
          forall i : nat,
            st (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp = st (A comp) (e' i) /\
              st' (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp = st' (A comp) (e' i) /\
        match opt_act (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) with
                | None => opt_act (A comp) (e' i) = None
                | Some act =>
                    match ActionClass (i := A comp) act with
                      | Unused => opt_act (A comp) (e' i) = None
                      | _ => opt_act (A comp) (e' i) = Some act
                    end
                end). eapply project_execution_exist.
    destruct H1.
    exists x. split ; auto.
    unfold Exec, Start, ExecFragment in H0 |- *. destruct H0 as [H0 Hstart].
    split.
    intro. specialize H0 with i.
    assert (st (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e (i+1)) comp = st (A comp) (x (i+1))).
    apply H1. rewrite <-H2.
    rewrite <-H0. apply eq_sym. apply H1.
    assert (st (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e 0) comp = st (A comp) (x 0)).
    apply H1. rewrite <-H2.
    unfold CompositionExtended in Hstart. specialize Hstart with comp.
    unfold Start in Hstart. unfold CompositionExtended. auto.
  Qed.

  Theorem extend_safety_properties
    (H : CompositionExtendedHyp)
    (FOutput : ActionPool -> bool)
    (FOutputSpec : OutputSpec FOutput)
    (FInput : ActionPool -> bool)
    (FInputSpec : InputSpec FInput)
    (FUnused : ActionPool -> bool)
    (FUnusedSpec : UnusedSpec FUnused) :
    forall comp : CompositionSet,
    forall Q : State (A comp) -> Prop,
    (forall e : ExecFragmentType,
      Exec e ->
      forall i : nat, Q (st (A comp) (e i))) ->
    forall e : ExecFragmentType,
      Exec e ->
      forall i : nat,
        Q (st (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp).
  Proof.
    intros.
    assert (exists e' : ExecFragmentType,
          Exec e' /\
            forall i : nat,
            st (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp = st (A comp) (e' i) /\
              st' (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp = st' (A comp) (e' i) /\
        match opt_act (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) with
                | None => opt_act (A comp) (e' i) = None
                | Some act =>
                    match ActionClass (i := A comp) act with
                      | Unused => opt_act (A comp) (e' i) = None
                      | _ => opt_act (A comp) (e' i) = Some act
                    end
                end). apply project_execution_exist_with_exec.
    apply H1.
    destruct H2.
    destruct H2. specialize H3 with i.
    destruct H3. rewrite H3.
    auto.
  Qed.

  Definition past_property_act_st
    (ioa : IOAType)
    (Q : ActionPool -> Prop)
    (P : State ioa -> Prop) :=
      forall e,
        Exec e ->
        forall i : nat, forall act : ActionPool,
          opt_act ioa (e i) = Some act ->
          Q act ->
          exists j : nat, j < i /\ P (st ioa (e j)).

  Theorem extend_past_properties_act_st
    (H : CompositionExtendedHyp)
    (FOutput : ActionPool -> bool)
    (FOutputSpec : OutputSpec FOutput)
    (FInput : ActionPool -> bool)
    (FInputSpec : InputSpec FInput)
    (FUnused : ActionPool -> bool)
    (FUnusedSpec : UnusedSpec FUnused) :
    forall comp : CompositionSet,
    forall Q : ActionPool -> Prop,
    forall P : State (A comp) -> Prop,
    (forall act, Q act -> ActionClass (i := A comp) act <> Unused) ->
    (past_property_act_st (A comp) Q P) ->
    past_property_act_st
      (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec)
      Q
      (fun s => P (s comp))
  .
  Proof.
    unfold past_property_act_st.
    intros.
    assert (exists e' : ExecFragmentType,
          Exec e' /\
            forall i : nat,
            st (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp = st (A comp) (e' i) /\
              st' (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp = st' (A comp) (e' i) /\
        match opt_act (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) with
                | None => opt_act (A comp) (e' i) = None
                | Some act =>
                    match ActionClass (i := A comp) act with
                      | Unused => opt_act (A comp) (e' i) = None
                      | _ => opt_act (A comp) (e' i) = Some act
                    end
                end). apply project_execution_exist_with_exec.
    apply H2. destruct H5.
    destruct H5.
    pose proof H6 as H6_dup.
    specialize H6 with i.
    destruct H6. destruct H7. rewrite H3 in H8.
    case_eq (ActionClass (i := A comp) act) ; intro ; rewrite H9 in H8 ;
    try (assert (opt_act (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) =
              opt_act (A comp) (x i)
          ) ;
    try (rewrite H3, H8 ; auto) ;
    assert (exists j, j < i /\ P (st (A comp) (x j))) ; try apply H1 with act ; auto ;
    destruct H11 ; exists x0 ; assert (
        st (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e x0) comp =
          st (A comp) (x x0)
      ) ;
    try (specialize H6_dup with x0 ; apply H6_dup) ;
    rewrite H12 ; auto).
    assert (ActionClass (i := A comp) act <> Unused). apply H0. auto.
    contradiction.
  Qed.

  Definition past_property_st_act
    (ioa : IOAType)
    (Q : State ioa -> Prop)
    (P : ActionPool -> Prop) :=
      forall e,
        Exec e ->
        forall i : nat,
          Q (st ioa (e i)) ->
          exists j : nat, exists act', j < i /\ opt_act ioa (e j) = Some act' /\ P act'.

  Theorem extend_past_properties_st_act
    (H : CompositionExtendedHyp)
    (FOutput : ActionPool -> bool)
    (FOutputSpec : OutputSpec FOutput)
    (FInput : ActionPool -> bool)
    (FInputSpec : InputSpec FInput)
    (FUnused : ActionPool -> bool)
    (FUnusedSpec : UnusedSpec FUnused) :
    forall comp : CompositionSet,
    forall Q : State (A comp) -> Prop,
    forall P : ActionPool -> Prop,
    (past_property_st_act (A comp) Q P) ->
    past_property_st_act
      (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec)
      (fun s => Q (s comp))
      P.
  Proof.
    unfold past_property_st_act.
    intros.
    assert (exists e' : ExecFragmentType,
          Exec e' /\
            forall i : nat,
            st (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp = st (A comp) (e' i) /\
              st' (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp = st' (A comp) (e' i) /\
        match opt_act (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) with
                | None => opt_act (A comp) (e' i) = None
                | Some act =>
                    match ActionClass (i := A comp) act with
                      | Unused => opt_act (A comp) (e' i) = None
                      | _ => opt_act (A comp) (e' i) = Some act
                    end
                end). apply project_execution_exist_with_exec.
    auto.
    destruct H3. destruct H3.
    apply H0 with x i in H3.
    destruct H3. destruct H3. destruct H3. destruct H5.
    exists x0, x1. split ; auto. specialize H4 with x0. split ; auto.
    destruct H4. destruct H7. destruct (e x0). simpl in *.
    induction opt_act0.
    induction (ActionClass (i := A comp) a) ;
    try (rewrite <-H8 ; auto).
    rewrite H8 in H5. inversion H5.
    rewrite H8 in H5. inversion H5.
    specialize H4 with i. destruct H4. rewrite <-H4. auto.
  Qed.

  Definition past_property_act_act
    (ioa : IOAType)
    (Q : ActionPool -> Prop)
    (P : ActionPool -> Prop) :=
      forall e,
        Exec e ->
        forall i : nat, forall act : ActionPool,
          opt_act ioa (e i) = Some act ->
          Q act ->
          exists j : nat, exists act' : ActionPool,
            j < i /\ opt_act ioa (e j) = Some act' /\ P act'.

  Theorem extend_past_properties_act_act
    (H : CompositionExtendedHyp)
    (FOutput : ActionPool -> bool)
    (FOutputSpec : OutputSpec FOutput)
    (FInput : ActionPool -> bool)
    (FInputSpec : InputSpec FInput)
    (FUnused : ActionPool -> bool)
    (FUnusedSpec : UnusedSpec FUnused) :
    forall comp : CompositionSet,
    forall Q P : ActionPool -> Prop,
    (forall act, Q act -> ActionClass (i := A comp) act <> Unused) ->
    (past_property_act_act (A comp) Q P) ->
    past_property_act_act
      (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec)
      Q P.
  Proof.
    unfold past_property_act_act.
    intros.
    assert (exists e' : ExecFragmentType,
          Exec e' /\
            forall i : nat,
            st (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp = st (A comp) (e' i) /\
              st' (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) comp = st' (A comp) (e' i) /\
        match opt_act (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e i) with
                | None => opt_act (A comp) (e' i) = None
                | Some act =>
                    match ActionClass (i := A comp) act with
                      | Unused => opt_act (A comp) (e' i) = None
                      | _ => opt_act (A comp) (e' i) = Some act
                    end
                end). apply project_execution_exist_with_exec ; auto.
    destruct H5 as [e' Hpast_prop_hyp].
    specialize H1 with e' i act.
    destruct Hpast_prop_hyp.
    apply H1 in H5.
    destruct H5 as [j Hj]. exists j. destruct Hj as [act' Hj]. exists act'. destruct Hj. split ; auto.
    specialize H6 with j. destruct H6. destruct H8.
    destruct H7. rewrite H7 in *. clear H7.
    case_eq (opt_act (CompositionExtended H FOutputSpec FInputSpec FUnusedSpec) (e j)) ; intros.
    rewrite H7 in H9.
    case_eq (ActionClass (i := A comp) a) ; intro Heq ; rewrite Heq in H9 ; auto.
    inversion H9.
    rewrite H7 in H9. inversion H9.
    specialize H6 with i. destruct H6. destruct H7. rewrite H3 in H8.
    case_eq (ActionClass (i := A comp) act) ;
      intro Heq ; rewrite Heq in H8 ; auto.
    apply H0 in H4. contradiction. auto.
  Qed.


(*)
Lemma ProjectExtendedActionLemma
  {A : nat -> IOAType}
  {H : CompositionExtendedHyp A}
  (FOutput : ActionPool -> bool)
  (FOutputSpec : OutputSpec A FOutput)
  (FInput : ActionPool -> bool)
  (FInputSpec : InputSpec A FInput)
  (FUnused : ActionPool -> bool)
  (FUnusedSpec : UnusedSpec A FUnused)
  (i : nat)
  (Skip : ActionPool)
  (HSkip : forall st st' : State (A i), (Transition (A i) st Skip st' -> st = st') /\ (Transition (A i) st Skip st))
  (Transition_dec : forall (st : State (A i)) (act : Action (A i)) (st' : State (A i)), {Transition (A i) st act st'}+{~Transition (A i) st act st'})
  : forall s : ExecSection (A := CompositionExtended H FOutputSpec FInputSpec FUnusedSpec),
    Transition (A i) (st s i) (if Transition_dec (st s i) (act s) (st' s i) then act s else Skip) (st' s i).
Proof.
  intros s.
  case_eq (Transition_dec (st s i) (act s) (st' s i)) ; intros.
  + auto.
  + assert (Hsteq : st s i = st' s i).
    assert (HWellFormed : Transition (CompositionExtended H Hout Hin Hun) (st s) (act s) (st' s)).
    apply (is_well_formed s).
    simpl in HWellFormed. (*destruct (st s i) eqn: Hst in HWellFormed. destruct (st' s i) eqn: Hst' in HWellFormed.*)
    case_eq (ActionClass (A i) (act s)) ; intros ; specialize HWellFormed with (i := i) ;
      destruct HWellFormed ; destruct H3 ; rewrite H1 in H3 ; (contradiction || auto || idtac) ;
    (rewrite H1 in * ; assert (Trivial : Transition (A i) (st s i) (act s) (st' s i)) ; (apply H3 ; discriminate) || idtac ; contradiction ; fail) || idtac.
    rewrite Hsteq. apply HSkip. apply (st s i).
Qed.

CoFixpoint ProjectExtended
  {A : nat -> IOAType}
  {H : CompositionExtendedHyp A}
  {Hout : forall act : ActionPool, *
      {exists i : nat, ActionClass (A i) act = Output}+{~exists i : nat, ActionClass (A i) act = Output}}
  {Hin : forall act : ActionPool,
      {exists i : nat, ActionClass (A i) act = Input}+{~exists i : nat, ActionClass (A i) act = Input}}
  {Hun : UnusedHyp A}
  (e : ExecFragmentType (A := CompositionExtended H Hout Hin Hun))
  (i : nat)
  (Skip : ActionPool)
  (HSkip : forall st st' : State (A i), (Transition (A i) st Skip st' -> st = st') /\ (Transition (A i) st Skip st))
  (Transition_dec : forall (st : State (A i)) (act : Action (A i)) (st' : State (A i)), {Transition (A i) st act st'}+{~Transition (A i) st act st'})
  : ExecFragmentType (A := A i) :=
  match e with
    | LNil => LNil
    | LCons s e' =>
        LCons
          (mkExecSection
             (st s i)
             (if Transition_dec (st s i) (act s) (st' s i) then act s else Skip)
             (st' s i)
             (ProjectExtendedActionLemma i Skip HSkip Transition_dec s)
          )
          (ProjectExtended e' i Skip HSkip Transition_dec)
    end
.

Lemma LNilProjectExtended
  {A : nat -> IOAType}
  {H : CompositionExtendedHyp A}
  {Hout : forall act : ActionPool,
      {exists i : nat, ActionClass (A i) act = Output}+{~exists i : nat, ActionClass (A i) act = Output}}
  {Hin : forall act : ActionPool,
      {exists i : nat, ActionClass (A i) act = Input}+{~exists i : nat, ActionClass (A i) act = Input}}
  {Hun : UnusedHyp A}
  (i : nat)
  (Skip : ActionPool)
  (HSkip : forall st st' : State (A i), (Transition (A i) st Skip st' -> st = st') /\ (Transition (A i) st Skip st))
  (Transition_dec : forall (st : State (A i)) (act : Action (A i)) (st' : State (A i)), {Transition (A i) st act st'}+{~Transition (A i) st act st'})
  : ProjectExtended (H := H) (Hout := Hout) (Hin := Hin) (Hun := Hun) LNil i Skip HSkip Transition_dec = LNil.
Proof.
  LList_unfold (ProjectExtended (H := H) (Hout := Hout) (Hin := Hin) (Hun := Hun) LNil i Skip HSkip Transition_dec). simpl. auto.
Qed.

Lemma LConsProjectExtended
  {A : nat -> IOAType}
  {H : CompositionExtendedHyp A}
  {Hout : forall act : ActionPool,
      {exists i : nat, ActionClass (A i) act = Output}+{~exists i : nat, ActionClass (A i) act = Output}}
  {Hin : forall act : ActionPool,
      {exists i : nat, ActionClass (A i) act = Input}+{~exists i : nat, ActionClass (A i) act = Input}}
  {Hun : UnusedHyp A}
  (i : nat)
  (Skip : ActionPool)
  (HSkip : forall st st' : State (A i), (Transition (A i) st Skip st' -> st = st') /\ (Transition (A i) st Skip st))
  (Transition_dec : forall (st : State (A i)) (act : Action (A i)) (st' : State (A i)), {Transition (A i) st act st'}+{~Transition (A i) st act st'})
  : forall (e : ExecFragmentType) (s : ExecSection),
    ProjectExtended (H := H) (Hout := Hout) (Hin := Hin) (LCons s e) i Skip HSkip Transition_dec =
      LCons
          (mkExecSection
             (st s i)
             (if Transition_dec (st s i) (act s) (st' s i) then act s else Skip)
             (st' s i)
             (ProjectExtendedActionLemma i Skip HSkip Transition_dec s)
          )
          (ProjectExtended (H := H) (Hout := Hout) (Hin := Hin) (Hun := Hun) e i Skip HSkip Transition_dec).
Proof.
  intros. LList_unfold (ProjectExtended (LCons s e) i Skip HSkip Transition_dec). simpl. auto.
Qed.


Theorem ExecFragmentProject
  {A : nat -> IOAType}
  {H : CompositionExtendedHyp A}
  {Hout : forall act : ActionPool,
      {exists i : nat, ActionClass (A i) act = Output}+{~exists i : nat, ActionClass (A i) act = Output}}
  {Hin : forall act : ActionPool,
      {exists i : nat, ActionClass (A i) act = Input}+{~exists i : nat, ActionClass (A i) act = Input}}
  {Hun : UnusedHyp A} :
  forall
  (e : ExecFragmentType (A := CompositionExtended H Hout Hin Hun))
  (i : nat)
  (Skip : ActionPool)
  (HSkip : forall st st' : State (A i), (Transition (A i) st Skip st' -> st = st') /\ (Transition (A i) st Skip st))
  (Transition_dec : forall (st : State (A i)) (act : Action (A i)) (st' : State (A i)), {Transition (A i) st act st'}+{~Transition (A i) st act st'}),
  ExecFragment (A := CompositionExtended H Hout Hin Hun) e -> ExecFragment (ProjectExtended e i Skip HSkip Transition_dec).
Proof.
  cofix Hcofix.
  intros.
  case_eq e ; intros.
  + rewrite (LNilProjectExtended i Skip HSkip Transition_dec). auto with ioa.
  + rewrite (LConsProjectExtended i Skip HSkip Transition_dec). case_eq l ; intros.
    - rewrite (LNilProjectExtended i Skip HSkip Transition_dec). auto with ioa.
    - rewrite (LConsProjectExtended i Skip HSkip Transition_dec). apply ExecFragment_LCons.
      * rewrite <-(LConsProjectExtended i Skip HSkip Transition_dec). apply Hcofix. rewrite H1 in H0. rewrite <-H2. apply ExecFragment_decomposition in H0. auto.
      * simpl. rewrite H1 in H0. rewrite H2 in H0. inversion H0. rewrite H7. auto.
Qed.

Theorem ExecProject
  {A : nat -> IOAType}
  {H : CompositionExtendedHyp A}
  {Hout : forall act : ActionPool,
      {exists i : nat, ActionClass (A i) act = Output}+{~exists i : nat, ActionClass (A i) act = Output}}
  {Hin : forall act : ActionPool,
      {exists i : nat, ActionClass (A i) act = Input}+{~exists i : nat, ActionClass (A i) act = Input}}
  {Hun : UnusedHyp A} :
  forall
  (e : ExecFragmentType (A := CompositionExtended H Hout Hin Hun))
  (i : nat)
  (Skip : ActionPool)
  (HSkip : forall st st' : State (A i), (Transition (A i) st Skip st' -> st = st') /\ (Transition (A i) st Skip st))
  (Transition_dec : forall (st : State (A i)) (act : Action (A i)) (st' : State (A i)), {Transition (A i) st act st'}+{~Transition (A i) st act st'}),
  Exec (A := CompositionExtended H Hout Hin Hun) e -> Exec (ProjectExtended e i Skip HSkip Transition_dec).
Proof.
  intros. split ; destruct H0.
  + apply ExecFragmentProject. auto.
  + case_eq e ; intros ; simpl ; auto.
    rewrite H2 in H1. hnf in H1. specialize H1 with (i := i). auto.
Qed.*)

End IOA.

  

  Ltac simpl_ActionClass :=
    match goal with
      | [|- context [
               ActionClass ?ioa ?act
      ]] =>
          let hioa := get_term_head ioa in
          cbv delta [hioa] beta ; simpl ; repeat simpl_match ; repeat simpl_arith_bool ; auto
      | [H : context [
                 ActionClass ?ioa ?act
      ] |- _] =>
          let hioa := get_term_head ioa in
          cbv delta [hioa] beta in H ; simpl in H ; repeat simpl_match ; repeat simpl_arith_bool ; auto
    end.

  Ltac simpl_Transition :=
    match goal with
      | [|- context [
               Transition ?ioa ?st ?act ?st'
      ]] =>
          let hioa := get_term_head ioa in
          cbv delta [hioa] beta ; simpl ; repeat simpl_match ; repeat simpl_arith_bool ; auto
      | [H : context [
                 Transition ?ioa ?st ?act ?st'
      ] |- _] =>
          let hioa := get_term_head ioa in
          cbv delta [hioa
            ] beta in H ; simpl in H ; repeat simpl_match ; repeat simpl_arith_bool ; auto
    end.

  Ltac revert_hyp_with_i i :=
    match goal with
      | [H : context [i] |- _] =>
          revert H ; revert_hyp_with_i i
      | _ => idtac
    end.

  Open Scope ltl_scope.
  Require Import Lia.

  Ltac destruct_fair_exec :=
    match goal with
      | [
        e : ExecFragmentType (ActionPool := ?action_pool),
        H : FairFragment ?e,
        x : ?action_pool |-
        ?e $ ?i |= ?phi
      ] =>
          let Hineq := fresh "Hineq" in
          let Htmp := fresh "Htmp" in
          let Hinduction := fresh "Hinduction" in
          let j := fresh "j" in
          let n := fresh "n" in
          hnf in H ; specialize H with x ; destruct H ;  hnf in H ; specialize H with i ;
          assert (Hineq : i >= 0) ; lia || idtac ; apply H in Hineq ;
          [idtac
          | destruct Hineq as (j, Hineq) ;
            revert Hineq ; revert_hyp_with_i i ;
            assert (Hinduction : exists n : nat, n = j - i) ; [exists (j - i) ; auto | idtac] ;
            destruct Hinduction as (n, Hinduction) ; revert Hinduction ; revert i j ; induction n
          ]
    end.

  Close Scope ltl_scope.
