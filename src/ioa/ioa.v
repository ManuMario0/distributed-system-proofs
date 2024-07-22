Require Import List Arith Bool Lia Ensembles.
Import ListNotations.

Require Import common.tactic.

(*)
Possibly later used, but TO REMOVE

Require Import Sets.Ensembles.
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
Require Import Lia.*)



(*
  I want to use a variant of IOA.
  If I simply transform them in
  automaton, I can say that I
  recognise the trace if :
  1. Does not go to None state
     This is automatic if we
     don't put it as accepting
     condition.
  2. Does not stagned if an
     action is enabled
     This one is way more tricky
     to specify, this is for
     liveness
     A solution might be to
     identify a set of states
     in which no internal or
     output actions are enabled,
     and set it a an acceptance
     condition.

 *)

Record Signature (action_t : Type) : Type :=
  mkSignature {
      intern : Ensemble action_t;
      output : Ensemble action_t;
      input : Ensemble action_t;
  }
.

Arguments intern {_} _.
Arguments output {_} _.
Arguments input {_} _.

Definition ext
  {action_t : Type}
  (sig : Signature action_t)
  : Ensemble action_t :=
  Union
    _
    sig.(output)
    sig.(input)
.
Definition acts
  {action_t : Type}
  (sig : Signature action_t)
  : Ensemble action_t :=
  Union
    _
    sig.(intern)
    (ext sig)
.
Definition local
  {action_t : Type}
  (sig : Signature action_t)
  : Ensemble action_t :=
  Union
    _
    sig.(intern)
    sig.(output)
.
Definition extsig
  {action_t : Type}
  (sig : Signature action_t)
  : Signature action_t :=
  mkSignature
    _
    (Empty_set _)
    sig.(output)
    sig.(input)
.

Definition sig_composition
  {action_t : Type}
  (sigA sigB : Signature action_t) :=
  mkSignature
    _
    (Union _ sigA.(intern) sigB.(intern))
    (Union _ sigA.(output) sigB.(output))
    ( Setminus _ (Union _ sigA.(input) sigB.(input)) (Union _ sigA.(output) sigB.(output)))
.

Definition empty_sig
  (action_t : Type)
  : Signature action_t
  :=
  mkSignature
    _
    (Empty_set _)
    (Empty_set _)
    (Empty_set _)
.

Definition sig_hide
  {action_t : Type}
  (sig : Signature action_t)
  (p : Ensemble action_t)
  : Signature action_t :=
  mkSignature
    _
    (Union _ sig.(intern) p)
    (Setminus _ sig.(output) p)
    (sig.(input))
.

Definition sig_dec
  {action_t : Type}
  (sig : Signature action_t) : Prop :=
  forall a : action_t,
    (In _ sig.(intern) a \/ ~In _ sig.(intern) a) /\
      (In _ sig.(output) a \/ ~In _ sig.(output) a) /\
      (In _ sig.(input) a \/ ~In _ sig.(input) a)
.

Definition
  act_dec_t
    {action_t : Type}
    (sig : Signature action_t)
    : Type :=
  forall a : action_t,
    {In _ (acts sig) a}+{~In _ (acts sig) a}
.

Global Hint Unfold ext acts local : sig.

Section Signature.
  Set Implicit Arguments.
  Variable action_t : Type.

  Variable sig : Signature action_t.

  Ltac auto_solve_sig :=
    unfold acts, ext, local in * ; auto with sets sig.

  Lemma intern_in_act :
    Included _ (intern sig) (acts sig).
  Proof.
    auto_solve_sig.
  Qed.

  Lemma output_in_act :
    Included _ (output sig) (acts sig).
  Proof.
    auto_solve_sig.
  Qed.

  Lemma input_in_act :
    Included _ (input sig) (acts sig).
  Proof.
    auto_solve_sig.
  Qed.

  Hint Resolve intern_in_act output_in_act input_in_act : sig.

  Lemma local_in_act :
    Included _ (local sig) (acts sig).
  Proof.
    auto_solve_sig.
    unfold Included. intros. destruct H ; auto with sig.
  Qed.

  Lemma ext_in_act :
    Included _ (ext sig) (acts sig).
  Proof.
    auto_solve_sig.
  Qed.

  Lemma intern_in_local :
    Included _ (intern sig) (local sig).
  Proof.
    auto_solve_sig.
  Qed.

  Lemma output_in_local :
    Included _ (output sig) (local sig).
  Proof.
    auto_solve_sig.
  Qed.

  Hint Resolve local_in_act ext_in_act intern_in_local output_in_local : sig.

  Lemma act_to_local_input :
    acts sig = Union _ (local sig) (input sig).
  Proof.
    apply Extensionality_Ensembles.
    unfold Same_set. split.
    - unfold Included. intros.
      auto_solve_sig.
      destruct H ; auto_solve_sig.
      destruct H ; auto_solve_sig.
    - unfold Included. intros.
      auto_solve_sig.
      destruct H ; auto_solve_sig.
  Qed.

  Lemma act_to_ext_intern :
    acts sig = Union _ (ext sig) (intern sig).
  Proof.
    apply Extensionality_Ensembles.
    unfold Same_set. split.
    - unfold Included. intros.
      auto_solve_sig.
      destruct H ; auto_solve_sig.
    - unfold Included. intros.
      auto_solve_sig.
      destruct H ; auto_solve_sig.
  Qed.

  Hint Rewrite act_to_local_input act_to_ext_intern : sig.

  Lemma sig_act_dec :
    forall a : action_t,
      sig_dec sig ->
      In _ (acts sig) a \/ ~In _ (acts sig) a.
  Proof.
    unfold sig_dec, acts.
    intros.
    specialize H with a.
    destruct H as [Hi [HO HI]].
    destruct Hi, HO, HI ; auto with sets sig.
    right.
    intro.
    repeat destruct H2 ; auto with sets.
  Qed.

  Lemma union_commute :
    forall T : Type,
      forall a b : Ensemble T,
        Union _ a b = Union _ b a.
  Proof.
    intros.
    apply Extensionality_Ensembles.
    unfold Same_set. split.
    - unfold Included, In. intros.
      destruct H.
      apply Union_intror. auto.
      apply Union_introl. auto.
    - unfold Included, In. intros.
      destruct H.
      apply Union_intror. auto.
      apply Union_introl. auto.
  Qed.

  Lemma union_dec :
    forall T : Type,
      forall a b : Ensemble T,
        (forall t : T, In _ a t \/ ~In _ a t) ->
        (forall t : T, In _ b t \/ ~In _ b t) ->
        (forall t : T, In _ (Union _ a b) t \/ ~In _ (Union _ a b) t).
  Proof.
    intros.
    edestruct H.
    - left. unfold In. apply Union_introl. apply H1.
    - edestruct H0. left. unfold In. apply Union_intror. apply H2.
      right. intro. destruct H3 ; contradiction.
  Qed.

  Hint Resolve union_dec : sig.

  Lemma setminus_dec :
    forall T : Type,
      forall a b : Ensemble T,
        (forall t : T, In _ a t \/ ~In _ a t) ->
        (forall t : T, In _ b t \/ ~In _ b t) ->
        (forall t : T, In _ (Setminus _ a b) t \/ ~In _ (Setminus _ a b) t).
  Proof.
    intros.
    edestruct H.
    - edestruct H0. right. intro. unfold In, Setminus in H3.
      destruct H3. apply H4. apply H2.
      left. unfold In, Setminus. split ; auto. apply H1.
    - right. intro. unfold In, Setminus in H2. destruct H2. contradiction.
  Qed.

  Hint Resolve setminus_dec : sig.

  Variable sigA sigB : Signature action_t.

  Lemma sig_composition_commute :
    sig_composition sigA sigB = sig_composition sigB sigA.
  Proof.
    intros.
    unfold sig_composition.
    assert (Union action_t (intern sigA) (intern sigB) = Union action_t (intern sigB) (intern sigA)).
    apply union_commute.
    assert (Union action_t (output sigA) (output sigB) = Union action_t (output sigB) (output sigA)).
    apply union_commute.
    rewrite H. rewrite H0.
    assert (Union action_t (input sigA) (input sigB) = Union action_t (input sigB) (input sigA)).
    apply union_commute.
    rewrite H1.
    auto.
  Qed.

  Lemma included_local_act :
    Included _ (local sigA) (acts sigA).
  Proof.
    unfold Included,
           local,
           acts,
           In
    .
    intros.
    destruct H.
    - apply Union_introl. auto.
    - apply Union_intror. unfold In. unfold ext. apply Union_introl.
      auto.
  Qed.

  Hint Resolve included_local_act : sig.

   Lemma sig_composition_keep_intern :
    Included _ (intern sigA) (intern (sig_composition sigA sigB)).
  Proof.
    unfold Included, In, sig_composition.
    intros. simpl.
    apply Union_introl ; auto.
  Qed.

  Hint Resolve sig_composition_keep_intern : sig.

  Lemma sig_composition_keep_output :
    Included _ (output sigA) (output (sig_composition sigA sigB)).
  Proof.
    unfold Included, In, sig_composition.
    intros. simpl.
    apply Union_introl ; auto.
  Qed.

  Hint Resolve sig_composition_keep_output : sig.

  Lemma sig_composition_keep_local :
    Included _ (local sigA) (local (sig_composition sigA sigB)).
  Proof.
    unfold Included, local, In.
    intros.
    destruct H.
    - apply Union_introl. auto with sig.
    - apply Union_intror. apply Union_introl. auto with sig.
  Qed.

  Hint Resolve sig_composition_keep_local : sig.

  Hypothesis HsigA_dec :
    sig_dec sigA.
  Hypothesis HsigB_dec :
    sig_dec sigB.

  Lemma sig_composition_keep_acts :
    Included _ (acts sigA) (acts (sig_composition sigA sigB)).
  Proof.
    unfold Included, acts, In. intros.
    destruct H.
    - apply Union_introl.
      auto with sig.
    - apply Union_intror. unfold ext, In, sig_composition in *.
      destruct H.
      + apply Union_introl.
        auto with sig.
      + unfold sig_dec in *.
        assert (In action_t (output sigA) x \/ ~ In action_t (output sigA) x).
        apply HsigA_dec. destruct H0.
        * apply Union_introl. unfold In. apply Union_introl. auto.
        * assert (In action_t (output sigB) x \/ ~ In action_t (output sigB) x).
          apply HsigB_dec. destruct H1.
          apply Union_introl. unfold In. apply Union_intror. auto.
          apply Union_intror. repeat unfold In, Setminus. split.
          apply Union_introl. auto.
          intro. destruct H2 ; contradiction.
  Qed.

  Hint Resolve sig_composition_keep_acts : sig.

  Lemma sig_composition_dec :
    sig_dec (sig_composition sigA sigB).
  Proof.
    unfold sig_dec. intro.
    unfold sig_composition.
    simpl.
    repeat split.
    - apply union_dec ; intro ; apply HsigA_dec || apply HsigB_dec.
    - apply union_dec ; intro ; apply HsigA_dec || apply HsigB_dec.
    - apply setminus_dec ; intro ; apply union_dec ; apply HsigA_dec || apply HsigB_dec.
  Qed.

  Hint Resolve sig_composition_dec : sig.

  Lemma extsig_dec :
    sig_dec (extsig sigA).
  Proof.
    unfold extsig, sig_dec.
    intro.
    repeat split ; simpl ; auto.
    - right. unfold In. intro. destruct H.
    - apply HsigA_dec.
    - apply HsigA_dec.
  Qed.

  Hint Resolve extsig_dec : sig.

  Unset Implicit Arguments.
End Signature.

Hint Rewrite act_to_local_input act_to_ext_intern : sig.

Hint Resolve union_dec setminus_dec included_local_act sig_composition_keep_intern
             sig_composition_keep_output sig_composition_keep_local sig_composition_keep_acts
             sig_composition_dec extsig_dec local_in_act ext_in_act intern_in_local output_in_local
  : sig.

(*
  We will create the IOA as a monad.
  We create an invalid state, None,
  which will be interpreted as an
  invalid state. The reason for that
  is to enforced a deterministic
  behaviour of the system and making
  it easier to specify some properties
  like enabled actions.
*)

(*
  Note : we need this strong assumption on sig for the
  compositions lemma. If we only have decidability on the actions,
  we cannot forward the lemma because of the way composition is built.
 *)

Record IOA (action_t : Type) : Type :=
  mkIOA {
      state_t : Type;
      sig : Signature action_t;
      initial : state_t -> Prop;
      transition : state_t -> action_t -> option state_t;
      act_dec : sig_dec sig;
    }
.

Arguments state_t {_}.
Arguments sig {_}.
Arguments initial {_} _.
Arguments transition {_} _ _.
Arguments act_dec {_}.

Section IOA.
  Set Implicit Arguments.
  Variable action_t : Type.

  (* For now, we assume that every action that
     is not in acts let the state unchange.
     It is easier than assuming the decidbility
     of sig I think
   *)

  Definition monad
    (ioa : IOA action_t)
    (s : option ioa.(state_t))
    (a : action_t)
    : option ioa.(state_t) :=
    match s with
      | None => None
      | Some ss => ioa.(transition) ss a
    end
  .

  Definition action_enabled
    (ioa : IOA action_t)
    (s : option ioa.(state_t))
    (a : action_t)
    : Prop :=
    monad ioa s a <> None
  .

  (* We want to define a trace as finite because
     traces will be executed and it is easier to
     deal with liveness this way I think.
     also because I really don't want to deal
     with inductive types, too difficult for me *)
  Definition trace_t (action_t : Type) : Type := list action_t.

  Fixpoint execute_trace
    (ioa : IOA action_t)
    (s : option ioa.(state_t))
    (t : trace_t action_t)
    : option ioa.(state_t) :=
    match t with
      | [] => s
      | h::t' => execute_trace ioa (monad ioa s h) t'
    end
  .

  (*Notation "ioa >-> s t" := (execute_trace ioa s t) (at level 76, right associativity).*)


  Notation "[ ioa ] s >-> t" := (execute_trace ioa s t) (at level 70).

  Definition trace_enabled
    (ioa : IOA action_t)
    (s : option ioa.(state_t))
    (t : trace_t action_t)
    : Prop :=
    [ioa] s >-> t <> None.

  Lemma trace_not_enabled_on_none :
    forall ioa : IOA action_t,
    forall t : trace_t action_t,
      ~ trace_enabled ioa None t.
  Proof.
    intro ioa.
    induction t ; auto.
  Qed.

  Hint Resolve trace_not_enabled_on_none : ioa.

  Definition trace_live
    (ioa : IOA action_t)
    (s : option ioa.(state_t))
    (t : trace_t action_t)
    : Prop :=
    forall a : action_t,
      In _ (local ioa.(sig)) a ->
      ~ (action_enabled ioa ([ioa] s >-> t) a)
  .

  (*
    A correct trace is a trace that is live
    and enabled.
   *)
  Definition trace_correct
    (ioa : IOA action_t)
    (s : option ioa.(state_t))
    (t : trace_t action_t)
    : Prop :=
    trace_enabled ioa s t /\ trace_live ioa s t
  .

  Definition trace_valid
    (ioa : IOA action_t)
    (t : trace_t action_t)
    : Prop :=
    exists s : ioa.(state_t),
      ioa.(initial) s /\ trace_correct ioa (Some s) t
  .

  (*
    The composition of two automata is
    simply the composition of the functions
   *)

  (*
    T?*T'?
   *)
  Definition option_prod_t (T T' : Type) : Type := (option T)*(option T').

  (*
    (T*T')?
   *)
  Definition quotient_t (T T' : Type) : Type := option (T*T').

  (*
    This function is a quotient for the
    equivalence relation which merges the
    None value on the set (option T, option T')
   *)
  Definition quotient_option
    {T T' : Type}
    (p : option_prod_t T T')
    : quotient_t T T' :=
    match p with
      | (Some va, Some vb) => Some (va, vb)
      | _ => None
    end
  .

  Hint Unfold quotient_option : ioa.

  (*Notation "( a , b ) ~>" := (quotient_option a b).*)
  Notation "a ~>" := (quotient_option a) (at level 1).

  Definition ioa_composition
    (ioaA ioaB : IOA action_t)
    : IOA action_t :=
    mkIOA
      _
      (ioaA.(state_t) * ioaB.(state_t))
      (sig_composition ioaA.(sig) ioaB.(sig))
      (fun s => ioaA.(initial) (fst s) /\ ioaB.(initial) (snd s))
      (
        fun s a =>
          ((ioaA.(transition) (fst s) a),
            (ioaB.(transition) (snd s) a)) ~>
      )
      (sig_composition_dec ioaA.(act_dec) ioaB.(act_dec))
  .

  Notation "a /*/ b" := (ioa_composition a b) (at level 50).

  Definition prod_state_t
    (ioaA ioaB : IOA action_t)
    : Type :=
    option_prod_t ioaA.(state_t) ioaB.(state_t).

  Definition quotient_state_t
    (ioaA ioaB : IOA action_t)
    : Type :=
    quotient_t ioaA.(state_t) ioaB.(state_t).

  Variable ioaA ioaB : IOA action_t.

  (*
    A fondamental lemma is that the monad
    'descent au quotient'
   *)

  Lemma monad_compat_with_quotient_option :
    forall a : action_t,
    forall (s : prod_state_t ioaA ioaB),
      monad (ioaA /*/ ioaB) s~> a =
        ( (monad ioaA (fst s) a), (monad ioaB (snd s) a) )~>
  .
  Proof.
    intros.
    destruct s as (sA, sB).
    unfold
      monad,
      ioa_composition,
      quotient_option.
    simpl.
    destruct sA, sB ; auto.
    destauto ; auto.
  Qed.

  (*
    The lemma is extendible to traces
   *)
  Lemma execute_trace_compat_with_quotient_option :
    forall t :  trace_t action_t,
    forall (s : prod_state_t ioaA ioaB),
      [ioaA /*/ ioaB] s~> >-> t =
        ( ([ioaA] (fst s) >-> t), ([ioaB] (snd s) >-> t) ) ~>
  .
  Proof.
    induction t.
    - destruct s. auto.
    - intros. simpl.
      rewrite monad_compat_with_quotient_option.
      auto.
  Qed.

  (*
    And we can then deduce the equivalence on
    enabled actions and traces
   *)

  Lemma action_enabled_compat_with_quotient_option :
    forall a : action_t,
    forall (s : prod_state_t ioaA ioaB),
      action_enabled (ioaA /*/ ioaB) s~> a <->
        (action_enabled ioaA (fst s) a) /\ (action_enabled ioaB (snd s) a)
  .
  Proof.
    intros.
    unfold action_enabled.
    rewrite monad_compat_with_quotient_option.
    unfold quotient_option.
    repeat (simpl_match ; auto) ;
      split ; intro HH ; try discriminate ; auto ; try split ; try discriminate ; destruct HH ; auto.
  Qed.

  Lemma trace_enabled_compat_with_quotient_option :
    forall t : trace_t action_t,
    forall (s : prod_state_t ioaA ioaB),
      trace_enabled (ioaA /*/ ioaB) s~> t <->
        (trace_enabled ioaA (fst s) t) /\ (trace_enabled ioaB (snd s) t)
  .
  Proof.
    intros.
    unfold trace_enabled.
    rewrite execute_trace_compat_with_quotient_option.
    unfold quotient_option.
    repeat (simpl_match ; auto) ;
      split ; intro HH ; try discriminate ; auto ; try split ; try discriminate ; destruct HH ; auto.
  Qed.

  (*
    Also extend liveness

    From now on, we also need decidability
    on actions because we need to know if
    the action is local or not

    Note : it is only possible to extend
    liveness on an enabled trace because
    we don't want the last state to be
    not None. Therefore we directly prove
    the compatibility of :

          enabled + live = correct

    traces.

    Note 2 : we also need hypothesis
    on input enabled automata. The
    reason for that is that we need
    to have the validity of the next
    in case of enabled output action.
   *)

  Definition input_enabled (ioa : IOA action_t) : Prop :=
    forall a : action_t,
      In _ (input ioa.(sig)) a ->
      forall s, action_enabled ioa s a.

  Definition action_coherent (ioa : IOA action_t) : Prop :=
    forall a : action_t,
      ~In _ (acts ioa.(sig)) a ->
      forall s, monad ioa s a = s.

  Definition ioa_compatible (ioaA ioaB : IOA action_t) : Prop :=
    Disjoint _ (local ioaA.(sig)) (local ioaB.(sig)).

  (*
    If the two sub-traces are correct, then the global
    trace also is. This result doesn't need any assumptions,
    so we put it here.
   *)

  Lemma traces_correct_then_composition_correct :
    forall t : trace_t action_t,
    forall (sA : option ioaA.(state_t)) (sB : option ioaB.(state_t)),
      (trace_correct ioaA sA t) /\ (trace_correct ioaB sB t) ->
      trace_correct (ioaA /*/ ioaB) (sA, sB)~> t.
  Proof.
    unfold trace_correct.
    intros * [[HAen HAlive] [HBen HBlive]].
    destruct sA, sB.
    - split.
      + apply trace_enabled_compat_with_quotient_option. auto.
      + unfold trace_live in *.
        intros.
        intro.
        rewrite execute_trace_compat_with_quotient_option in H0.
        apply action_enabled_compat_with_quotient_option in H0.
        destruct H ; destruct H.
        * assert (In action_t (local (sig ioaA)) x).
          apply intern_in_local. auto.
          apply HAlive in H1.
          tauto.
        * assert (In action_t (local (sig ioaB)) x).
          apply intern_in_local. auto.
          apply HBlive in H1.
          tauto.
        * assert (In action_t (local (sig ioaA)) x).
          apply output_in_local. auto.
          apply HAlive in H1.
          tauto.
        * assert (In action_t (local (sig ioaB)) x).
          apply output_in_local. auto.
          apply HBlive in H1.
          tauto.
    - simpl.
      assert (~trace_enabled ioaB None t).
      auto with ioa.
      contradiction.
    - simpl.
      assert (~trace_enabled ioaA None t).
      auto with ioa.
      contradiction.
    - simpl.
      assert (~trace_enabled ioaB None t).
      auto with ioa.
      contradiction.
  Qed.



  (*
    TODO:
    Might be possible to use
    lighter hypothesis like :
    acts_dec instead of sig_dec

    Note : removed as we enforced the decidability in the def
   *)
  (*
  Hypothesis HioaA_sig_dec :
    sig_dec ioaA.(sig).
  Hypothesis HioaB_sig_dec :
    sig_dec ioaB.(sig).*)

  Hypothesis HioaA_input_enabled :
    input_enabled ioaA.
  Hypothesis HioaB_input_enabled :
    input_enabled ioaB.

  Hypothesis HioaA_coherent :
    action_coherent ioaA.
  Hypothesis HioaB_coherent :
    action_coherent ioaB.

  Hypothesis Hioa_compatible :
    ioa_compatible ioaA ioaB.

  Lemma trace_correct_compat_with_quotient_option :
    forall t : trace_t action_t,
    forall (sA : option ioaA.(state_t)) (sB : option ioaB.(state_t)),
      trace_correct (ioaA /*/ ioaB) (sA, sB)~> t <->
        (trace_correct ioaA sA t) /\ (trace_correct ioaB sB t)
  .
  Proof.
    intros.
    split.
    - intro.
      split.
      + unfold trace_correct.
        split.
        * destruct H.
          apply trace_enabled_compat_with_quotient_option in H. apply H.
        * destruct H.
          apply trace_enabled_compat_with_quotient_option in H.
          destruct H.
          unfold trace_live in *.
          intros.
          unfold action_enabled.
          case_eq (monad ioaA ([ioaA] sA >-> t) a).
          {
            intros.
            (* because the action is None, one of them is none *)
            (* in this case, it is B *)
            case_eq (monad ioaB ([ioaB] sB >-> t) a) ; intros.

            eapply sig_composition_keep_local in H2.
            apply H0 in H2.
            rewrite execute_trace_compat_with_quotient_option in H2.
            contradict H2.
            apply action_enabled_compat_with_quotient_option.
            simpl. unfold action_enabled. rewrite H3, H4.
            split ; discriminate.
            edestruct sig_act_dec.
            apply ioaB.(act_dec).
            Unshelve. 3: apply a.

            (* if a is an action of B *)
            rewrite act_to_local_input in H5.
            destruct H5.

            (* if a is in local B *)
            unfold ioa_compatible in *.
            destruct Hioa_compatible.
            specialize H6 with x.
            contradict H6.
            unfold In.
            apply Intersection_intro ; auto.

            (* if a is in input B *)
            apply HioaB_input_enabled in H5.
            specialize H5 with ([ioaB] sB >-> t).
            contradiction.

            (* if a is not an action of B *)
            unfold action_coherent in *.
            eapply HioaB_coherent in H5.
            rewrite H5 in H4.
            unfold trace_enabled in H1.
            contradiction.
          }
          {
            auto.
          }
      + unfold trace_correct.
        split.
        * destruct H.
          apply trace_enabled_compat_with_quotient_option in H. apply H.
        * destruct H.
          apply trace_enabled_compat_with_quotient_option in H.
          destruct H.
          unfold trace_live in *.
          intros.
          unfold action_enabled.
          case_eq (monad ioaB ([ioaB] sB >-> t) a).
          {
            intros.
            (* because the action is None, one of them is none *)
            (* in this case, it is B *)
            case_eq (monad ioaA ([ioaA] sA >-> t) a) ; intros.

            eapply sig_composition_keep_local in H2.
            rewrite sig_composition_commute in H2.
            apply H0 in H2.
            rewrite execute_trace_compat_with_quotient_option in H2.
            contradict H2.
            apply action_enabled_compat_with_quotient_option.
            simpl. unfold action_enabled. rewrite H3, H4.
            split ; discriminate.
            edestruct sig_act_dec.
            apply ioaA.(act_dec).
            Unshelve. 3: apply a.

            (* if a is an action of B *)
            rewrite act_to_local_input in H5.
            destruct H5.

            (* if a is in local B *)
            unfold ioa_compatible in *.
            destruct Hioa_compatible.
            specialize H6 with x.
            contradict H6.
            unfold In.
            apply Intersection_intro ; auto.

            (* if a is in input B *)
            apply HioaA_input_enabled in H5.
            specialize H5 with ([ioaA] sA >-> t).
            contradiction.

            (* if a is not an action of B *)
            unfold action_coherent in *.
            eapply HioaA_coherent in H5.
            rewrite H5 in H4.
            unfold trace_enabled in H1.
            contradiction.
          }
          {
            auto.
          }
    - apply traces_correct_then_composition_correct.
  Qed.

  (*
    After this main theorem, we can continue with
    creating tools for the compositions of more
    automata easily
   *)

  (*
    "Identity" automata.
    It is not an actual identity in the sence of equality
    but we will prove later that a /*/ id ~ id /*/ a ~ a
    where ~ is a relation of bisimulation (with a very specific def)
    between the two automata.
   *)

  Definition ioa_neutral
    : IOA action_t.
    refine (
        mkIOA
          _
          unit
          (empty_sig action_t)
          (fun s => True)
          (fun s a => Some s)
          _
      )
    .
    unfold sig_dec, empty_sig.
    simpl. intro.
    repeat split ; right ; unfold In ; intro H ; destruct H.
  Defined.

  Fixpoint ioa_composition_list
    (l : list (IOA action_t))
    : IOA action_t :=
    match l with
      | nil => ioa_neutral
      | a::nil => a
      | a::t => a /*/ (ioa_composition_list t)
    end.
End IOA.

Notation "[ ioa ] s >-> t" := (execute_trace ioa s t) (at level 70).
Notation "a ~>" := (quotient_option a) (at level 1).
Notation "a /*/ b" := (ioa_composition a b) (at level 50).

Section Simulation.
  (*
    Definition of abstraction, refinement, and simulation relations
   *)

  (*
    Hiding some actions
   *)
  Definition
    hide
      {action_t : Type}
      (ioa : IOA action_t)
      (p : Ensemble action_t)
    : IOA action_t.
    refine (
    mkIOA
      _
      ioa.(state_t)
      (sig_hide ioa.(sig) p)
      ioa.(initial)
      ioa.(transition)
      _
    ).
    unfold sig_dec, sig_hide.
    simpl. intro.
    split ; [|split].
    -

  Fixpoint
    filter
      {action_t : Type}
      (sig : Signature action_t)
      (act_dec : act_dec_t sig)
      (t : trace_t action_t)
    : trace_t action_t :=
    match t with
      | nil => nil
      | a::t' =>
          if act_dec a then
            a::(@filter _ sig act_dec t')
          else
            @filter _ sig act_dec t'
    end.

  (*
    I want to define a definition of simulation specific to IOA.
    The reason for that is that it make it easier to reason about it.

    A simulation H from A to B is a function that associate each :
    - output action of A to an output action of B
    - input action of A to an input action of B
    - for every state s and every external action enabled in
      automata A, H(a) is also enabled in B


    There are mainly three ways to define a partial function :
    1. either the monad Option
    2. either using specification ({ x | P })
    3. either using a dummy for the value we are interested in

    The option 2. is very complex to manipulate so we prefer to avoid.
    Therefore we are left with option 1. and 3.

    I decided to go for option 3. as it makes it easier to manipulate
    and is just enough for all the proof, the only downside is when defining
    the simulation function, it can be a bit disrupting at first.
   *)

  Definition
    simulation_t
    :=
    fun a b : Type => a -> b
  .

  Definition
    simulation_spec
      {action_A_t action_B_t : Type}
      (ioaA : IOA action_A_t)
      (ioaB : IOA action_B_t)
      (S : simulation_t action_A_t action_B_t)
    : Prop :=
    forall a : action_A_t,
      (
        In _ (input ioaA.(sig)) a ->
        In _ (input ioaB.(sig)) (S a)
      )
      /\ (
        In _ (output ioaA.(sig)) a ->
        In _ (output ioaB.(sig)) (S a)
      )
  .

  Lemma
    simulation_spec_refl :
    forall T : Type,
    forall ioa : IOA T,
      simulation_spec ioa ioa (fun a => a)
  .
  Proof.
    intros.
    unfold simulation_spec.
    auto.
  Qed.

  Lemma simulation_spec_trans :
    forall TA TB TC : Type,
    forall ioaA : IOA TA, forall ioaB : IOA TB, forall ioaC : IOA TC,
    forall S : simulation_t TA TB,
    forall S': simulation_t TB TC,
      simulation_spec ioaA ioaB S ->
      simulation_spec ioaB ioaC S' ->
      simulation_spec ioaA ioaC (fun a => S' (S a))
  .
  Proof.
    intros.
    unfold simulation_spec in *.
    intro.
    split ; intro ; apply H0 ; apply H ; auto.
  Qed.

  Fixpoint
    simulate
      {action_A_t action_B_t : Type}
      (S : simulation_t action_A_t action_B_t)
      (t : trace_t action_A_t)
      : trace_t action_B_t :=
    match t with
      | nil => nil
      | a::t' =>
          (S a)::(simulate S t')
    end
  .

  Definition
    simulation
      {action_A_t action_B_t : Type}
      (ioaA : IOA action_A_t)
      (ioaB : IOA action_B_t)
      (S : simulation_t action_A_t action_B_t)
      (act_A_dec : act_dec_t ioaA.(sig))
      (act_B_dec : act_dec_t ioaB.(sig))
    : Prop :=
    simulation_spec ioaA ioaB S /\
      forall t : trace_t action_A_t,
        trace_valid ioaA t ->
        exists t' : trace_t action_B_t,
          trace_valid ioaB t' /\
            simulate S (filter act_A_dec t) = filter act_B_dec t'
  .

  Lemma
    simulation_refl :
    forall T : Type,
    forall ioa : IOA T,
    forall act_dec : act_dec_t ioa.(sig),
      simulation ioa ioa (fun a => a) act_dec act_dec
  .
  Proof.
    intros.
    unfold simulation.
    split.
    - apply simulation_spec_refl.
    - intros.
      exists t. split ; auto.
      clear H.
      induction t ; auto.
      simpl.
      simpl_match. rewrite IHt. auto.
      auto.
  Qed.

  Lemma
    simulation_trans :
    forall TA TB TC : Type,
    forall ioaA : IOA TA, forall ioaB : IOA TB, forall ioaC : IOA TC,
    forall act_A_dec : act_dec_t ioaA.(sig),
    forall act_B_dec : act_dec_t ioaB.(sig),
    forall act_C_dec : act_dec_t ioaC.(sig),
    forall S : simulation_t TA TB,
    forall S': simulation_t TB TC,
      simulation ioaA ioaB S act_A_dec act_B_dec ->
      simulation ioaB ioaC S' act_B_dec act_C_dec ->
      simulation ioaA ioaC (fun x => S' (S x)) act_A_dec act_C_dec
  .
  Proof.
    intros.
    unfold simulation in *.
    split.
    - eapply simulation_spec_trans.
      apply H.
      apply H0.
    - intros.
      destruct H as [_ H].
      destruct H0 as [_ H0].
      specialize H with t.
      apply H in H1. clear H. destruct H1 as [t_tmp [H1 H]].
      specialize H0 with t_tmp.
      apply H0 in H1. clear H0.
      destruct H1 as [t' [H1 H0]].
      exists t'. split ; auto.
      rewrite <-H in H0.
      rewrite <-H0.
      clear H H0.
      induction t ; auto.
      simpl ; simpl_match ; rewrite IHt ; auto.
  Qed.
  
  Definition
    bisimulation
      {action_A_t action_B_t : Type}
      (ioaA : IOA action_A_t)
      (ioaB : IOA action_B_t)
      (S : simulation_t action_A_t action_B_t)
      (S__inv : simulation_t action_B_t action_A_t)
      (act_A_dec : act_dec_t ioaA.(sig))
      (act_B_dec : act_dec_t ioaB.(sig))
    : Prop :=
    simulation ioaA ioaB S act_A_dec act_B_dec /\
      simulation ioaB ioaA S__inv act_B_dec act_A_dec /\
      (forall a, S (S__inv a) = a) /\ (forall b, S__inv (S b) = b)
  .

  Lemma
    bisimulation_commute :
    forall TA TB : Type,
    forall ioaA : IOA TA, forall ioaB : IOA TB, forall S S__inv act_A_dec act_B_dec,
      bisimulation ioaA ioaB S S__inv act_A_dec act_B_dec ->
      bisimulation ioaB ioaA S__inv S act_B_dec act_A_dec
  .
  Proof.
    unfold bisimulation.
    intros.
    split ; [ | split].
    - unfold simulation in *.
      destruct H as [_ [H _]].
      split.
      + destruct H as [H _].
        unfold simulation_spec in *.
        intro.
        split ; intro ; apply H ; auto.
      + apply H.
    - destruct H as [H _].
      unfold simulation in *.
      split.
      + destruct H as [H _].
        unfold simulation_spec in *.
        intro.
        split ; intro ; apply H ; auto.
      + apply H.
    - intros ; split ; apply H ; auto.
  Qed.

  Definition
    ioa_equivalent
      {action_A_t action_B_t : Type}
      (ioaA : IOA action_A_t)
      (ioaB : IOA action_B_t)
      (act_A_dec : act_dec_t ioaA.(sig))
      (act_B_dec : act_dec_t ioaB.(sig))
    : Prop :=
    exists S S__inv,
      bisimulation ioaA ioaB S S__inv act_A_dec act_B_dec.

  (*
    Bisimulation is an equivalence relation
   *)
  Lemma
    ioa_refl :
    forall T : Type,
    forall ioa : IOA T,
    forall act_dec : act_dec_t ioa.(sig),
      ioa_equivalent ioa ioa act_dec act_dec
  .
  Proof.
    intros.
    exists (fun a => a), (fun a => a).
    unfold bisimulation.
    split ; [|split].
    - apply simulation_refl.
    - apply simulation_refl.
    - auto.
  Qed.

  Lemma
    ioa_sym :
    forall TA TB : Type,
    forall ioaA : IOA TA, forall ioaB : IOA TB,
    forall act_A_dec : act_dec_t ioaA.(sig),
    forall act_B_dec : act_dec_t ioaB.(sig),
      ioa_equivalent ioaA ioaB act_A_dec act_B_dec ->
        ioa_equivalent ioaB ioaA act_B_dec act_A_dec
  .
  Proof.
    unfold ioa_equivalent.
    intros.
    destruct H.
    destruct H.
    exists x0, x.
    unfold bisimulation in *.
    split ; [ |split ] ; try apply H.
    intros. split ; apply H ; auto.
  Qed.

  Lemma
    ioa_transitive :
    forall TA TB TC : Type,
    forall ioaA : IOA TA, forall ioaB : IOA TB, forall ioaC : IOA TC,
    forall act_A_dec : act_dec_t ioaA.(sig),
    forall act_B_dec : act_dec_t ioaB.(sig),
    forall act_C_dec : act_dec_t ioaC.(sig),
      ioa_equivalent ioaA ioaB act_A_dec act_B_dec ->
        ioa_equivalent ioaB ioaC act_B_dec act_C_dec ->
        ioa_equivalent ioaA ioaC act_A_dec act_C_dec
  .
  Proof.
    intros.
    unfold ioa_equivalent in *.
    destruct H.
    destruct H.
    destruct H0.
    destruct H0.
    exists (fun a => x1 (x a)), (fun a => x0 (x2 a)).
    unfold bisimulation in *.
    split ; [|split].
    - eapply simulation_trans.
      apply H.
      apply H0.
    - eapply simulation_trans.
      apply H0. apply H.
    - intros.
      destruct H0 as [_ [_ [Ha0 Hb0]]].
      destruct H as [_ [_ [Ha Hb]]].
      split.
      + intros. rewrite Ha. auto.
      + intros. rewrite Hb0. auto.
  Qed.

  (*
    It means that we can define a quotient over the set of IOA.
    In particular, this quotient is compatible with the product operation :
                  /*/
      IOA*IOA -----------> IOA
        |                   |
        |                   |
Q_~*Q_~ |                   | Q_~
        |                   |
        v                   v
   IOA/~*IOA/~ ---------> IOA/~
                /*/

    Or, equivalently, that every equivalent pairs of ioa, when composed,
    gives equivalent ioa
   *)

  Lemma
    composition_compat_with_equiv :
    forall T T' : Type,
    forall ioaA ioaB : IOA T,
    forall ioaA' ioaB' : IOA T',
    forall act_A_dec : act_dec_t ioaA.(sig),
    forall act_A'_dec : act_dec_t ioaA'.(sig),
    forall act_B_dec : act_dec_t ioaB.(sig),

      ioa_equivalent ioaA ioaA'

  (*
    Now we can talk about the identity ioa defined above.
    If we compose with this operator, we are
   *)

  
  (*
  The goals are :
  - Tying to make composition as easy as possible
  - Proving result on simulation and making good definitions
  - Adding fairness and results to make it easier to reason about it
  - making reasonning about temporality easier
   *)

  (* ---------------------------------------------------------------

   We first defines some basic definitions on the execution of an IOA

   --------------------------------------------------------------- *)

  (* A section is a tripplet (state, action, state) *)

  Definition section_t : Type := ioa.(state_t) * actions_t * ioa.(state_t).

  Definition is_section (sect : section_t) : Prop :=
    let '(s, a, s') := sect in
    ioa.(transition) s a = Some s'.

  (* A fragment of execution defines the type used to represent the traces *)
  Definition fragment_t : Type := nat -> section_t.

  (* check if the states are matching from one to the next *)
  Definition is_fragment (f : fragment_t) : Prop :=
    forall i : nat,
      let '(_, _, s) := (f i) in
      let '(s', _, _) := (f (i+1)) in
      s = s'.

  (* Check if each sections are section of execution *)
  Definition is_exec (f : fragment_t) : Prop :=
    forall i : nat, is_section (f i).

  (* A trace is a fragment which is an execution *)
  Definition is_trace (t : fragment_t) : Prop :=
    is_fragment t /\ is_exec t.

  (* ---------------------------------------------------------------

   Then we definine what is the composition of automata

   --------------------------------------------------------------- *)

  (* A composition is construct around a type, so that it is easiser
     to manipulate in proofs *)
  Definition composer_t (t : Type) : Type := t -> IOA actions_t.

  Definition composition {t : Type} (c : composer_t t) : IOA actions_t :=
    mkIOA
      _

  .
