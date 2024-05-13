Require Import common.IOA.
Require Import common.LTL.
Require Import common.buffer.
Require Import P2P.P2P.
Require Import common.tactic.
Require Import reliable_broadcast.definitions.
Require Import reliable_broadcast.transition_prop.
Require Import Lia.
Require Import Arith.
Require Import Bool.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.

Close Scope ltl_scope.

Section Leader_not_byzentine.
  Variable root_message : Message.

  Variable label :
    nat -> Process.
  Hypothesis label_is_bij :
    forall p, exists! q, q < count /\ label q = p.

  Lemma label_is_inj :
    forall p q, label p = label q -> p < count -> q < count ->
           p = q.
  Proof.
    intros.
    destruct label_is_bij with (label p).
    destruct H2.
    assert (x = p).
    apply H3. auto.
    subst x.
    apply H3. auto.
  Qed.

  Lemma label_is_surj :
    forall p, exists q, q < count /\ label q = p.
  Proof.
    intros.
    destruct label_is_bij with p.
    exists x.
    unfold unique in H. destruct H. auto.
  Qed.

  Inductive Composition_t (f : nat) :=
    | Correct_T : forall n, n < count - f -> Composition_t f
    | Corrupted_T : forall n, count - f <= n < count -> Composition_t f
    | Network_T : Composition_t f.

  Definition Ref
    (f : nat)
    (byzentine : Process -> IOADef BrachaRBAction)
    (c : Composition_t f) :
    IOADef BrachaRBAction :=
    match c with
    | Correct_T _ n _ => BrachaRBProcess f (label n)
    | Corrupted_T _ n _ => byzentine (label n)
    | Network_T _ => P2PNetwork
    end.

  Lemma composition_extended_hyp
    (f : nat)
    (byzentine : Process -> IOADef BrachaRBAction)
    (Hbyzentine :
      forall p : Process,
        is_byzentine (BrachaRBProcess f p) (byzentine p)
    ) :
    CompositionExtendedHyp
      eq
      (Ref f byzentine).
  Proof.
    unfold is_byzentine in Hbyzentine. split ; intros.
    - contradict H1.
      induction act ; simpl_ActionClass ; induction i ; discriminate || auto ;
        intros ; rewrite <-Hbyzentine ; simpl_ActionClass ; discriminate
      .
    - induction act, i, j ; simpl_ActionClass ; try discriminate ;
        simpl_ActionClass ; try discriminate ; try rewrite <-Hbyzentine in * ; try simpl_ActionClass ;
        try (contradiction || discriminate) ; destruct p as [pval pproof] ; try simpl_ActionClass ;
        simpl in * ; subst pval ;
        try (apply process_proof_irrelevence in H2 ; apply label_is_inj in H2 ; try lia ; subst n ;
             assert (l = l0) || assert (a = a0) ; try apply proof_irrelevance ; subst l || subst a ; contradiction
          ) ; inversion H0.
  Qed.

  Definition exists_output (act : BrachaRBAction) : bool :=
    match act with
      | BrachaRBBroadcast _ => false
      | BrachaRBDeliver _ _ | BrachaRBP2PSend _ _ _  | BrachaRBP2PRecv _ _ _ => true
    end.

  Lemma exists_output_spec
    (f : nat)
    (byzentine : Process -> IOADef BrachaRBAction)
    (Hbyzentine :
      forall p : Process,
        is_byzentine (BrachaRBProcess f p) (byzentine p)
    ) :
    OutputSpec (Ref f byzentine) exists_output.
  Proof.
    hnf. intro. split ; intro.
    - induction act.
      + unfold exists_output in H. inversion H.
      + destruct label_is_bij with p. destruct H0.
        case_eq (x <? count - f) ; intros ; simpl_arith_bool.
        exists (Correct_T f x H2). simpl_ActionClass. destruct H0. rewrite H4 in H3. contradiction.
        assert (count - f <= x < count). lia. clear H2.
        exists (Corrupted_T f x H3). simpl_ActionClass. rewrite <-Hbyzentine.
        simpl_ActionClass. destruct H0. rewrite H4 in H2. contradiction.
      + exists (Network_T f). simpl_ActionClass.
      + destruct label_is_bij with p. destruct H0.
        case_eq (x <? count - f) ; intros ; simpl_arith_bool.
        exists (Correct_T f x H2). simpl_ActionClass. destruct H0. rewrite H4 in H3. contradiction.
        assert (count - f <= x < count). lia. clear H2.
        exists (Corrupted_T f x H3). simpl_ActionClass. rewrite <-Hbyzentine.
        simpl_ActionClass. destruct H0. rewrite H4 in H2. contradiction.
    - destruct H. induction act, x ; simpl_ActionClass ; inversion H. clear H1.
      rewrite <-Hbyzentine in H. simpl_ActionClass ; inversion H.
  Qed.

  Definition exists_input (act : BrachaRBAction) : bool :=
    match act with
      | BrachaRBBroadcast _ | BrachaRBP2PSend _ _ _ | BrachaRBP2PRecv _ _ _ => true
      | BrachaRBDeliver _ _ => false
    end.

  Lemma exists_input_spec
    (f : nat)
    (byzentine : Process -> IOADef BrachaRBAction)
    (Hbyzentine :
      forall p : Process,
        is_byzentine (BrachaRBProcess f p) (byzentine p)
    ) :
    InputSpec (Ref f byzentine) exists_input.
  Proof.
    hnf. intro. split ; intro.
    - induction act.
      + destruct label_is_bij with process_zero. destruct H0.
        case_eq (x <? count - f) ; intros ; simpl_arith_bool.
        exists (Correct_T f x H2). simpl_ActionClass. destruct H0. rewrite H4 in H3. contradiction.
        assert (count - f <= x < count). lia. clear H2.
        exists (Corrupted_T f x H3). simpl_ActionClass. rewrite <-Hbyzentine.
        simpl_ActionClass. destruct H0. rewrite H4 in H2. contradiction.
      + unfold exists_input in H. inversion H.
      + destruct label_is_bij with p. destruct H0.
        case_eq (x <? count - f) ; intros ; simpl_arith_bool.
        exists (Correct_T f x H2). simpl_ActionClass. destruct H0. rewrite H4 in H3. contradiction.
        assert (count - f <= x < count). lia. clear H2.
        exists (Corrupted_T f x H3). simpl_ActionClass. rewrite <-Hbyzentine.
        simpl_ActionClass. destruct H0. rewrite H4 in H2. contradiction.
      + exists (Network_T f). simpl_ActionClass.
    - destruct H. induction act, x ; simpl_ActionClass ; inversion H. clear H1.
      rewrite <-Hbyzentine in H. simpl_ActionClass ; inversion H.
  Qed.

  Definition forall_unused (act : BrachaRBAction) : bool :=
    false.

  Lemma forall_unused_spec
    (f : nat)
    (byzentine : Process -> IOADef BrachaRBAction)
    (Hbyzentine :
      forall p : Process,
        is_byzentine (BrachaRBProcess f p) (byzentine p)
    ) :
    UnusedSpec (Ref f byzentine) forall_unused.
  Proof.
    hnf. intro. split ; intro.
    - induction act ; unfold exists_input in H ; inversion H.
    - induction act.
      + destruct label_is_bij with process_zero. destruct H0.
        case_eq (x <? count - f) ; intros ; simpl_arith_bool.
        specialize H with (Correct_T f x H2). simpl_ActionClass. inversion H. destruct H0. rewrite H4 in H3.
        simpl in H3. contradiction.
        assert (count - f <= x < count). lia. clear H2.
        specialize H with (Corrupted_T f x H3). simpl_ActionClass. rewrite <-Hbyzentine in H.
        simpl_ActionClass. inversion H. destruct H0. rewrite H4 in H2. contradiction.
      + destruct label_is_bij with p. destruct H0.
        case_eq (x <? count - f) ; intros ; simpl_arith_bool.
        specialize H with (Correct_T f x H2). simpl_ActionClass. inversion H. destruct H0. rewrite H4 in H3.
        simpl in H3. contradiction.
        assert (count - f <= x < count). lia. clear H2.
        specialize H with (Corrupted_T f x H3). simpl_ActionClass. rewrite <-Hbyzentine in H.
        simpl_ActionClass. inversion H. destruct H0. rewrite H4 in H2. contradiction.
      + destruct label_is_bij with p. destruct H0.
        case_eq (x <? count - f) ; intros ; simpl_arith_bool.
        specialize H with (Correct_T f x H2). simpl_ActionClass. inversion H. destruct H0. rewrite H4 in H3.
        simpl in H3. contradiction.
        assert (count - f <= x < count). lia. clear H2.
        specialize H with (Corrupted_T f x H3). simpl_ActionClass. rewrite <-Hbyzentine in H.
        simpl_ActionClass. inversion H. destruct H0. rewrite H4 in H2. contradiction.
      + destruct label_is_bij with p. destruct H0.
        case_eq (x <? count - f) ; intros ; simpl_arith_bool.
        specialize H with (Correct_T f x H2). simpl_ActionClass. inversion H. destruct H0. rewrite H4 in H3.
        simpl in H3. contradiction.
        assert (count - f <= x < count). lia. clear H2.
        specialize H with (Corrupted_T f x H3). simpl_ActionClass. rewrite <-Hbyzentine in H.
        simpl_ActionClass. inversion H. destruct H0. rewrite H4 in H2. contradiction.
  Qed.

  Definition BrachaRB
    (f : nat)
    (byzentine : Process -> IOADef BrachaRBAction)
    (Hbyzentine :
      forall p : Process,
        is_byzentine (BrachaRBProcess f p) (byzentine p)
    )
    : IOADef BrachaRBAction :=
    CompositionExtended
      (Network_T f)
      (composition_extended_hyp f byzentine Hbyzentine)
      (exists_output_spec f byzentine Hbyzentine)
      (exists_input_spec f byzentine Hbyzentine)
      (forall_unused_spec f byzentine Hbyzentine)
  .

  Fixpoint action_modulo_process_equality_dec
    (f : nat)
    (byzentine : Process -> IOADef BrachaRBAction)
    (Hbyzentine : (forall p : Process, is_byzentine (BrachaRBProcess f p) (byzentine p)))
    (m : InternMessage)
    (s : ExecSection BrachaRBAction (BrachaRB f byzentine Hbyzentine))
    (k : nat) : {exists n, n < k /\ opt_act BrachaRBAction (BrachaRB f byzentine Hbyzentine) s =
                            Some (BrachaRBP2PSend (label n) (label n) m)}+
      {forall n, n < k -> opt_act BrachaRBAction (BrachaRB f byzentine Hbyzentine) s <>
                              Some (BrachaRBP2PSend (label n) (label n) m)}.
    induction k.
    right. intros. lia.
    destruct BrachaRBOptionAction_dec with
      (opt_act BrachaRBAction (BrachaRB f byzentine Hbyzentine) s)
      (Some (BrachaRBP2PSend (label k) (label k) m)).
    left. exists k. split. lia. auto.
    destruct IHk. left. destruct e. exists x. split. lia. apply H.
    right. intros.
    case_eq (n1 =? k) ; intro ; simpl_arith_bool.
    subst k. auto.
    apply n0. lia.
  Qed.

  Lemma send_ready_then_condition_satisfied :
    forall f : nat,
    forall byzentine : Process -> IOADef BrachaRBAction,
    forall Hbyzentine : (forall p : Process, is_byzentine (BrachaRBProcess f p) (byzentine p)),
      forall e : ExecFragmentType (A := BrachaRB f byzentine Hbyzentine),
      Exec e ->
      forall i : nat, forall m : Message, forall n : nat,
        forall H : n < count - f,
        BrachaRBSendBuffer
                (st BrachaRBAction (BrachaRB f byzentine Hbyzentine) (e i) (Correct_T f n H))
                ((label n), Ready m) = true ->
              let st := st BrachaRBAction (BrachaRB f byzentine Hbyzentine) (e i) (Correct_T f n H) in
              BrachaRBStep st >= 3 /\ (
                                      BrachaRBRecvBufferSize st (Echo m) >= 2*f+1 \/
                                        BrachaRBRecvBufferSize st (Ready m) >= f+1
                                    ).
  Proof.
    intros.
    eapply project_execution_exist_with_exec in H.
    Unshelve. 2: apply (Correct_T f n H0).
    decompose [ex and or] H. clear H.
    specialize H4 with i. decompose [and] H4. clear H4.
    fold st in H1.
    unfold BrachaRB in st. fold st in H. rewrite H in *.
    clear H st. eapply send_ready_then_condition_satisfied ; auto.
    apply H1.
  Qed.

  Open Scope ltl_scope.

  Lemma extend_buffer_size_is_size
    (f : nat)
    (byzentine : Process -> IOADef BrachaRBAction)
    (Hbyzentine : (forall p : Process, is_byzentine (BrachaRBProcess f p) (byzentine p)))
    : forall proc : nat, forall Hineq : proc < count - f, forall m : InternMessage,
    forall e : ExecFragmentType (A := BrachaRB f byzentine Hbyzentine),
    Exec e ->
    e $ 0 |= G (N (fun s => let (st, act, st', _) := s in
        buffer_size
          Process_dec
          (fun p => BrachaRBRecvBuffer (st (Correct_T f proc Hineq)) (p, m))
          (BrachaRBRecvBufferSize (st (Correct_T f proc Hineq)) m))).
  Proof.
    intros.
    eapply project_execution_exist_with_exec in H.
    Unshelve. 2: apply (Correct_T f proc Hineq).
    decompose [ex and or] H. clear H.
    eapply recv_buffer_size_is_size_of_recv_buffer in H1.
    hnf in H1.
    intros i Hi. specialize H2 with i. specialize H1 with i. decompose [and] H2. clear H2.
    apply H1 in Hi. hnf in Hi |- *.
    destruct (e i). destruct (x i). simpl in *. subst. apply Hi.
  Qed.

  Axiom buffer_size_is_less_than_count :
    forall i, forall b : buffer Process, buffer_size Process_dec b i -> i <= count.

  Lemma buffer_has_size :
    forall b, exists i, buffer_size Process_dec b i.
  Proof.
    induction b.


  Theorem two_buffer_of_size_big_then_intersect_no_cond :
    forall f : nat,
    3*f = count ->
  forall i i' : nat, forall buff buff' : Process -> bool,
    buffer_size Process_dec buff i -> buffer_size Process_dec buff' i' ->
    2*f+1 <= i < count -> 2*f+1 <= i' < count ->
    exists q : nat, buff (label q) = true /\ buff' (label q) = true.
  Proof.
    intros.

    eapply intersection_of_big_sets_is_non_empty.







  Definition union
    (buff buff' : Process -> bool) : Process -> bool :=
    fun p => buff p || buff' p.

  Definition buff_add
    (buff : Process -> bool)
    (p : Process) : Process -> bool :=
    fun p' => if Process_dec p p' then true else buff p'.

  Definition buff_sub
    (buff : Process -> bool)
    (p : Process) : Process


  Inductive buffer_size_bis
    (buff : Process -> bool)
    (size : nat) : Prop :=
    | buff_empty : size = 0 -> (forall proc : Process, buff proc = false) -> buffer_size_bis buff size
    | exist_packet : size > 0 -> (exists proc : Process, buff proc = true /\ buffer_size (BrachaRBBuffer_sub buff proc) (size - 1)) ->
                   buffer_size buff size
.

  
  Lemma truc :
    forall c,
       (*forall f : nat,
         (count - c - 1) / 2 < 2*f+1 /\ 3*f+1 <= count - c - 1 ->*)
         forall (i i' cup : nat) (buff buff' : Packet -> bool) (m m' : InternMessage),
           (forall j : nat, count - c - 1 + 1 <= j < count ->
                     buff ((label j), m) = false /\ buff' ((label j), m') = false) ->
           buffer_size buff m i ->
           buffer_size buff' m' i' ->
           (count - c - 1) < i + i' ->
           0 < i -> 0 < i' ->
           exists q : nat, buff (label q, m) = true /\ buff' (label q, m') = true.

  Fixpoint lookup_same_element
    (buff buff' : Packet -> bool)
    (m m' : InternMessage)
    (i : nat) :=
    match i with
      | 0 =>
          if (buff (label i, m)) && (buff' (label i, m')) then
            buff
          else
            BrachaRBBuffer_sub buff (label i) m
      | S n =>
          if (buff (label i, m)) && (buff' (label i, m')) then
            buff
          else
            lookup_same_element
              (BrachaRBBuffer_sub buff (label i) m)
              (BrachaRBBuffer_sub buff' (label i) m')
              m m' n
    end.

  Lemma sub_reduce_size :
    forall i : nat, forall buff : Packet -> bool, forall m : InternMessage, forall p : Process,
      buffer_size buff m i -> buff (p, m) = true ->
        buffer_size (BrachaRBBuffer_sub buff p m) m (i-1).
  Proof.
    induction i.
    - intros.
      destruct H. specialize H1 with p. rewrite H1 in H0. inversion H0.
      lia.
    - intros.
      destruct H. lia. destruct H1.
      case_eq (proj1_sig p =? proj1_sig x) ; intro ; simpl_arith_bool.
      apply process_proof_irrelevence in H2. subst x. apply H1.
      assert (tmp : S i - 1 = i) by lia. rewrite tmp in *. clear tmp.
      apply exist_packet. induction i.
      destruct H1. destruct H3. specialize H4 with p. assert (p <> x). intro. subst. contradiction.
      assert (buff (p, m) = false). buffer_solver.
      rewrite H0 in H6. inversion H6.
      lia.
      lia.
      destruct H1. eapply IHi in H3.
      exists x. split. assert (p <> x). intro. subst. contradiction. buffer_solver.
      assert (BrachaRBBuffer_sub (BrachaRBBuffer_sub buff x m) p m = BrachaRBBuffer_sub (BrachaRBBuffer_sub buff p m) x m).
      apply functional_extensionality_dep. intro. unfold BrachaRBBuffer_sub. repeat simpl_match ; auto.
      rewrite <-H4. apply H3. assert (p <> x). intro. subst. contradiction. buffer_solver.
  Qed.

  Lemma truc :
    forall i : nat, forall buff : Packet -> bool, forall m : InternMessage,
      (forall j : nat, i <= j < count -> buff (label j, m) = false) ->
      buffer_size buff m i ->
      forall j : nat, j < i -> buff (label j, m) = true.
  Proof.
    intros i buff m Hsup Hsize.
    apply size_of_buffer_then_exists_set_of_proc in Hsize.
    destruct Hsize as [x Hsize].
    intros.
    assert (forall i : nat, forall p, exists j, j < i /\ x j = p)




    assert (exists n, lookup_label_value x (label j) (i-1) = Some n).



    assert (exists n, x n = label j).
    revert Hsize. revert x.
    generalize dependent j. generalize dependent i. induction i.
    intros. lia.
    intros.



    assert (exists sset : nat -> nat,
               (forall n : nat, n < i ->
                           label n = x (sset n) /\ sset n < count) /\
                 (forall n m : nat, n < m < i -> sset n <> sset m)
           ).
    revert Hsize. revert x.
    generalize i. induction i0 ; intros.
    exists (fun n => 0). split ; lia.
    edestruct IHi0. destruct Hsize. split. intros. apply e. lia. intros. apply n. lia.
    destruct Hsize. specialize H0 with i0. assert (buff (x i0, m) = true). auto.
    destruct label_is_bij with (label n). destruct H3.
    exists (fun n => if n =? i0 then x1 else (x0 n)). split. intros.
    simpl_match ; simpl_arith_bool. subst. split. destruct H3. rewrite H6. auto. split ; apply H3.
    apply H. lia.
    intros. simpl_match ; simpl_arith_bool ; subst ;
    simpl_match ; simpl_arith_bool. lia. lia. subst.
    destruct H. specialize H with n.
    assert (label (x0 n) <> x i0). destruct H. lia.
    destruct H8. rewrite H8. apply H1. auto.
    destruct H3. rewrite <-H9 in H8. intro. apply H8. subst. auto.
    apply H. lia.
    destruct H. intros.
    destruct H.

    specialize H0 with i0.



    intros. assert (exists n, x n = label j).



    assert (exists sset : nat -> nat, (forall n : nat, n < i -> buff (label (sset n), m) = true /\ label (sset n) = x n /\ sset n < count) /\ (forall n m : nat, n < m < i -> sset n <> sset m)).
    revert Hsize. revert x.
    (*generalize dependent i.*) generalize i.
    induction i0 ; intros.
    exists (fun n => 0). split ; lia.
    edestruct IHi0. destruct Hsize. split. intros. apply e. lia. intros. apply n. lia.
    destruct Hsize. specialize H0 with i0. assert (buff (x i0, m) = true). auto.
    destruct label_is_bij with (x i0). destruct H3.
    exists (fun n => if n =? i0 then x1 else (x0 n)). split. intros.
    simpl_match ; simpl_arith_bool. subst. split. destruct H3. rewrite H6. auto. split ; apply H3.
    apply H. lia.
    intros. simpl_match ; simpl_arith_bool ; subst ;
    simpl_match ; simpl_arith_bool. lia. lia. subst.
    destruct H. specialize H with n.
    assert (label (x0 n) <> x i0). destruct H. lia.
    destruct H8. rewrite H8. apply H1. auto.
    destruct H3. rewrite <-H9 in H8. intro. apply H8. subst. auto.
    apply H. lia.
    destruct H. intros.
    destruct H.
    assert (exists n, j = x0 n).
    revert H. revert x0. revert H0. revert j. generalize i. induction i0.
    intros. lia.
    intros.



    intros.
    destruct H. destruct H.





    intros. apply Hsup. lia.
    intros.
    revert H. revert H0. revert j. generalize i.
    induction i0.
    - intros. lia.
    - intros.
      destruct H.


    destruct H
    assert (exists n, x n = (label j, m)).
    generalize dependent i.
    (*intro i. revert j. revert i.*)
    induction i ; intros. lia.
    case_eq (j =? i) ; intro ; simpl_arith_bool.
    subst.






    assert (forall i0, forall buff', buffer_size buff' m i0 -> (forall p, (negb (buff' p)) || (buff p) = true) -> forall j : nat, j < i -> buff' (label j, m) = true).
    induction i0.
    - intros.
      destruct Hsize. lia.
      destruct H3. specialize H0 with (x, m).


    destruct H. specialize H0 with (label j, m). simpl_arith_bool. apply negb_true_iff in H0. lia.
    intros. destruct H. lia.
    destruct H2. destruct Process_dec with x (label j). subst. apply H2.
    destruct H2.
    assert (BrachaRBBuffer_sub buff' x m (label j, m) = true).
    assert (tmp : S i0 - 1 = i0) by lia. rewrite tmp in H3. clear tmp.
    apply IHi0 ; auto.
    intro.
    specialize H0 with p. repeat simpl_arith_bool.
    apply negb_true_iff in H0.
    left. apply negb_true_iff. buffer_solver.
    auto.


    case_eq ()

    revert Hsize. generalize buff.
    induction Hsize. lia.
    intros. destruct H0.



    induction i.
    - intros. lia.
    - intros.
      destruct H0. lia. destruct H2 as [p Hp].
      destruct Hp as [Hpbuff Hpsize].
      clear H0.
      assert (S i - 1 = i) by lia. rewrite H0 in *. clear H0.
      destruct Process_dec with p (label j). subst. auto.
      assert (BrachaRBBuffer_sub buff p m (label j, m) = true).
      apply IHi.
      intros. specialize H with j0. apply H in H0.
      buffer_solver.
      auto; lia.

      eapply IHi.
      auto.*)


  Theorem two_buffer_of_size_big_then_intersect_no_cond :
    forall f : nat,
    3*f = count ->
  forall i i' : nat, forall buff buff' : Packet -> bool, forall m m' : InternMessage,
    buffer_size buff m i -> buffer_size buff' m' i' ->
    2*f+1 <= i < count -> 2*f+1 <= i' < count ->
    exists q : nat, buff (label q, m) = true /\ buff' (label q, m') = true.
  Proof.
    assert (
      forall c,
       (*forall f : nat,
         (count - c - 1) / 2 < 2*f+1 /\ 3*f+1 <= count - c - 1 ->*)
         forall (i i' : nat) (buff buff' : Packet -> bool) (m m' : InternMessage),
           (forall j : nat, count - c - 1 + 1 <= j < count ->
                     buff ((label j), m) = false /\ buff' ((label j), m') = false) ->
           buffer_size buff m i ->
           buffer_size buff' m' i' ->
           (count - c - 1) < i + i' ->
           0 < i -> 0 < i' ->
           exists q : nat, lookup_same_element buff buff' m m' (count - c - 1) (label q, m) = true).
    intros c.
    induction (count - c - 1).
    intros.
    - exists 0. (*assert (f = 0) by lia. subst f.*)
      simpl.
      destruct H0. lia. destruct H5.
      destruct H1. lia. destruct H6.
      destruct label_is_surj with x as [p Hp].
      induction p ; destruct Hp as [Hp tmp] ; subst x.
      destruct label_is_surj with x0 as [q Hq].
      induction q ; destruct Hq as [Hq tmp] ; subst x0.
      destruct H5, H6. rewrite H5, H6.
      simpl. auto.
      assert (1 <= S q < count) by lia. apply H in H7.
      destruct H7. destruct H6. rewrite H6 in H8. inversion H8.
      assert (1 <= S p < count) by lia. apply H in H7.
      destruct H7. destruct H5. rewrite H5 in H7. inversion H7.
    - intros. simpl. simpl_match ; simpl_arith_bool.
      exists (S n). auto.
      case_eq (buff' (label (S n), m')) ; intro.
      eapply IHn.
      intros. split.
      case_eq (j =? S n) ; intro ; simpl_arith_bool.
      buffer_solver.
      assert (S n + 1 <= j < count) by lia. apply H in H9. destruct H9.
      buffer_solver.
      case_eq (j =? S n) ; intro ; simpl_arith_bool.
      buffer_solver.
      assert (S n + 1 <= j < count) by lia. apply H in H9. destruct H9.
      buffer_solver.
      assert (BrachaRBBuffer_sub buff (label (S n)) m = buff). buffer_solver. rewrite H7. apply H0.
      apply sub_reduce_size. apply H1. apply H6. lia. auto.
      case_eq (i' =? 1) ; intro ; simpl_arith_bool.
      subst. assert (n < i). lia.







      assert (forall n : nat, forall i : nat, forall buff : Packet -> bool, (forall j : nat, n + 1 <= j < count -> buff (label j, m) = false) ->
                                                     forall m : InternMessage, forall j : nat, j <= n -> buff (label j, m) = true).
      intros. revert dependent buff. generalize i. induction i0. intros. lia.
      generalize dependent i. induction i. intros. lia.
      intros. induction i.
      assert (j <= 1). lia.
      (*induction j.*)
      destruct H0. lia. destruct H10. destruct H10. simpl in H11. destruct H11.
      destruct label_is_bij with x. destruct H13. destruct H13. subst x.
      case_eq (x0 =? j) ; intro ; simpl_arith_bool.
      subst. auto.
      assert (n = 0). lia. subst n. simpl in *.
      case_eq (x0 =? 1) ; intro ; simpl_arith_bool.
      subst. rewrite H5 in H10. inversion H10.
      case_eq (j =? 1) ; intro ; simpl_arith_bool.
      subst.
      assert (buff (label (S x0), m) = false). apply H. lia.


      induction x0. auto. assert (n = 0). lia. subst n. simpl in *.
      case_eq (S x0 =? 1) ; intro ; simpl_arith_bool.
      rewrite H15 in H10. rewrite H5 in H10. inversion H10.
      assert (buff (label (S x0), m) = false). apply H. lia.
      rewrite H10 in H16. inversion H16. lia.
      assert (S j = 1). lia. rewrite H10.



      destruct Process_dec with (label 0) x. subst. auto.
      specialize H12 with (label 0).
      destruct label_is_surj with x. destruct H13. subst x.
      destruct H0. lia. destruct H9.



      Lemma sub_reduce_size :
        forall i : nat, forall buff : Packet -> bool, forall m : Message, forall p : Process,
          buffer_size buff m i -> buff (p, m) = true ->
            buffer_size (BrachaRBBuffer_sub buff p m) m (i-1).



    lia.
    intros. simpl. assert (tmp : n - 0 = n) by lia. rewrite tmp. clear tmp.




    assert (exists q : nat, lookup_same_element buff buff' m m' (count - 1) (label q, m) = true).





    intros f Hf.
    assert (
        forall (i i' : nat) (buff buff' : Packet -> bool) (m m' : InternMessage),
  buffer_size buff m i ->
  buffer_size buff' m' i' ->
  2 * f + 1 <= i <= count-1 ->
  2 * f + 1 <= i' <= count-1 ->
        exists q : nat, lookup_same_element buff buff' m m' (count - 1) (label q, m) = true).
    generalize (count-1).
    induction n.
    intros.
    lia.
    intros.
    simpl. simpl_match.
    exists (S n). simpl_arith_bool. auto.
    simpl_arith_bool.
    eapply IHn.
    assert (BrachaRBBuffer_sub buff (label (S n)) m = buff). buffer_solver.
    rewrite H4. apply H.
    apply H0.


    simpl. assert (tmp : n-0 = n) by lia. rewrite tmp. clear tmp.


    induction n. simpl.





    assert (exists q : nat, lookup_same_element buff buff' m m' (count-1) = Some q).
    generalize count.
    induction n.
    simpl.

    generalize count.
    induction n.
    intros. lia.
    intros.
    case_eq (i =? n) ; intro ; simpl_arith_bool.
    case_eq (i' =? n) ; intro ; simpl_arith_bool.
    subst i. subst i'. clear H2.
    destruct H, H0 ; try lia.
    destruct H2, H3.
    assert (exists q : nat, (BrachaRBBuffer_sub buff x m) (label q, m) = true /\
                       (BrachaRBBuffer_sub buff' x0 m') (label q, m') = true).
    eapply IHn.
    apply H2. apply H3.




  Theorem two_buffer_of_size_big_then_intersect_cond :
  forall f : nat,
    3*f+1 = count ->
  forall i i' : nat, forall buff buff' : Packet -> bool, forall m m' : InternMessage,
    buffer_size buff m i -> buffer_size buff' m' i' ->
    2*f+1 <= i < count -> 2*f+1 <= i' < count ->
    exists q : nat, q < count - f /\ buff (label q, m) = true /\ buff' (label q, m') = true.
  Proof.
    induction count.
    intros. lia.
    intros.
    case_eq (i =? n) ; intro ; simpl_arith_bool.
    case_eq (i' =? n) ; intro ; simpl_arith_bool.
    subst i. subst i'. clear H3.


    induction f.
    intros. lia.




    intros f Heq.
    induction i ; induction i' ; intros ; try lia.
    destruct H. lia.
    destruct H0. lia.
    destruct H3, H4.
    case_eq (buff (x, m)) ; intro.
    case_eq (buff' (x0, m')) ; intro.
    assert (exists q : nat, q < count - f /\ BrachaRBBuffer_sub buff x m (label q, m) = true /\
                       BrachaRBBuffer_sub buff' x0 m' (label q, m') = true).
    eapply IHi.
    assert (tmp : S i - 1 = i) by lia. rewrite tmp in H3. clear tmp.
    apply H3.
    apply H4.

    exists 0. split. lia. auto.
    assert (exists q : nat, q < count - f /\
                       BrachaRBBuffer_sub buff (label 0) m (label q, m) = true /\
                       buff' (label q, m') = true).
    eapply IHi.

    apply H


  Lemma two_ready_are_equals :
    forall f : nat,
    forall Hf : 3*f + 1 = count,
    forall byzentine : Process -> IOADef BrachaRBAction,
    forall Hbyzentine : (forall p : Process, is_byzentine (BrachaRBProcess f p) (byzentine p)),
      forall e : ExecFragmentType (A := BrachaRB f byzentine Hbyzentine),
      Exec e ->
      forall i j : nat, forall m m' : Message, forall p q : nat,
        p < count - f -> q < count - f ->
        opt_act BrachaRBAction (BrachaRB f byzentine Hbyzentine) (e i) =
          Some (BrachaRBP2PSend (label p) (label p) (Ready m)) ->
        opt_act BrachaRBAction (BrachaRB f byzentine Hbyzentine) (e j) =
          Some (BrachaRBP2PSend (label q) (label q) (Ready m')) ->
        m = m'.
  Proof.
    intros.
    case_eq (Message_dec m m') ; intros ; auto.
    assert ((fun s => if action_modulo_process_equality_dec
                        f
                        byzentine
                        Hbyzentine
                        (Ready m)
                        s
                        (count - f)
                  then true else false
           ) (e i) = true).
    simpl_match. auto. clear H5. specialize n1 with p. apply n1 in H0. contradiction.
    apply existence_of_first_state_for_property in H5.
    assert ((fun s => if action_modulo_process_equality_dec
                        f
                        byzentine
                        Hbyzentine
                        (Ready m')
                        s
                        (count - f)
                  then true else false
           ) (e j)= true).
    simpl_match. auto. clear H6. specialize n1 with q. apply n1 in H1. contradiction.
    apply existence_of_first_state_for_property in H6.
    clear H0 H1 H2 H3 i j.
    decompose [ex and or] H5. decompose [ex and or] H6. clear H5 H6.
    move H1 at bottom.
    simpl_match ; cycle 1. inversion H1. clear H0 H1.
    simpl_match ; cycle 1. inversion H3. clear H0 H3.
    clear p q.
    destruct n1 as [p Heq_p].
    destruct n2 as [q Heq_q].
    destruct Heq_p as [Hineq_p Hopt_act_eq_p].
    destruct Heq_q as [Hineq_q Hopt_act_eq_q].

    assert (
        p_send_buffer_hyp :
        BrachaRBSendBuffer
          (st
             BrachaRBAction
             (BrachaRB f byzentine Hbyzentine)
             (e x)
             (Correct_T f p Hineq_p)
          )
          (label p, Ready m) = true
    ).
    destruct (e x). simpl in *.
    eapply transition_send_only_if_in_send_buffer.
    subst opt_act. specialize is_well_formed with (Correct_T f p Hineq_p).
    destruct is_well_formed. destruct H1. unfold Transition, Ref in H1. simpl in H1. apply H1.
    simpl_match. discriminate. simpl_arith_bool. contradiction.

    assert (
        q_send_buffer_hyp :
        BrachaRBSendBuffer
          (st
             BrachaRBAction
             (BrachaRB f byzentine Hbyzentine)
             (e x0)
             (Correct_T f q Hineq_q)
          )
          (label q, Ready m') = true
    ).
    destruct (e x0). simpl in *.
    eapply transition_send_only_if_in_send_buffer.
    subst opt_act. specialize is_well_formed with (Correct_T f q Hineq_q).
    destruct is_well_formed. destruct H1. unfold Transition, Ref in H1. simpl in H1. apply H1.
    simpl_match. discriminate. simpl_arith_bool. contradiction.
    apply send_ready_then_condition_satisfied in p_send_buffer_hyp. 2: apply H.
    apply send_ready_then_condition_satisfied in q_send_buffer_hyp. 2: apply H.
    destruct p_send_buffer_hyp as [_ p_recv_hyp].
    destruct q_send_buffer_hyp as [_ q_recv_hyp].
    destruct p_recv_hyp as [p_recv_hyp | p_recv_hyp_imp].
    destruct q_recv_hyp as [q_recv_hyp | q_recv_hyp_imp].
    induction f.
    {
      (* f = 0 *)
      simpl in *.
      pose proof H as Hp.
      eapply extend_buffer_size_is_size in Hp.
      hnf in Hp. specialize Hp with x.
      assert (x >= 0) by lia. apply Hp in H0. clear Hp.
      pose proof H0 as Hp. clear H0.
      hnf in Hp. destruct (e x). simpl in *. subst.
      apply size_of_buffer_then_exists_set_of_proc in Hp.
      destruct Hp as [ssetp [Hptrue Hpdiff]].
      induction (BrachaRBRecvBufferSize (st (Correct_T 0 p Hineq_p)) (Echo m)) eqn : Hp_ind.
      lia.
      rewrite Hp_ind in Hptrue.


      size_of_buffer_then_exists_set_of_proc
    }
    intros.

    generalize dependent f.
    induction f.
    generalize dependent count.

















  Definition Other_type :=
    { n : nat | 0 < n < count - f }.

  Axiom other_type_proof_irrelevence :
    forall p q : Other_type, proj1_sig p = proj1_sig q -> p = q.

  Definition Byzentine_type :=
    { n : nat | count-f <= n < count }.

  Axiom byzentine_type_proof_irrelevence :
    forall p q : Byzentine_type, proj1_sig p = proj1_sig q -> p = q.

  Inductive Composition_type :=
    | Leader_T : Composition_type
    | Other_T : Other_type -> Composition_type
    | Network_T : Composition_type
    | Byzentine_T : Byzentine_type -> Composition_type.

  Definition Composition_type_eq
    (i j : Composition_type) : Prop :=
    i = j.

  Definition process_from_other_type (p : Other_type) : Process.
    create_sig Process (proj1_sig p) out.
    destruct p. simpl in *. lia.
    apply out.
  Defined.

  Definition process_from_byzentine_type (p : Byzentine_type) : Process.
    create_sig Process (proj1_sig p) out.
    destruct p. simpl in *. lia.
    apply out.
  Defined.

  Ltac create_sig2 typ a out :=
    let typ' := eval unfold typ in typ in
    match typ' with
      | sig ?P =>
          let H := fresh "H" in
          assert (H : P a) ; [
              auto |
              pose (exist P a H) as out
            ]
    end.

  Definition composition_type_from_process_aux (p : Process) :
    {q : Composition_type |
      match proj1_sig p with
        | 0 => q = Leader_T
        | _ => match q with
                | Other_T q' | Byzentine_T q' => proj1_sig q' = proj1_sig p
                | _ => False
              end
        end
    }.
    case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool.
    apply exist with Leader_T.
    rewrite H. auto.
    case_eq (proj1_sig p <? count - f) ; intro ; simpl_arith_bool.
    create_sig2 Other_type (proj1_sig p) out. lia.
    apply exist with (Other_T out).
    simpl_match ; try simpl_arith_bool ; auto.
    contradiction.
    create_sig2 Byzentine_type (proj1_sig p) out. destruct p. simpl in *. lia.
    apply exist with (Byzentine_T out).
    simpl_match ; try simpl_arith_bool ; auto.
    contradiction.
  Defined.

  Definition composition_type_from_process (p : Process) :=
    proj1_sig (composition_type_from_process_aux p).

  Lemma if_process_zero_then_leader :
    forall p : Process,
      proj1_sig p = 0 ->
      composition_type_from_process p = Leader_T.
  Proof.
    intros.
    destruct p. simpl in *. subst x.
    unfold composition_type_from_process.
    simpl. auto.
  Qed.

  Lemma if_process_non_zero_and_not_byzentine_then_other :
    forall p : Process,
      proj1_sig p <> 0 ->
      proj1_sig p < count - f ->
      exists p', composition_type_from_process p = Other_T p'.
  Proof.
    intros.
    destruct p. simpl in *.
    unfold composition_type_from_process.
    destruct (composition_type_from_process_aux (exist (fun n : nat => n < count) x l)).
    simpl in *.
    destruct x. contradiction.
    case_eq x0 ; intros ; subst x0.
    contradiction.
    exists o. auto.
    contradiction.
    destruct b. simpl in *. lia.
  Qed.

  Lemma if_process_byzentine_then_byzentine :
    forall p : Process,
      proj1_sig p < count ->
      proj1_sig p >= count - f ->
      exists p', composition_type_from_process p = Byzentine_T p'.
  Proof.
    intros.
    destruct p. simpl in *.
    unfold composition_type_from_process.
    destruct (composition_type_from_process_aux (exist (fun n : nat => n < count) x l)).
    simpl in *.
    destruct x. lia.
    case_eq x0 ; intros ; subst x0.
    contradiction.
    destruct o. simpl in *. lia.
    contradiction.
    exists b. auto.
  Qed.

  Lemma conversion_never_network :
    forall p : Process,
      composition_type_from_process p <> Network_T.
  Proof.
    intros.
    unfold composition_type_from_process.
    destruct (composition_type_from_process_aux p).
    simpl in *.
    repeat simpl_match ; subst ; try discriminate ; contradiction.
  Qed.

  Definition Ref
    (byzentine : Byzentine_type -> IOADef BrachaRBAction)
    (n : Composition_type) :
    IOADef BrachaRBAction :=
    match n with
    | Leader_T => BrachaRBProcess f process_zero
    | Other_T p => BrachaRBProcess f (process_from_other_type p)
    | Network_T => P2PNetwork
    | Byzentine_T p => byzentine p
    end.

  Ltac guess_IOA_from_action act interface out :=
      let other := fresh "other" in
      match act with
        | BrachaRBBroadcast _ =>
            match interface with
              | Input => pose Leader_T as out
              | Unused => pose Network_T as out
              | _ => idtac
            end
        | BrachaRBDeliver ?p _ =>
            match interface with
              | Output =>
                  case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
                  [
                    pose Leader_T as out |
                    case_eq (proj1_sig p <? count - f) ; intro ; simpl_arith_bool ;
                    [
                      create_sig Other_type (proj1_sig p) other ;
                      [
                        idtac |
                        pose (Other_T other) as out
                      ] |
                      create_sig Byzentine_type (proj1_sig p) other ;
                      [
                        idtac |
                        pose (Byzentine_T other) as out
                      ]
                    ]
                  ]
              | Unused => pose Network_T as out
              | Input => idtac
            end
        | BrachaRBP2PRecv ?p ?q _ =>
            match interface with
              | Output => pose Network_T as out
              | Input =>
                   case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
                  [
                    pose Leader_T as out |
                    case_eq (proj1_sig p <? count - f) ; intro ; simpl_arith_bool ;
                    [
                      create_sig Other_type (proj1_sig p) other ;
                      [
                        idtac |
                        pose (Other_T other) as out
                      ] |
                      create_sig Byzentine_type (proj1_sig p) other ;
                      [
                        idtac |
                        pose (Byzentine_T other) as out
                      ]
                    ]
                  ]
               | Unused =>
                   case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
                   [
                     create_sig Other_type 1 other ;
                     [
                       idtac |
                       pose (Other_T other) as out
                     ] |
                     pose Leader_T as out
                   ]
              end
        | BrachaRBP2PSend ?p ?q _ =>
            match interface with
              | Input => pose Network_T as out
              | Output =>
                   case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
                  [
                    pose Leader_T as out |
                    case_eq (proj1_sig p <? count - f) ; intro ; simpl_arith_bool ;
                    [
                      create_sig Other_type (proj1_sig p) other ;
                      [
                        idtac |
                        pose (Other_T other) as out
                      ] |
                      create_sig Byzentine_type (proj1_sig p) other ;
                      [
                        idtac |
                        pose (Byzentine_T other) as out
                      ]
                    ]
                  ]
               | Unused =>
                   case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool ;
                   [
                     create_sig Other_type 1 other ;
                     [
                       idtac |
                       pose (Other_T other) as out
                     ] |
                     pose Leader_T as out
                   ]
              end
      end.

  Ltac guess_compose_type_from_action_class :=
      let out := fresh "out" in
      match goal with
        | [|- context [ActionClass _ ?act = ?interface]] =>
            guess_IOA_from_action act interface out ;
            (exists out ; simpl_ActionClass) || idtac
        | [H : context [ActionClass _ ?act = ?interface] |- _] =>
            match interface with
              | Input =>
                  guess_IOA_from_action act Unused out ;
                  (specialize H with out ; simpl_ActionClass) || idtac
              | Output =>
                  guess_IOA_from_action act Unused out ;
                  (specialize H with out ; simpl_ActionClass) || idtac
              | Unused =>
                  (guess_IOA_from_action act Output out ;
                  (specialize H with out ; simpl_ActionClass) || idtac) ||
                  (guess_IOA_from_action act Input out ;
                  (specialize H with out ; simpl_ActionClass) || idtac)
            end
      end.

  Lemma composition_extended_hyp
    (byzentine : Byzentine_type -> IOADef BrachaRBAction)
    (Hbyzentine :
      forall p : Byzentine_type,
        is_byzentine (BrachaRBProcess f (process_from_byzentine_type p)) (byzentine p)
    ) :
    CompositionExtendedHyp
      eq
      (Ref byzentine).
  Proof.
    unfold is_byzentine in Hbyzentine. intros. split ; intros.
    + contradict H1. induction act ;
        simpl_ActionClass ; try (rewrite <-Hbyzentine ; simpl_ActionClass) ; discriminate.
    + induction act ; simpl_ActionClass ; try discriminate ;
      simpl_ActionClass ; try discriminate ; try rewrite <-Hbyzentine in * ; try simpl_ActionClass ; try (contradiction || discriminate) ;
        destruct p, n0 ; simpl in * ; lia || (destruct n1 ; simpl in *; lia || auto) ; try (simpl_match ; simpl_arith_bool ; lia || inversion H0).
      subst x x0. assert (exist (fun n : nat => 0 < n < count - f) x1 a0 = exist (fun n : nat => 0 < n < count - f) x1 a).
      apply other_type_proof_irrelevence. simpl. auto. rewrite H2 in H. contradiction.
      subst x x0. assert (exist (fun n : nat => count - f <= n < count) x1 a0 = exist (fun n : nat => count - f <= n < count) x1 a).
      apply byzentine_type_proof_irrelevence. simpl. auto. rewrite H3 in H. contradiction.
      subst x x0. assert (exist (fun n : nat => 0 < n < count - f) x1 a0 = exist (fun n : nat => 0 < n < count - f) x1 a).
      apply other_type_proof_irrelevence. simpl. auto. rewrite H2 in H. contradiction.
      subst x x0. assert (exist (fun n : nat => count - f <= n < count) x1 a0 = exist (fun n : nat => count - f <= n < count) x1 a).
      apply byzentine_type_proof_irrelevence. simpl. auto. rewrite H3 in H. contradiction.
  Qed.

  Definition exists_output (act : BrachaRBAction) : bool :=
    match act with
      | BrachaRBBroadcast _ => false
      | BrachaRBDeliver _ _ | BrachaRBP2PSend _ _ _  | BrachaRBP2PRecv _ _ _ => true
    end.

  Lemma exists_output_spec
    (byzentine : Byzentine_type -> IOADef BrachaRBAction)
    (Hbyzentine :
      forall p : Byzentine_type,
        is_byzentine (BrachaRBProcess f (process_from_byzentine_type p)) (byzentine p)
    ) :
    OutputSpec (Ref byzentine) exists_output.
  Proof.
    hnf. intro. split ; intro.
    + case_eq act ; intros ; rewrite H0 in H ; simpl in H ; clear H0 ; inversion H ;
      guess_compose_type_from_action_class ; fold Nat.sub in * ; try rewrite <-Hbyzentine ; lia || (split ; apply proj2_sig || lia) || (simpl_ActionClass ; lia).
    + case_eq act ; intros ; rewrite H0 in * ; simpl ; destruct H ;
        simpl_ActionClass ; try rewrite <-Hbyzentine in * ; inversion H ; destruct n0 ; simpl in *.
        repeat simpl_match ; inversion H1 ; inversion H.
  Qed.

  Definition exists_input (act : BrachaRBAction) : bool :=
    match act with
      | BrachaRBBroadcast _ | BrachaRBP2PSend _ _ _ | BrachaRBP2PRecv _ _ _ => true
      | BrachaRBDeliver _ _ => false
    end.

  Lemma exists_input_spec
    (byzentine : Byzentine_type -> IOADef BrachaRBAction)
    (Hbyzentine :
      forall p : Byzentine_type,
        is_byzentine (BrachaRBProcess f (process_from_byzentine_type p)) (byzentine p)
    ) :
    InputSpec (Ref byzentine) exists_input.
  Proof.
    hnf. intro. split ; intro.
    + case_eq act ; intros ; rewrite H0 in H ; simpl in H ; clear H0 ; inversion H ;
      guess_compose_type_from_action_class ; fold Nat.sub in * ; try rewrite <-Hbyzentine ; lia || (split ; apply proj2_sig || lia) || (simpl_ActionClass ; lia).
    + case_eq act ; intros ; rewrite H0 in * ; simpl ; destruct H ;
        simpl_ActionClass ; try rewrite <-Hbyzentine in * ; inversion H ; destruct p, n0 ; simpl_ActionClass ; simpl in * ; lia || inversion H3.
  Qed.

  Definition forall_unused (act : BrachaRBAction) : bool :=
    false.

  Lemma forall_unused_spec
    (byzentine : Byzentine_type -> IOADef BrachaRBAction)
    (Hbyzentine :
      forall p : Byzentine_type,
        is_byzentine (BrachaRBProcess f (process_from_byzentine_type p)) (byzentine p)
    ) :
    UnusedSpec (Ref byzentine) forall_unused.
  Proof.
    hnf. intro. split ; intro.
    + case_eq act ; intros ; rewrite H0 in H ; simpl in H ; inversion H ;
      simpl_ActionClass ; destruct n0 || idtac ; simpl in * ; lia || inversion H.
    + case_eq act ; intros ; rewrite H0 in H ; simpl in H ; clear H0 ;
        guess_compose_type_from_action_class ; fold Nat.sub in * ; try rewrite <-Hbyzentine in * ; try inversion H ;
        lia || (split ; apply proj2_sig || lia) || (simpl_ActionClass ; inversion H4).
  Qed.

  Definition BrachaRB
    (byzentine : Byzentine_type -> IOADef BrachaRBAction)
    (Hbyzentine :
      forall p : Byzentine_type,
        is_byzentine (BrachaRBProcess f (process_from_byzentine_type p)) (byzentine p)
    )
    : IOADef BrachaRBAction :=
    CompositionExtended
      Leader_T
      (composition_extended_hyp byzentine Hbyzentine)
      (exists_output_spec byzentine Hbyzentine)
      (exists_input_spec byzentine Hbyzentine)
      (forall_unused_spec byzentine Hbyzentine)
  .

  Lemma proj1_zero_is_process_zero :
    forall p : Process,
      proj1_sig p = 0 -> p = process_zero.
  Proof.
    intros. assert (proj1_sig p = proj1_sig process_zero). auto.
    apply process_proof_irrelevence. auto.
  Qed.

  Lemma action_modulo_process_equality_dec :
    forall byzentine : Byzentine_type -> IOADef BrachaRBAction,
    forall Hbyzentine : (forall p : Byzentine_type, is_byzentine (BrachaRBProcess f (process_from_byzentine_type p)) (byzentine p)),
    forall m : InternMessage, forall s,
    {exists p, proj1_sig p < count - f /\ opt_act BrachaRBAction (BrachaRB byzentine Hbyzentine) s = Some (BrachaRBP2PSend p process_zero m)}+
      {forall p, proj1_sig p < count - f -> opt_act BrachaRBAction (BrachaRB byzentine Hbyzentine) s <> Some (BrachaRBP2PSend p process_zero m)}.
  Proof.
    intros.
    destruct forall_process_property_decidable with
      (fun p => proj1_sig p < count - f -> opt_act BrachaRBAction (BrachaRB byzentine Hbyzentine) s <> Some (BrachaRBP2PSend p process_zero m)).
    intro.
    case_eq (proj1_sig p <? count - f) ; intro ; simpl_arith_bool.
    destruct BrachaRBOptionAction_dec with
      (opt_act BrachaRBAction (BrachaRB byzentine Hbyzentine) s) (Some (BrachaRBP2PSend p process_zero m)) ; auto.
    left. intro. lia.
    auto.
    left.
    destruct e. exists x. hnf in H.
    case_eq (proj1_sig x <? count - f) ; intro ; simpl_arith_bool.
    split. auto.
    destruct BrachaRBOptionAction_dec with
      (opt_act BrachaRBAction (BrachaRB byzentine Hbyzentine) s) (Some (BrachaRBP2PSend x process_zero m)).
    auto. assert (proj1_sig x < count - f ->
       opt_act BrachaRBAction (BrachaRB byzentine Hbyzentine) s <> Some (BrachaRBP2PSend x process_zero m)).
    auto.
    apply H in H1. contradiction.
    assert (proj1_sig x < count - f ->
       opt_act BrachaRBAction (BrachaRB byzentine Hbyzentine) s <> Some (BrachaRBP2PSend x process_zero m)).
    intro. lia. apply H in H1. contradiction.
  Qed.

  Lemma send_ready_then_condition_satisfied :
    forall byzentine : Byzentine_type -> IOADef BrachaRBAction,
    forall Hbyzentine : (forall p : Byzentine_type, is_byzentine (BrachaRBProcess f (process_from_byzentine_type p)) (byzentine p)),
      forall e : ExecFragmentType (A := BrachaRB byzentine Hbyzentine),
      Exec e ->
      forall i : nat, forall m : Message, forall p : Process,
        proj1_sig p < count - f ->
        match composition_type_from_process p with
          | Leader_T =>
              BrachaRBSendBuffer
                (st BrachaRBAction (BrachaRB byzentine Hbyzentine) (e i) Leader_T)
                (process_zero, Ready m) = true ->
              let st := st BrachaRBAction (BrachaRB byzentine Hbyzentine) (e i) Leader_T in
              BrachaRBStep st >= 3 /\ (
                                      BrachaRBRecvBufferSize st (Echo m) >= 2*f+1 \/
                                        BrachaRBRecvBufferSize st (Ready m) >= f+1
                                    )
          | Other_T q =>
              BrachaRBSendBuffer
                (st BrachaRBAction (BrachaRB byzentine Hbyzentine) (e i) (Other_T q))
                (process_zero, Ready m) = true ->
              let st := st BrachaRBAction (BrachaRB byzentine Hbyzentine) (e i) (Other_T q) in
              BrachaRBStep st >= 3 /\ (
                                      BrachaRBRecvBufferSize st (Echo m) >= 2*f+1 \/
                                        BrachaRBRecvBufferSize st (Ready m) >= f+1
                                    )
          | _ => False
      end.
  Proof.
    intros.
    case_eq (composition_type_from_process p) ; [intro Heq | intros q Heq | intros | intros q Heq].
    intros.
    eapply project_execution_exist_with_exec in H.
    Unshelve. 5: apply Leader_T.
    decompose [ex and or] H.
    clear H.
    specialize H4 with i.
    decompose [and] H4. clear H4.
    fold st in H1.
    unfold BrachaRB in st.
    fold st in H.
    rewrite H in *.
    clear H st.
    eapply send_ready_then_condition_satisfied ; auto.
    apply H1.
    intros.
    eapply project_execution_exist_with_exec in H.
    Unshelve. 4: apply (Other_T q).
    decompose [ex and or] H.
    clear H.
    specialize H4 with i.
    decompose [and] H4. clear H4.
    fold st in H1.
    unfold BrachaRB in st.
    fold st in H.
    rewrite H in *.
    clear H st.
    eapply send_ready_then_condition_satisfied ; auto.
    apply H1.
    unfold composition_type_from_process in H1.
    destruct (composition_type_from_process_aux p) ; repeat simpl_match ; subst ; inversion H1.
    lia. auto.
    unfold composition_type_from_process in Heq.
    destruct (composition_type_from_process_aux p) ; repeat simpl_match ; subst ; inversion Heq.
    lia. subst. destruct p, q. simpl in *. subst. lia.
  Qed.

  Lemma two_ready_are_equals :
    forall byzentine : Byzentine_type -> IOADef BrachaRBAction,
    forall Hbyzentine : (forall p : Byzentine_type, is_byzentine (BrachaRBProcess f (process_from_byzentine_type p)) (byzentine p)),
      forall e : ExecFragmentType (A := BrachaRB byzentine Hbyzentine),
      Exec e ->
      forall i j : nat, forall m m' : Message, forall p q : Process,
        proj1_sig p < count - f -> proj1_sig q < count - f ->
        opt_act BrachaRBAction (BrachaRB byzentine Hbyzentine) (e i) = Some (BrachaRBP2PSend p process_zero (Ready m)) ->
        opt_act BrachaRBAction (BrachaRB byzentine Hbyzentine) (e j) = Some (BrachaRBP2PSend q process_zero (Ready m')) ->
        m = m'.
  Proof.
    intros.
    case_eq (Message_dec m m') ; intros ; auto.
    assert ((fun s => if action_modulo_process_equality_dec
                        (Ready m)
                        s
                  then true else false
           ) (e i)= true).
    simpl_match. auto. clear H5. specialize n1 with p. apply n1 in H0. contradiction.
    apply existence_of_first_state_for_property in H5.
    assert ((fun s => if action_modulo_process_equality_dec
                        (Ready m')
                        s
                  then true else false
           ) (e j)= true).
    simpl_match. auto. clear H6. specialize n1 with q. apply n1 in H1. contradiction.
    apply existence_of_first_state_for_property in H6.
    clear H0 H1 H2 H3 i j.
    decompose [ex and or] H5. decompose [ex and or] H6. clear H5 H6.
    simpl_match ; cycle 1. inversion H3. clear H0 H3.
    simpl_match ; cycle 1. inversion H1. clear H0 H1.
    clear p q.
    destruct n1 as [p Heq_p].
    destruct n2 as [q Heq_q].
    destruct Heq_p as [Hineq_p Hopt_act_eq_p].
    destruct Heq_q as [Hineq_q Hopt_act_eq_q].
    assert (BrachaRBSendBuffer (
                st
                  BrachaRBAction
                  (BrachaRB)
                  (e x)) (process_zero, Ready m) = true).


    edestruct project_execution_exist_with_exec as [e_proj].
    apply H.
    destruct (e_proj x0).
    destruct H0.
    assert (opt_act = Some (BrachaRBP2PSend q process_zero (Ready m))).
    specialize H1 with x0. decompose [and] H1. clear H1.
    unfold BrachaRB in Hopt_act_eq_p.
    rewrite Hopt_act_eq_p in H8.
    case_eq (ActionClass
               (Ref byzentine (composition_type_from_process p))
               (BrachaRBP2PSend p process_zero (Ready m'))) ; intros.
    rewrite H1 in H8.
    simpl_ActionClass ; inversion H1.
    unfold composition_type_from_process in H1.
    Print transition_send_only_if_in_send_buffer.
    assert (BrachaRBSendBuffer st (p, m) = true).

    apply conversion_never_byzentine in H5.

    unfold BrachaRB in Hopt_act_eq_p.
    erewrite H1 in Hopt_act_eq_p.
    apply transition_send_only_if_in_send_buffer in is_well_formed.
    destruct (e x0). simpl in Hopt_act_eq_p. subst opt_act.
    apply transition_send_only_if_in_send_buffer in is_well_formed.



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



    transition_send_only_if_in_send_buffer




    assert (
        let st := st BrachaRBAction (BrachaRB byzentine Hbyzentine) (e x0) Leader_T in
        BrachaRBStep st >= 3 /\ (
                                 BrachaRBRecvBufferSize st (Echo m) >= 2*f+1 \/
                                 BrachaRBRecvBufferSize st (Ready m) >= f+1
                              )).
    simpl.
    apply send_ready_then_condition_satisfied.






    assert (opt_act BrachaRBAction (BrachaRB byzentine Hbyzentine) (e x) =
                  Some (BrachaRBP2PSend p process_zero (Ready m))).
    eapply project_execution_exist_with_exec in H.
    destruct H as [e' H]. destruct H.
    specialize H0 with x0.
    destruct H0. destruct H1.
    case_eq (proj1_sig p =? 0) ; intro.
    assert (opt_act BrachaRBAction (Ref byzentine (Leader_T)) (e' x) =
                  Some (BrachaRBP2PSend q process_zero (Ready m))).
    unfold BrachaRB in Hopt_act_eq_p. rewrite Hopt_act_eq_p in H3.
    simpl in H3.
    rewrite H5 in H3. unfold BrachaRBProcess in H3. simpl in H3.
    create_sig Other_type (proj1_sig q) out.
    split. destruct q ; simpl in *.
    assert (opt_act BrachaRBAction (Ref byzentine (Other_T out)) (e' x) =
                  Some (BrachaRBP2PSend q process_zero (Ready m))).
    clear H2 H3.
    clear H4.


    
    destruct H5, H6.




    destruct (e i). destruct (e j).
    simpl in H2, H3. subst opt_act opt_act0.
    simpl_Transition. simpl_Transition.
    case_eq (Message_dec m m') ; intros.
    auto.

    guess_compose_type_from_action_class. move is_well_formed after is_well_formed0. guess_compose_type_from_action_class.
    apply proj1_zero_is_process_zero in H2, H4. subst p q. clear H3 H5.
    assert (Transition (BrachaRBProcess f process_zero) (st0 out) (BrachaRBP2PSend process_zero process_zero (Ready m')) (st'0 out)).
    apply is_well_formed0. discriminate.
    assert (Transition (BrachaRBProcess f process_zero) (st out0) (BrachaRBP2PSend process_zero process_zero (Ready m)) (st' out0)).
    apply is_well_formed. discriminate.
    apply transition_send_only_if_in_send_buffer in H2, H3.

  Lemma extend_past_properties
    (CompositionSet : Set)
    (H : CompositionExtendedHyp)
    (FOutput : ActionPool -> bool)
    (FOutputSpec : OutputSpec FOutput)
    (FInput : ActionPool -> bool)
    (FInputSpec : InputSpec FInput)
    (FUnused : ActionPool -> bool)
    (FUnusedSpec : UnusedSpec FUnused) : True.
    forall
  .

  Definition ProjectExec (ActionPool : Set) (exec : ExecFragmentType (ActionPool := ActionPool)) (proj : )

  Lemma project_exists

  Lemma extend_local_properties :
    forall P : IOAType -> Prop, forall A : IOAType,
      P A -> P

    apply send_ready_then_condition_satisfied with f process_zero e H st st in H2, H3.

    specialize is_well_formed with out. specialize is_well_formed0

    unfold BrachaRB in is_well_formed, is_well_formed0.

    apply transition_send_only_if_in_send_buffer in is_well_formed.
    apply send_ready_then_condition_satisfied in H0, H1.



  Lemma send_init_then_broadcast_before :
    forall byzentine : Byzentine_type -> IOADef BrachaRBAction,
    forall Hbyzentine : (forall p : Byzentine_type, is_byzentine (BrachaRBProcess f (process_from_byzentine_type p)) (byzentine p)),
      forall e : ExecFragmentType (A := BrachaRB byzentine Hbyzentine),
      Exec e ->
      forall i : nat, forall m : Message,
        act BrachaRBAction (BrachaRB byzentine Hbyzentine) (e i) = BrachaRBP2PSend process_zero process_zero (Init m) ->
        exists j : nat, j < i /\ act BrachaRBAction (BrachaRB byzentine Hbyzentine) (e j) = BrachaRBBroadcast m.
  Proof.
    intros.
    (* we build a goal such that we show the existance by induction *)
    assert (
        forall j : nat,
          (exists k : nat, k >= i - j /\ k < i /\ act BrachaRBAction (BrachaRB byzentine Hbyzentine) (e k) = BrachaRBBroadcast m) \/
          (BrachaRBSendBuffer (st BrachaRBAction (BrachaRB byzentine Hbyzentine) (e (i - j)) Leader_T) (process_zero, (Init m)) = true)
      ).
    induction j.
    + (* case i *)
      right. assert (i - 0 = i). lia. rewrite H1. clear H1.
      destruct (e i) ; simpl in *.
      specialize is_well_formed with Leader_T. intuition. clear H4. rewrite H0 in H3.
      simpl_ActionClass. assert (BrachaRBLeaderTransition f (st Leader_T) (BrachaRBP2PSend process_zero process_zero (Init m)) (st' Leader_T)).
      apply H3. discriminate.
      unfold BrachaRBLeaderTransition, BrachaRBLeader_compute_transition in H2. simpl in H2.
      simpl_match. inversion H2. case_eq (BrachaRBSendBuffer (st Leader_T) (process_zero, Init m)) ; intro. auto.
      assert (BrachaRBBuffer_sub (BrachaRBSendBuffer (st Leader_T)) process_zero (Init m) = BrachaRBSendBuffer (st' Leader_T)).
      rewrite <- H6. simpl. auto.
      assert (BrachaRBBuffer_sub (BrachaRBSendBuffer (st Leader_T)) process_zero (Init m) (process_zero, Init m) = BrachaRBSendBuffer (st' Leader_T) (process_zero, Init m)).
      rewrite H7 ; auto. rewrite H4 in H5. inversion H5.
      inversion H2.
    + (* induction *)
      destruct H as [H Hstart]. unfold ExecFragment in H. specialize H with (i - S j).
      destruct IHj. left. destruct H1. exists x. intuition. lia.
      case_eq (i - j =? 0) ; intro Heq ; simpl_arith_bool.
      unfold Start, BrachaRB, CompositionExtended in Hstart.
      specialize Hstart with Leader_T. simpl in Hstart. unfold BrachaRBLeaderStart in Hstart.
      rewrite Heq in *. destruct (e 0). simpl in *. rewrite Hstart in H1. simpl in H1. unfold BrachaRBBuffer_empty_set in H1. inversion H1.
      case_eq (act BrachaRBAction (BrachaRB byzentine Hbyzentine) (e (i - S j))) ; intros.
      case_eq (Message_dec m0 m) ; intros.
      - left. exists (i - S j). intuition. lia. subst m0. auto.
      - right. destruct (e (i - S j)). simpl in *.
        specialize is_well_formed with Leader_T. intuition. clear H7. rewrite H2 in H6.
        simpl_ActionClass. assert (BrachaRBLeaderTransition f (st Leader_T) (BrachaRBBroadcast m0) (st' Leader_T)).
        apply H6. discriminate.
        unfold BrachaRBLeaderTransition, BrachaRBLeader_compute_transition in H5.
        simpl_match. inversion H5. case_eq (BrachaRBSendBuffer (st Leader_T) (process_zero, Init m)) ; intro. auto.
        rewrite H in H9. assert (i - S j + 1 = i - j). lia. rewrite H10 in *. clear H10.
        assert (InternMessage_dec_bool (Init m) (Init m0) =
                  BrachaRBSendBuffer (IOA.st BrachaRBAction (BrachaRB byzentine Hbyzentine) (e (i - j)) Leader_T) (process_zero, Init m)).
        rewrite <-H9. simpl. auto. rewrite H1 in H10. unfold InternMessage_dec_bool in H10. simpl_match. inversion n1. intuition.
        inversion H10.
        inversion H5. rewrite H in H9. rewrite H9. assert (i - S j + 1 = i - j). lia. rewrite H8 in *. clear H8. auto.
      - right.
        destruct (e (i - S j)). simpl in *. specialize is_well_formed with Leader_T. intuition. rewrite H in *. simpl in *.
        assert (Htmp : i - S j + 1 = i - j). lia. rewrite Htmp in * ; clear Htmp.
        case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool.
        * rewrite H2 in *.
          assert (BrachaRBLeaderTransition f (st Leader_T) (BrachaRBDeliver p m0) (IOA.st BrachaRBAction (BrachaRB byzentine Hbyzentine) (e (i - j)) Leader_T)).
          apply H5. unfold BrachaRBLeaderActionClass. simpl_match. inversion H7. simpl_arith_bool. lia.
          unfold BrachaRBLeaderTransition, BrachaRBLeader_compute_transition in H7.
          simpl_match ; repeat simpl_arith_bool ; inversion H7 ; rewrite <-H12 in H1 ; simpl in H1 ; auto.
        * assert (st Leader_T = IOA.st BrachaRBAction (BrachaRB byzentine Hbyzentine) (e (i - j)) Leader_T). apply H6. unfold BrachaRBLeaderActionClass.
          rewrite H2. simpl_match. simpl_arith_bool. lia. auto.
          rewrite H7. auto.
      - right.
        destruct (e (i - S j)). simpl in *. specialize is_well_formed with Leader_T. intuition. rewrite H in *. simpl in *.
        assert (Htmp : i - S j + 1 = i - j). lia. rewrite Htmp in * ; clear Htmp.
        case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool.
        * rewrite H2 in *.
          assert (BrachaRBLeaderTransition f (st Leader_T) (BrachaRBP2PRecv p p0 i0) (IOA.st BrachaRBAction (BrachaRB byzentine Hbyzentine) (e (i - j)) Leader_T)).
          apply H5. unfold BrachaRBLeaderActionClass. simpl_match. inversion H7. simpl_arith_bool. lia.
          destruct (e (i - j)).
          simpl in *. induction i0 ;
          unfold BrachaRBLeaderTransition, BrachaRBLeader_compute_transition in H7.
          {
            rewrite H4 in H7. simpl in H7.
            simpl_match ; repeat simpl_arith_bool ;
            inversion H7 ;
            rewrite <-H11 in H1 || rewrite <-H10 in H1 ; simpl in H1 ; repeat simpl_arith_bool ; auto ;
            unfold InternMessage_dec_bool in H1 ; repeat simpl_match ; inversion n0 || inversion H1.
          }
          {
            rewrite H4 in H7. simpl in H7.
            repeat simpl_match ; repeat simpl_arith_bool ;
            inversion H7 ;
            rewrite <-H11 in H1 || rewrite <-H10 in H1 || rewrite <-H13 in H1 || rewrite <- H14 in H1 || rewrite <- H15 in H1 ; simpl in H1 ; repeat simpl_arith_bool ; auto ;
            unfold InternMessage_dec_bool in H1 ; repeat simpl_match ; inversion n0 || inversion H1 || inversion n1.
          }
          {
            rewrite H4 in H7. simpl in H7.
            repeat simpl_match ; repeat simpl_arith_bool ;
            inversion H7 ;
            rewrite <-H11 in H1 || rewrite <-H10 in H1 || rewrite <-H13 in H1 || rewrite <- H14 in H1 || rewrite <- H15 in H1 || rewrite <-H16 in H1
            ; simpl in H1 ; repeat simpl_arith_bool ; auto ;
            unfold InternMessage_dec_bool in H1 ; repeat simpl_match ; inversion n0 || inversion H1 || inversion n1.
          }
        * rewrite H2 in *.
          assert (st Leader_T = IOA.st BrachaRBAction (BrachaRB byzentine Hbyzentine) (e (i - j)) Leader_T).
          apply H6. simpl ; simpl_match ; repeat simpl_arith_bool ; lia || auto.
          rewrite H7. auto.
      - right.
        destruct (e (i - S j)). simpl in *. specialize is_well_formed with Leader_T. intuition. rewrite H in *. simpl in *.
        assert (Htmp : i - S j + 1 = i - j). lia. rewrite Htmp in * ; clear Htmp.
        case_eq (proj1_sig p =? 0) ; intro ; simpl_arith_bool.
        * rewrite H2 in *.
          assert (BrachaRBLeaderTransition f (st Leader_T) (BrachaRBP2PSend p p0 i0) (IOA.st BrachaRBAction (BrachaRB byzentine Hbyzentine) (e (i - j)) Leader_T)).
          apply H5. unfold BrachaRBLeaderActionClass. simpl_match. inversion H7. simpl_arith_bool. lia.
          destruct (e (i - j)).
          simpl in *. induction i0 ;
          unfold BrachaRBLeaderTransition, BrachaRBLeader_compute_transition in H7.
          {
            rewrite H4 in H7. simpl in H7. unfold BrachaRBBuffer_sub in H7.
            simpl_match ; repeat simpl_arith_bool ;
            inversion H7 ;
            rewrite <-H11 in H1 || rewrite <-H10 in H1 ; simpl in H1 ; repeat simpl_arith_bool ; auto ;
            unfold InternMessage_dec_bool in H1 ; repeat simpl_match ; inversion n0 || inversion H1 ; lia || auto.
          }
          {
            rewrite H4 in H7. simpl in H7. unfold BrachaRBBuffer_sub in H7.
            repeat simpl_match ; repeat simpl_arith_bool ;
            inversion H7 ;
            rewrite <-H11 in H1 || rewrite <-H10 in H1 || rewrite <-H13 in H1 || rewrite <- H14 in H1 || rewrite <- H15 in H1 ; simpl in H1 ; repeat simpl_arith_bool ; auto ;
            unfold InternMessage_dec_bool in H1 ; repeat simpl_match ; inversion n0 || inversion H1 || inversion n1 ; lia || auto.
          }
          {
            rewrite H4 in H7. simpl in H7. unfold BrachaRBBuffer_sub in H7.
            repeat simpl_match ; repeat simpl_arith_bool ;
            inversion H7 ;
            rewrite <-H11 in H1 || rewrite <-H10 in H1 || rewrite <-H13 in H1 || rewrite <- H14 in H1 || rewrite <- H15 in H1 || rewrite <-H16 in H1
            ; simpl in H1 ; repeat simpl_arith_bool ; auto ;
            unfold InternMessage_dec_bool in H1 ; repeat simpl_match ; inversion n0 || inversion H1 || inversion n1 ; lia || auto.
          }
        * rewrite H2 in *.
          assert (st Leader_T = IOA.st BrachaRBAction (BrachaRB byzentine Hbyzentine) (e (i - j)) Leader_T).
          apply H6. simpl ; simpl_match ; repeat simpl_arith_bool ; lia || auto.
          rewrite H7. auto.
    + (* conclusion *)
      specialize H1 with i. destruct H1.
      - destruct H1. exists x. intuition.
      - destruct H as [H Hstart]. unfold Start, BrachaRB, CompositionExtended in Hstart.
        specialize Hstart with Leader_T. simpl in Hstart. unfold BrachaRBLeaderStart in Hstart.
        unfold BrachaRB, CompositionExtended in H1. assert (i-i = 0). lia. rewrite H2 in H1. simpl in H1. rewrite Hstart in H1.
        simpl in H1. unfold BrachaRBBuffer_empty_set in H1. inversion H2. inversion H1.
  Qed.

  Theorem exists_effective_broadcast :
    forall byzentine : Byzentine_type -> IOADef BrachaRBAction,
    forall Hbyzentine : (forall p : Byzentine_type, is_byzentine (BrachaRBOther f (proj1_sig p)) (byzentine p)),
      forall e : ExecFragmentType (A := BrachaRB byzentine Hbyzentine),
      Exec e -> FairFragment e ->
      exists i : nat, exists m : Message,
        act BrachaRBAction (BrachaRB byzentine Hbyzentine) (e i) = BrachaRBBroadcast m /\
          st BrachaRBAction (BrachaRB byzentine Hbyzentine) (e i) = st' BrachaRBAction (BrachaRB byzentine Hbyzentine) (e i).
  Proof.
    intros.
    Open Scope ltl_scope.

    unfold FairFragment in H0. specialize H0 with (BrachaRBBroadcast root_message).
    destruct H0. hnf in H0.



          




  Theorem bracha_leader_non_byzentine_correct :
    forall byzentine : Byzentine_type -> IOADef BrachaRBAction,
    forall Hbyzentine : (forall p : Byzentine_type, is_byzentine (BrachaRBOther f (proj1_sig p)) (byzentine p)),
      forall e : ExecFragmentType (A := BrachaRB byzentine Hbyzentine),
      Exec e -> FairFragment e ->
      exists i : nat, exists m : Message,
        act BrachaRBAction (BrachaRB byzentine Hbyzentine) (e i) = BrachaRBBroadcast m /\
          forall j : nat, forall p : Process,
            proj1_sig p < count - f ->
            act BrachaRBAction (BrachaRB byzentine Hbyzentine) (e j) = BrachaRBDeliver p m.
  Proof.



      forall i j : nat, forall p q : Process,
        proj1_sig p < count - f /\ proj1_sig q < count - f
        forall m m' : Message, e $ i |= N (fun s => act BrachaRBAction (BrachaRB byzentine Hbyzentine) s = BrachaRBDeliver p m) /\
                            e $ j |= N (fun s => act s = BrachaRBDeliver q m') ->
                          True
  .


End Leader_not_byzentine.
