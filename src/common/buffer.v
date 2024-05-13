Require Import common.IOA.
Require Import common.LTL.
Require Import common.tactic.
Require Import Lia.
Require Import Arith.
Require Import Bool.
Require Import FunctionalExtensionality.

Section Buffer.
  Set Implicit Arguments.

  Variable P : Set.
  Hypothesis eq_dec : forall p q : P, {p = q}+{p <> q}.

  Definition buffer := P -> bool.
  Definition empty_buffer : buffer := fun p => false.
  Definition buffer_add
    (b : buffer)
    (p : P) :=
    fun p' => if eq_dec p p' then true else b p'.
  Definition buffer_sub
    (b : buffer)
    (p : P) :=
    fun p' => if eq_dec p p' then false else b p'.
  Definition in_buffer
    (b : buffer)
    (p : P) :=
    b p = true.

  Lemma buffer_empty_then_false :
    forall p : P, empty_buffer p = false.
  Proof.
    auto.
  Qed.

  Lemma buffer_add_in_buffer_invariant :
    forall b : buffer, forall p : P,
      b p = true -> buffer_add b p = b.
  Proof.
    intros.
    unfold buffer_add.
    apply functional_extensionality. intro p'.
    destruct eq_dec with p p' ; subst ; auto.
  Qed.

  Lemma buffer_add_then_in_buffer :
    forall b : buffer, forall p : P,
      buffer_add b p p = true.
  Proof.
    intros.
    unfold buffer_add.
    destruct eq_dec with p p ; auto.
  Qed.

  Lemma buffer_add_in_buffer_keep_true :
    forall b : buffer, forall p p' : P,
      b p = true -> buffer_add b p' p = true.
  Proof.
    intros.
    unfold buffer_add.
    destruct eq_dec with p' p ; auto.
  Qed.

  Lemma buffer_add_keep_other_unchaged :
    forall b : buffer, forall p p' : P,
      p <> p' -> buffer_add b p p' = b p'.
  Proof.
    intros.
    unfold buffer_add.
    destruct eq_dec with p p' ; auto ; contradiction.
  Qed.

  Lemma buffer_add_twice_permute :
    forall b : buffer, forall p p' : P,
      buffer_add (buffer_add b p) p' = buffer_add (buffer_add b p') p.
  Proof.
    intros.
    apply functional_extensionality. intro q.
    unfold buffer_add.
    destruct eq_dec with p' q ; destruct eq_dec with p q ; auto.
  Qed.

  Lemma buffer_sub_not_in_buffer_invariant :
    forall b : buffer, forall p : P,
      b p = false -> buffer_sub b p = b.
  Proof.
    intros.
    apply functional_extensionality. intro q.
    unfold buffer_sub.
    destruct eq_dec with p q ; subst ; auto.
  Qed.

  Lemma buffer_sub_then_not_in_buffer :
    forall b : buffer, forall p : P,
      buffer_sub b p p = false.
  Proof.
    intros.
    unfold buffer_sub.
    destruct eq_dec with p p ; auto ; contradiction.
  Qed.

  Lemma buffer_sub_not_in_buffer_keep_false :
    forall b : buffer, forall p p' : P,
      b p = false -> buffer_sub b p' p = false.
  Proof.
    intros.
    unfold buffer_sub.
    destruct eq_dec with p' p ; auto.
  Qed.

  Lemma buffer_sub_twice_permute :
    forall b : buffer, forall p p' : P,
      buffer_sub (buffer_sub b p) p' = buffer_sub (buffer_sub b p') p.
  Proof.
    intros.
    apply functional_extensionality. intro q.
    unfold buffer_sub.
    destruct eq_dec with p' q ; destruct eq_dec with p q ; auto.
  Qed.

  Lemma buffer_sub_keep_other_unchaged :
    forall b : buffer, forall p p' : P,
      p <> p' -> buffer_sub b p p' = b p'.
  Proof.
    intros.
    unfold buffer_sub.
    destruct eq_dec with p p' ; auto ; contradiction.
  Qed.

  Lemma buffer_sub_add_not_in_buffer_then_invarient :
    forall b : buffer, forall p : P,
      b p = false -> buffer_sub (buffer_add b p) p = b.
  Proof.
    intros.
    apply functional_extensionality. intro q.
    unfold buffer_sub, buffer_add.
    repeat simpl_match ; subst ; auto.
  Qed.

  Lemma buffer_sub_add_distinct_permute :
    forall b : buffer, forall p p' : P,
      p <> p' -> buffer_sub (buffer_add b p) p' = buffer_add (buffer_sub b p') p.
  Proof.
    intros.
    apply functional_extensionality. intro q.
    unfold buffer_sub, buffer_add.
    repeat simpl_match ; subst ; auto.
  Qed.

  Lemma buffer_add_sub_in_buffer_then_invarient :
    forall b : buffer, forall p : P,
      b p = true -> buffer_add (buffer_sub b p) p = b.
  Proof.
    intros.
    apply functional_extensionality. intro q.
    unfold buffer_sub, buffer_add.
    repeat simpl_match ; subst ; auto.
  Qed.

  Ltac buffer_solver :=
    intros ;
    subst ; simpl in * ;
    match goal with
      (* boolean goal solving *)
      | H : true = false |- _ => inversion H
      | H : false = true |- _ => inversion H
      (* empty buffer reduction *)
      | |- context [empty_buffer _] =>
          rewrite buffer_empty_then_false
      | H : context [empty_buffer _] |- _ =>
          rewrite buffer_empty_then_false in H
      (* repetition reduction *)
      | |- context [buffer_add _ ?p ?p] =>
          rewrite buffer_add_then_in_buffer
      | |- context [buffer_sub _ ?p ?p] =>
          rewrite buffer_sub_then_not_in_buffer
      | H : context [buffer_add _ ?p ?p] |- _ =>
          rewrite buffer_add_then_in_buffer in H
      | H : context [buffer_sub _ ?p ?p] |- _ =>
          rewrite buffer_sub_then_not_in_buffer in H
      (* buffer property reduction *)
      | _ : context [?b ?p = true] |- context [buffer_add ?b ?p] =>
          rewrite buffer_add_in_buffer_invariant
      | _ : context [?b ?p = true] |- context [buffer_add ?b _ ?p] =>
          rewrite buffer_add_in_buffer_keep_true
      | _ : context [?b ?p = false] |- context [buffer_sub ?b ?p] =>
          rewrite buffer_sub_not_in_buffer_invariant
      | _ : context [?b ?p = false] |- context [buffer_sub ?b _ ?p] =>
          rewrite buffer_sub_not_in_buffer_keep_false
      | _ : context [?b ?p = true], H : context [buffer_add ?b ?p] |- _ =>
          rewrite buffer_add_in_buffer_invariant in H
      | _ : context [?b ?p = true], H : context [buffer_add ?b _ ?p] |- _ =>
          rewrite buffer_add_in_buffer_keep_true in H
      | _ : context [?b ?p = false], H : context [buffer_sub ?b ?p] |- _ =>
          rewrite buffer_sub_not_in_buffer_invariant in H
      | _ : context [?b ?p = false], H : context [buffer_sub ?b _ ?p] |- _ =>
          rewrite buffer_sub_not_in_buffer_keep_false in H
      (* add and sub alternance reduction *)
      | _ : context [?b ?p = false] |-
          context [buffer_sub (buffer_add ?b ?p) ?p] =>
          rewrite buffer_sub_add_not_in_buffer_then_invarient end ; (*)
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
    end ;*)
    (intuition ; fail) || buffer_solver
  .

  Definition buffer_union (b b' : buffer) :=
    fun p => b p || b' p.

  Lemma buffer_add_left_then_add_union :
    forall b b' : buffer, forall p : P,
      buffer_union (buffer_add b p) b' = buffer_add (buffer_union b b') p.
  Proof.
    intros.
    apply functional_extensionality. intro q.
    unfold buffer_union, buffer_add.
    simpl_match ; auto.
  Qed.

  Lemma buffer_add_right_then_add_union :
    forall b b' : buffer, forall p : P,
      buffer_union b (buffer_add b' p) = buffer_add (buffer_union b b') p.
  Proof.
    intros.
    apply functional_extensionality. intro q.
    unfold buffer_union, buffer_add.
    simpl_match ; auto with bool.
  Qed.

  Lemma buffer_sub_union_is_union_sub :
    forall b b' : buffer, forall p : P,
      buffer_sub (buffer_union b b') p = buffer_union (buffer_sub b p) (buffer_sub b' p).
  Proof.
    intros.
    apply functional_extensionality. intro q.
    unfold buffer_union, buffer_sub.
    simpl_match ; auto with bool.
  Qed.

  Lemma buffer_union_commute :
    forall b b' : buffer,
      buffer_union b b' = buffer_union b' b.
  Proof.
    intros.
    apply functional_extensionality. intro p.
    unfold buffer_union. auto with bool.
  Qed.

  Definition inclusion
    (b b' : buffer) :
    forall p : P, (negb (b p)) && (b' p).

  Definition strict_inclusion


  Inductive buffer_size : buffer -> nat -> Prop :=
    | buffer_empty : buffer_size empty_buffer 0
    | buffer_some : forall b : buffer, forall n : nat, buffer_size b n -> forall p : P, b p = false -> buffer_size (buffer_add b p) (S n).

  Lemma nul_size_then_empty_set :
    forall b : buffer,
      buffer_size b 0 -> b = empty_buffer.
  Proof.
    intros.
    inversion H. auto.
  Qed.

  Lemma buffer_sub_reduce_size :
    forall i : nat, forall b : buffer, forall p : P,
      buffer_size b (S i) -> b p = true -> buffer_size (buffer_sub b p) i.
  Proof.
    induction i.
    - intros. inversion H. inversion H2. subst.
      unfold buffer_add in H0. simpl_match.
      subst. rewrite buffer_sub_add_not_in_buffer_then_invarient ; auto.
      rewrite buffer_empty_then_false in H0. inversion H0.
    - intros. inversion H. subst.
      destruct eq_dec with p p0. subst.
      rewrite buffer_sub_add_not_in_buffer_then_invarient ; auto.
      rewrite buffer_sub_add_distinct_permute. apply buffer_some.
      apply IHi. apply H2. unfold buffer_add in H0.
      simpl_match ; subst ; auto. buffer_solver. auto.
  Qed.

  Lemma size_of_union_bigger_than_distinct_size :
    forall j i : nat, forall b b' : buffer,
      buffer_size (buffer_union b b') j ->
      buffer_size b i ->
      i <= j.
  Proof.
    induction j.
    - intros.
      apply nul_size_then_empty_set in H.
      destruct H0 ; auto.
      assert (buffer_union (buffer_add b p) b' p = empty_buffer p). rewrite H. auto.
      unfold buffer_union in H2.
      buffer_solver.
    - intros.
      case_eq i ; intros ; subst i.
      lia. assert (n <= j) ; try lia.
      inversion H0. subst.
      eapply buffer_sub_reduce_size in H. rewrite buffer_sub_union_is_union_sub in H.
      eapply IHj. apply H. Unshelve. 3 : apply p.
      rewrite buffer_sub_add_not_in_buffer_then_invarient ; auto.
      rewrite buffer_add_left_then_add_union. rewrite buffer_add_then_in_buffer. auto.
  Qed.

  Lemma intersection_of_big_sets_is_non_empty :
    forall j i i' : nat, forall b b' : buffer,
      buffer_size (buffer_union b b') j ->
      buffer_size b i ->
      buffer_size b' i' ->
      j < i + i' ->
      exists p : P, b p = true  /\ b' p = true.
  Proof.
    induction j.
    - intros.
      assert (i <= 0).
      eapply size_of_union_bigger_than_distinct_size. apply H. auto.
      assert (i' <= 0).
      eapply size_of_union_bigger_than_distinct_size. rewrite buffer_union_commute in H. apply H. auto. lia.
    - intros.
      assert (i <= S j).
      eapply size_of_union_bigger_than_distinct_size. apply H. auto.
      assert (i' <= S j).
      eapply size_of_union_bigger_than_distinct_size. rewrite buffer_union_commute in H. apply H. auto.
      assert (i > 0). lia. assert (i' > 0). lia.
      inversion H0 ; subst. lia.
      inversion H1 ; subst. lia.
      destruct eq_dec with p p0. subst p0.
      exists p. split ; apply buffer_add_then_in_buffer.
      case_eq (b p) ; intro. exists p. split.
      apply buffer_add_then_in_buffer. apply buffer_add_in_buffer_keep_true. auto.
      assert (exists p : P, b0 p = true /\ buffer_add b p0 p = true). eapply IHj.
      eapply buffer_sub_reduce_size in H.
      rewrite buffer_add_left_then_add_union in H.
      assert (buffer_sub (buffer_add (buffer_union b0 (buffer_add b p0)) p) p = buffer_union b0 (buffer_add b p0)). apply buffer_sub_add_not_in_buffer_then_invarient.
      rewrite buffer_add_right_then_add_union. rewrite buffer_add_keep_other_unchaged.
      unfold buffer_union. auto with bool. auto.
      rewrite H12 in H. clear H12. auto.
      rewrite buffer_add_left_then_add_union. rewrite buffer_add_then_in_buffer. auto.
      assert (buffer_size (buffer_sub (buffer_add b0 p) p) n). apply buffer_sub_reduce_size. auto.
      apply buffer_add_then_in_buffer. rewrite buffer_sub_add_not_in_buffer_then_invarient in H12. apply H12.
      auto. apply H1. lia. destruct H12. destruct H12. exists x. split. rewrite buffer_add_in_buffer_keep_true ; auto.
      auto.
  Qed.
End Buffer.

Global Ltac buffer_solver :=
    intros ;
    subst ; simpl in * ;
    match goal with
      (* boolean goal solving *)
      | H : true = false |- _ => inversion H
      | H : false = true |- _ => inversion H
      (* empty buffer reduction *)
      | |- context [empty_buffer _ _] =>
          rewrite buffer_empty_then_false
      | H : context [empty_buffer _ _] |- _ =>
          rewrite buffer_empty_then_false in H
      (* repetition reduction *)
      | |- context [buffer_add _ _ ?p ?p] =>
          rewrite buffer_add_then_in_buffer
      | |- context [buffer_sub _ _ ?p ?p] =>
          rewrite buffer_sub_then_not_in_buffer
      | H : context [buffer_add _ _ ?p ?p] |- _ =>
          rewrite buffer_add_then_in_buffer in H
      | H : context [buffer_sub _ _ ?p ?p] |- _ =>
          rewrite buffer_sub_then_not_in_buffer in H
      (* buffer property reduction *)
      | _ : context [?b ?p = true] |- context [buffer_add _ ?b ?p] =>
          rewrite buffer_add_in_buffer_invariant
      | _ : context [?b ?p = true] |- context [buffer_add _ ?b _ ?p] =>
          rewrite buffer_add_in_buffer_keep_true
      | _ : context [?b ?p = false] |- context [buffer_sub _ ?b ?p] =>
          rewrite buffer_sub_not_in_buffer_invariant
      | _ : context [?b ?p = false] |- context [buffer_sub _ ?b _ ?p] =>
          rewrite buffer_sub_not_in_buffer_keep_false
      | _ : context [?b ?p = true], H : context [buffer_add _ ?b ?p] |- _ =>
          rewrite buffer_add_in_buffer_invariant in H
      | _ : context [?b ?p = true], H : context [buffer_add _ ?b _ ?p] |- _ =>
          rewrite buffer_add_in_buffer_keep_true in H
      | _ : context [?b ?p = false], H : context [buffer_sub _ ?b ?p] |- _ =>
          rewrite buffer_sub_not_in_buffer_invariant in H
      | _ : context [?b ?p = false], H : context [buffer_sub _ ?b _ ?p] |- _ =>
          rewrite buffer_sub_not_in_buffer_keep_false in H
      (* add and sub alternance reduction *)
      | _ : context [?b ?p = false] |-
          context [buffer_sub _ (buffer_add ?b ?p) ?p] =>
          rewrite buffer_sub_add_not_in_buffer_then_invarient end ;
    (intuition ; fail) || buffer_solver
  .
