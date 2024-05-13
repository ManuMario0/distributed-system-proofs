Require Import List.
Require Import Arith.
Require Import Nat.
Require Import Lia.

Declare Scope ltl_scope.

Section ltl.
  Set Implicit Arguments.
  Variable A : Type.
  Definition Run := nat -> A.
  Definition LTLFormula := Run -> nat -> Prop.

  Definition ltl_apply (l : Run) (i : nat) (P : LTLFormula) : Prop :=
    P l i.
  Notation "l $ i |= p" := (ltl_apply l i p) (at level 80) : ltl_scope.
  Definition ltl_not (l : Run) (i : nat) (P : LTLFormula) : Prop :=
    ~ (P l i).
  Notation "~ p" := (fun l i => ltl_not l i p) : ltl_scope.
  Definition ltl_or (l : Run) (i : nat) (P Q : LTLFormula) : Prop :=
    (P l i) \/ (Q l i).
  Notation "p \/ q" := (fun l i => ltl_or l i p q) : ltl_scope.
  Definition ltl_and (l : Run) (i : nat) (P Q : LTLFormula) : Prop :=
    (P l i) /\ (Q l i).
  Notation "p /\ q" := (fun l i => ltl_and l i p q) : ltl_scope.
  Definition ltl_impl (l : Run) (i : nat) (P Q : LTLFormula) : Prop :=
    (P l i) -> (Q l i).
  Notation "p -> q" := (fun l i => ltl_impl l i p q) : ltl_scope.

  Definition ltl_now (l : Run) (i : nat) (P : A -> Prop) : Prop :=
    P (l i).
  Notation "'N' p" := (fun l i => ltl_now l i p) (at level 70) : ltl_scope.

  Definition ltl_strict_until (l : Run) (i : nat) (P Q : LTLFormula) : Prop :=
    exists j : nat, i < j /\ (Q l j) /\ (forall k : nat, k < j -> i < k -> (P l k)).
  Notation "p 'SU' q" := (fun l i => ltl_strict_until l i p q) (at level 70) : ltl_scope.

  Open Scope ltl_scope.

  Lemma ltl_strict_until_fold :
    forall (l : Run) (i : nat) (P Q : LTLFormula),
       (l$ i+1 |= P SU Q) -> (l $ i+1 |= P) -> (l$ i |= P SU Q).
  Proof.
    intros. hnf in H, H0. hnf.
    destruct H. destruct H.
    destruct H1.
    exists x. split.
    lia.
    split.
    auto.
    intro. specialize H2 with k.
    intros. case_eq (i+1 =? k) ; intro.
    apply PeanoNat.Nat.eqb_eq in H5. rewrite <- H5. auto.
    apply PeanoNat.Nat.eqb_neq in H5. apply H2. lia. lia.
  Qed.

  Lemma ltl_strict_until_unfold :
    forall (l : Run) (i : nat) (P Q : LTLFormula),
      (l$ i |= P SU Q) -> (l$ i+1 |= P) -> (l $ i+1 |= ~Q) -> (l $ i+1 |= P SU Q).
  Proof.
    intros. hnf in H, H0, H1. hnf.
    destruct H. destruct H. destruct H2. exists x.
    split.
    case_eq (i+1 =? x) ; intro.
    apply PeanoNat.Nat.eqb_eq in H4. rewrite <-H4 in H2. contradiction.
    apply PeanoNat.Nat.eqb_neq in H4. lia.
    split ; auto.
    intros. specialize H3 with k. apply H3 ; auto. lia.
  Qed.

  Hint Resolve ltl_strict_until_unfold ltl_strict_until_fold : ltl.

  Close Scope ltl_scope.

  Definition ltl_until (l : Run) (i : nat) (P Q : LTLFormula) : Prop :=
    exists j : nat, i <= j /\ (Q l j) /\ (forall k : nat, k <= j -> i < k -> (P l k)).
  (*)
  Definition ltl_until (l : Run) (i : nat) (P Q : LTLFormula) : Prop :=
    l$ i |= (Q \/ (P /\ (P SU Q))).*)
  Notation "p 'U' q" := (fun l i => ltl_until l i p q) (at level 70) : ltl_scope.

  Open Scope ltl_scope.
  Definition ltl_next (l : Run) (i : nat) (P : LTLFormula) : Prop :=
    l$ i |= (fun (l : Run) (i : nat) => False) SU P.
  Notation "'X' p" := (fun l i => ltl_next l i p) (at level 70) : ltl_scope.

  Lemma ltl_next_unfold :
    forall (l : Run) (i : nat) (P : LTLFormula), (l$ i |= X P) -> (l$ i+1 |= P).
  Proof.
    intros. hnf. hnf in H.
    destruct H. destruct H. destruct H0.
    case_eq (x =? i+1) ; intro.
    apply PeanoNat.Nat.eqb_eq in H2. rewrite <- H2. auto.
    apply PeanoNat.Nat.eqb_neq in H2. specialize H1 with (i+1). assert (False). apply H1 ; lia. contradiction.
  Qed.

  Lemma ltl_next_fold :
    forall (l : Run) (i : nat) (P : LTLFormula), (l$ i+1 |= P) -> (l $ i |= X P).
  Proof.
    intros. hnf. hnf in H.
    exists (i+1). split.
    lia.
    split.
    auto.
    intro. intros. lia.
  Qed.
  Hint Resolve ltl_next_unfold ltl_next_fold : ltl.

  Definition ltl_strict_future (l : Run) (i : nat) (P : LTLFormula) : Prop :=
    l$ i |= (fun _ _ => True) SU P.
  Notation "'SF' p" := (fun l i => ltl_strict_future l i p) (at level 70) : ltl_scope.

  Definition ltl_future (l : Run) (i : nat) (P : LTLFormula) : Prop :=
    l$ i |= (fun _ _ => True) U P.
  Notation "'F' p" := (fun l i => ltl_future l i p) (at level 70) : ltl_scope.

  Lemma ltl_future_is_exists :
    forall (l : Run) (i : nat) (P : LTLFormula), l $ i |= F P <-> (exists j : nat, and (j >= i) (l $ j |= P)).
  Proof.
    intros l i P.
    split ; intro H.
    - destruct H. exists x. destruct H. split ; auto. destruct H0. auto.
    - destruct H. exists x. destruct H. split ; auto.
  Qed.

(*)
Lemma ltl_strict_future_unfold {A : Type} :
  forall (a : A) (l : LList A) (P : LList A -> Prop), (LCons a l) |= SF P -> l |= F P.
Proof.
  intros.
  case_eq l ; intros ; rewrite H0 in H ; hnf in H ; apply ltl_strict_until_unfold in H ; auto.
Qed.

Lemma ltl_future_fold {A : Type} :
  forall (a : A) (l : LList A) (P : LList A -> Prop), l |= F P -> LCons a l |= F P.
Proof.
  intros. case_eq l ; intros.
  + rewrite H0 in H. hnf in H. hnf. right. split ; auto. apply ltl_strict_until_QHolds. destruct H. auto.
    destruct H. inversion H1.
  + hnf. rewrite H0 in H. case H ; intros.
    - right. split ; auto. apply ltl_strict_until_QHolds. auto.
    - destruct H1. right. split ; auto. apply ltl_strict_until_LCons ; auto.
Qed.

Lemma ltl_future_unfold {A : Type} :
  forall (a : A) (l : LList A) (P : LList A -> Prop), (LCons a l) |= F P -> ~ (P (LCons a l)) -> l |= F P.
Proof.
  intros.
  inversion H. contradiction.
  destruct H1. apply ltl_strict_until_unfold in H2. auto.
Qed.
Global Hint Resolve ltl_strict_future_
*)

  Definition ltl_general (l : Run) (i : nat) (P : LTLFormula) : Prop :=
    forall j : nat, j >= i -> l $ j |= P.
  (*)
  Definition ltl_general (l : Run) (i : nat) (P : LTLFormula) : Prop :=
    l$ i |= (~ (F (~ P))).*)
  Notation "'G' p" := (fun l i => ltl_general l i p) (at level 70) : ltl_scope.

  (*)
  Lemma ltl_general_is_forall :
    forall (l : Run) (i : nat) (P : LTLFormula) (H : forall i' : nat, {P l i'}+{~P l i'}), l $ i |= G P <-> forall j : nat, j >= i -> l $ j |= P.
  Proof.
    intros l i P Hdec.
    hnf. split ; intro H.
    - hnf in H. intros j Hineq.
      intros j Hineq. hnf. cbv in H. case_eq (Hdec j) ; intros HP Heq. apply HP. cut False. intro f. contradiction.
      apply H. case_eq (j =? i) ; intro Hj_eq_i.
      + apply PeanoNat.Nat.eqb_eq in Hj_eq_i. left. clear Heq. rewrite Hj_eq_i in HP. apply HP.
      + apply PeanoNat.Nat.eqb_neq in Hj_eq_i. right. split ; auto. exists j. split. lia. split. auto. intros k Hltk Hlti. lia.
    - hnf. intro Hf. destruct Hf. hnf in H0. specialize H with i. cut False. auto. apply H0. apply H. lia.
      destruct H0. destruct H1. destruct H1. destruct H2. apply H2. apply H. lia.
  Qed.

  Lemma ltl_future_neg :
    forall (l : Run) (i : nat) (P : LTLFormula) (H : forall i' : nat, {P l i'}+{~P l i'}), l $ i |= ~F P <-> l $ i |= G (~P).
  Proof.
    intros l i P Hdec.
    split ; intro H.
    - apply ltl_general_is_forall. intro i'. specialize Hdec with i'. destruct Hdec ; auto.
      intros j Hineq.
      intro HP. apply H. case_eq (j =? i) ; intro Heq.
      + apply PeanoNat.Nat.eqb_eq in Heq. rewrite Heq in HP. left. auto.
      + apply PeanoNat.Nat.eqb_neq in Heq. right. split ; auto. exists j. split. lia. auto.
    - intro HFuture. apply H. destruct HFuture.
      + left. intro Hnot. apply Hnot. auto.
      + right. destruct H0. split ; auto. destruct H1. exists x.
        destruct H1. destruct H2. split.
        auto. split. intro Hnot. apply Hnot. auto. apply H3.
  Qed.*)
  
(*)
(* I don't want to use the excluded middle so I assume this result for now *)
Axiom ltl_general_implies_apply : forall A : Type,
  forall (l : LList A) (P : LList A -> Prop), l |= G P -> l |= P.
Global Hint Resolve ltl_general_implies_apply : ltl.

Axiom ltl_general_LNil : forall A : Type,
  forall P : LList A -> Prop, LNil |= G P.
Global Hint Resolve ltl_general_LNil : ltl.

Lemma ltl_general_unfold {A : Type} :
  forall (a : A) (l : LList A) (P : LList A -> Prop), (LCons a l) |= G P -> l |= G P.
Proof.
  intros a l P.
  assert (HF : l |= F (~ P) -> (LCons a l |= F (~ P))).
  intros. apply (ltl_future_fold a) in H. auto. intros. hnf. intros. apply HF in H0. contradiction.
Qed.
Global Hint Resolve ltl_general_unfold : ltl.
*)
  Definition ltl_weak_until (l : Run) (i : nat) (P Q : LTLFormula) : Prop :=
    l$ i |= ((G P) \/ (P U Q)).
  Notation "p 'W' q" := (fun l i => ltl_weak_until l i p q) (at level 70) : ltl_scope.

  Definition ltl_finitely_many (l : Run) (i : nat) (p : LTLFormula) : Prop :=
    l$ i |= F (G (~ p)).
  Notation "'FM' p" := (fun l i => ltl_finitely_many l i p) (at level 70) : ltl_scope.
(*)
Lemma ltl_finitely_many_unfold {A : Type} :
  forall (p : LList A -> Prop) (a : A) (l : LList A),((LCons a l) |= (FM p)) -> l |= (FM p).
Proof.
  intros.
  inversion H.
  + case_eq l ; intros.
    - rewrite H1 in H0. hnf. intros. apply ltl_general_unfold in H0. destruct H.
      left ; auto. left. auto.
    - apply ltl_general_unfold in H0. rewrite H1 in H0. left. auto.
  + case_eq l; intros ; rewrite H1 in H0 ; destruct H0 ;
      (inversion H2 ; [auto ; left ; auto | right ; split ; auto]).
Qed.

Lemma ltl_finitely_many_fold {A : Type} :
  forall (p : LList A -> Prop) (a : A) (l : LList A), (l |= (FM p)) -> (LCons a l) |= (FM p).
Proof.
  intros. apply ltl_future_fold. auto.
Qed.

Global Hint Resolve ltl_finitely_many_unfold ltl_finitely_many_fold : ltl.

Lemma ltl_finite_finitely_many {A : Type} :
  forall (p : LList A -> Prop) (l : LList A), Finite l -> (l |= FM p).
Proof.
  intros p l.
  induction 1.
  + auto with ltl.
  + destruct IHFinite.
    - right. split ; auto with ltl.
    - right. split ; auto. destruct H0. auto with ltl.
Qed.*)

  Definition ltl_infinitely_many (l : Run) (i : nat) (P : LTLFormula) : Prop :=
    l$ i |= G (F P).
  Notation "'IM' p" := (fun l i => ltl_infinitely_many l i p) (at level 70) : ltl_scope.
(*)
  Lemma ltl_infinitely_many_is_always_future :
    forall (l : Run) (i : nat) (P : LTLFormula), l $ i |= IM P <-> l $ i |= G (F P).
  Proof.
    intros l i P.
    split ; intro H.
    - intros j Hineq. apply H.
      destruct H0. apply ltl_future_neg in H0. left. auto. auto.
      right. split ; auto. destruct H0. destruct H1. destruct H1. destruct H2. exists x. split. lia. split. apply ltl_future_neg in H2. auto. auto. auto.
    - intro. apply H.
      destruct H0. apply ltl_future_neg in H0. left. auto. auto.
      right. split ; auto. destruct H0. destruct H1. destruct H1. destruct H2. exists x. split. lia. split. apply ltl_future_neg in H2. auto. auto. auto.
  Qed.*)
(*)
Lemma ltl_infinitely_many_unfold {A : Type} :
  forall (p : LList A -> Prop) (a : A) (l : LList A), ((LCons a l) |= (IM p) -> l |= (IM p)).
Proof.
  intros. hnf. intros. apply ltl_finitely_many_fold with (a := a) in H0. contradiction.
Qed.

Lemma ltl_infinitely_many_fold {A : Type} :
  forall (p : LList A -> Prop) (a : A) (l : LList A), (l |= (IM p)) -> (LCons a l) |= (IM p).
Proof.
  intros.
  hnf. intros.
  apply ltl_finitely_many_unfold in H0. contradiction.
Qed.

Global Hint Resolve ltl_infinitely_many_unfold ltl_infinitely_many_fold : ltl.
*)
End ltl.

Global Notation "l $ i |= p" := (ltl_apply l i p) (at level 80) : ltl_scope. (*
Global Notation "~ p" := (fun l i => ltl_not l i p) : ltl_scope.
Global Notation "p \/ q" := (fun l i => ltl_or l i p q) : ltl_scope.
Global Notation "p /\ q" := (fun l i => ltl_and l i p q) : ltl_scope.*)
Global Notation "p --> q" := (fun l i => ltl_impl l i p q) (at level 70) : ltl_scope.
Global Notation "'N' p" := (fun l i => ltl_now l i p) (at level 70) : ltl_scope.
Global Notation "p 'SU' q" := (fun l i => ltl_strict_until l i p q) (at level 70) : ltl_scope.
Global Notation "p 'U' q" := (fun l i => ltl_until l i p q) (at level 70) : ltl_scope.
Global Notation "'X' p" := (fun l i => ltl_next l i p) (at level 70) : ltl_scope.
Global Notation "'SF' p" := (fun l i => ltl_strict_future l i p) (at level 70) : ltl_scope.
Global Notation "'F' p" := (fun l i => ltl_future l i p) (at level 70) : ltl_scope.
Global Notation "'G' p" := (fun l i => ltl_general l i p) (at level 70) : ltl_scope.
Global Notation "p 'W' q" := (fun l i => ltl_weak_until l i p q) (at level 70) : ltl_scope.
Global Notation "'FM' p" := (fun l i => ltl_finitely_many l i p) (at level 70) : ltl_scope.
Global Notation "'IM' p" := (fun l i => ltl_infinitely_many l i p) (at level 70) : ltl_scope.
Global Hint Resolve ltl_strict_until_unfold ltl_strict_until_fold : ltl.
Global Hint Resolve ltl_next_unfold ltl_next_fold : ltl.
