Require Import String Ascii HexString BinNums BinPos.
Require Import List Arith.
Import ListNotations.

Definition serialize_prefix_nat (n : nat) (s : string) : string :=
  String.concat "H" [(of_nat n); s].

Notation "s $ m" := (serialize_prefix_nat s m) (at level 70).

(* This function allows one to desarialize the concatenation of two strings *)
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

Open Scope positive_scope.

Lemma double_is_bit_shift :
  forall n, n*2 = n~0.
Proof.
  induction n.
  - simpl. rewrite IHn. auto.
  - simpl. rewrite IHn. auto.
  - simpl. auto.
Qed.

Lemma plus1_simpl_in_lt :
  forall n m, n+1 <= m -> n <= m.
Proof.
  intros.
  eapply Pos.add_le_mono in H.
  Unshelve.
  3: apply 1. 3: apply 1~0.
  rewrite Pos.add_comm in H.
  assert (n+1+1 = 2+n). rewrite Pos.add_comm.
  assert (n+1 = 1+n). rewrite Pos.add_comm. auto.
  rewrite H0. clear H0. apply Pos.add_assoc.
  rewrite H0 in H. clear H0.
  apply Pos.add_le_mono_l in H. auto.
  hnf. intro. cbv in H0. inversion H0.
Qed.

Lemma times2_simpl_in_lt :
   forall n m, n*2 <= m -> n <= m.
Proof.
  intros.
  eapply Pos.mul_le_mono in H.
  Unshelve.
  3: apply 1. 3: apply 1~0.
  rewrite Pos.mul_comm in H.
  assert (n*2*1 = 2*n). rewrite Pos.mul_comm.
  assert (n*2 = 2*n). apply Pos.mul_comm.
  rewrite H0. clear H0. apply Pos.mul_assoc.
  rewrite H0 in H. clear H0.
  apply Pos.mul_le_mono_l in H. auto.
  hnf. intro. cbv in H0. inversion H0.
Qed.

Lemma bit_shift_doesnt_affect_order :
  forall n m, n~0 <= m~1 -> n <= m.
Proof.
  intros.
  apply Pos.leb_le.
  destruct (n <=? m) eqn: Heq ; auto.
  apply Bool.not_true_iff_false in Heq.
  assert (~n <= m). intro. apply Heq. apply Pos.leb_le. auto.
  apply Pos.lt_nle in H0.
  assert (1 <= 1 + n - m - 1).
  apply Pos.le_1_l.
  rewrite Pos.add_comm in H1.
  rewrite <-Pos.sub_add_distr in H1 ; auto.
  assert (1+(m+1) <= n + 1 - (m+1) + (m+1)).
  apply Pos.add_le_mono_r. auto.
  assert (n + 1 - (m+1)+(m+1) = n+1 + (m+1) - (m+1)).
  rewrite Pos.add_comm. rewrite Pos.add_sub_assoc.
  rewrite Pos.add_comm. auto.
  apply Pos.add_lt_mono_r. auto.
  rewrite H3 in H2. clear H3.
  rewrite Pos.add_sub in H2.
  clear H1. assert (2*(1+(m+1)) <= 2*(n+1)).
  apply Pos.mul_le_mono_l. auto.
  repeat rewrite Pos.mul_add_distr_l in H1.
  assert (2*1 = 2). simpl. auto. rewrite H3 in H1. clear H3.
  rewrite Pos.add_comm in H1. apply Pos.add_le_mono_r in H1.
  assert (2*m + 1 < 2*n).
  rewrite Pos.add_1_r. apply Pos.le_succ_l.
  repeat rewrite <-Pos.add_1_r. rewrite <-Pos.add_assoc.
  assert (1+1=2). simpl. auto.
  rewrite H3. auto.
  rewrite <-double_is_bit_shift in H.
  assert (forall n, n~1 = n*2+1). intro.
  rewrite double_is_bit_shift. simpl. auto.
  rewrite H4 in H.
  rewrite Pos.mul_comm in H.
  apply Pos.lt_nle in H.
  auto. rewrite Pos.mul_comm. auto.
  apply Pos.add_lt_mono_r. auto.
Qed.

Lemma trailing0_disappear :
  forall n m, n~0 <= m~0 -> n <= m.
Proof.
  intros.
  rewrite <-double_is_bit_shift in H.
  assert (m~0 = m*2).
  rewrite <-double_is_bit_shift. auto.
  rewrite H0 in H. clear H0.
  apply Pos.mul_le_mono_r in H. auto.
Qed.

Lemma trailing1_disappear :
  forall n m, n~1 <= m~0 -> n <= m.
Proof.
  intros.
  rewrite <-double_is_bit_shift in H.
  assert (forall n, n~1 = n*2+1). intro.
  rewrite double_is_bit_shift. simpl. auto.
  rewrite H0 in H.
  apply plus1_simpl_in_lt in H.
  apply Pos.mul_le_mono_r in H. auto.
Qed.

Lemma of_pos_no_H : forall n, forall s, index 0 "H" s = None -> index 0 "H" (Raw.of_pos n s) = None.
Proof.
  assert (
      forall n n', (n' <= n)%positive -> forall s, index 0 "H" s = None -> index 0 "H" (Raw.of_pos n' s) = None
    ).
  induction n.
  - intros.
    assert (forall n, n~1 = n*2+1). intro.
    rewrite double_is_bit_shift. simpl. auto.
    assert (forall n, n~0 = n*2). intro. rewrite double_is_bit_shift. auto.
    destruct n' ; try destruct n' ; try destruct n' ; try destruct n' ; simpl ;
        try apply IHn ; try (
    repeat match goal with
      | H: _~0 <= _~1 |- _ => apply bit_shift_doesnt_affect_order in H
      | H: _~0 <= _ |- _ => rewrite H2 in H
      | H: _~1 <= _ |- _ => rewrite H1 in H
      | H: _ <= _~1 |- _ => rewrite H1 in H
      | H: _ + 1 <= _ + 1 |- _ => apply Pos.add_le_mono_r in H
      | H: _ * 2 <= _ * 2 |- _ => apply Pos.mul_le_mono_r in H
      | H: _ + 1 <= _ |- _ => apply plus1_simpl_in_lt in H
      | H: _ * 2 <= _ |- _ => apply times2_simpl_in_lt in H
      | _ => auto
    end ; simpl ; rewrite H0 ; auto).
  - intros.
    assert (forall n, n~1 = n*2+1). intro.
    rewrite double_is_bit_shift. simpl. auto.
    assert (forall n, n~0 = n*2). intro. rewrite double_is_bit_shift. auto.
     destruct n' ; try destruct n' ; try destruct n' ; try destruct n' ; simpl ;
        try apply IHn ; try (
    repeat match goal with
      | H: _~0 <= _~1 |- _ => apply bit_shift_doesnt_affect_order in H
      | H: _~0 <= _~0 |- _ => apply trailing0_disappear in H
      | H: _~1 <= _~0 |- _ => apply trailing1_disappear in H
      | H: _~0 <= _ |- _ => rewrite H2 in H
      | H: _~1 <= _ |- _ => rewrite H1 in H
      | H: _ <= _~1 |- _ => rewrite H1 in H
      | H: _ + 1 <= _ + 1 |- _ => apply Pos.add_le_mono_r in H
      | H: _ * 2 <= _ * 2 |- _ => apply Pos.mul_le_mono_r in H
      | H: _ + 1 <= _ |- _ => apply plus1_simpl_in_lt in H
      | H: _ * 2 <= _ |- _ => apply times2_simpl_in_lt in H
      | _ => auto
    end ; simpl ; rewrite H0 ; auto).
  - intros.
    destruct (Pos.eq_dec n' 1).
    subst. simpl. rewrite H0. auto.
    contradict n.
    apply Pos.le_antisym.
    auto. apply Pos.le_1_l.
  - intros. eapply H.
    apply Pos.le_refl.
    auto.
Qed.

Lemma of_N_no_H : forall n, index 0 "H" (of_N n) = None.
Proof.
  intro. destruct n. auto. simpl.
  rewrite of_pos_no_H ; auto.
Qed.

Lemma of_nat_no_H : forall n : nat, index 0 "H" (of_nat n) = None.
Proof.
  intro. unfold of_nat. rewrite of_N_no_H. auto.
Qed.

Definition deserialize_prefix_nat (s : string) : nat*string :=
  let (n_enc, s') := cut_on_H s in
  let n := to_nat n_enc in
  (n, s').

Lemma deserialize_serialize_prefix_nat :
  forall n : nat, forall s : string, deserialize_prefix_nat (n$s) = (n, s).
Proof.
  intros.
  unfold deserialize_prefix_nat, serialize_prefix_nat.
  simpl. repeat rewrite cut_on_H_cut_on_first_H.
  - rewrite to_nat_of_nat. auto.
  - apply of_nat_no_H.
Qed.
