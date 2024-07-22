Require Import PArray List.
Require Import Uint63 ZArith.
Require Import Lia.
Require Import Bool.

Set Implicit Arguments.

Import ListNotations.

Open Scope Z_scope.

Fixpoint size_Z (format : list int) :=
    match format with
      | [] => 0%Z
      | h::[] => to_Z h
      | h::t =>
          (to_Z h * size_Z t)%Z
    end.

Fixpoint size (format : list int) :=
    match format with
      | [] => 0%uint63
      | h::[] => h
      | h::t =>
          (h * size t)%uint63
    end.

Record MultiArray A :=
  mkMultiArray {
    format : list int;
    data : array A;
  }.

Open Scope uint63_scope.

Fixpoint build_index (format : list int) (index : list int) : option int :=
    match format, index with
      | [], [] => None
      | hf::[], hi::[] =>
          if hi <? hf then
            Some hi
          else
            None
      | hf::tf, hi::ti =>
          if hi <? hf then
            match build_index tf ti with
            | None => None
            | Some i =>
                Some (hi + hf*i)
            end
          else
            None
      | _, _ => None
    end.

Fixpoint well_formated_rec (index : list int) (format : list int) :=
    match index, format with
      | [], [] => true
      | hi::ti, hf::tf =>
          (hi <? hf)%uint63 && well_formated_rec ti tf
      | _, _ => false
    end.

Definition well_formated {A : Type} (index : list int) (arr : @MultiArray A) :=
    well_formated_rec index arr.(format).

Definition make_multiarray {A : Type} (format : list int) (a : A) :=
    mkMultiArray
      format
      (make (size format) a).

Definition set_val {A : Type} (a : A) (index : list int) (arr : @MultiArray A) :=
  match build_index arr.(format A) index with
    | None => arr
    | Some i =>
        mkMultiArray
          arr.(format A)
          arr.(data A).[ i <- a ]
  end.

Definition get_val {A : Type} (index : list int) (arr : @MultiArray A) :=
  match build_index arr.(format A) index with
    | None => None
    | Some i =>
          Some arr.(data A).[ i ]
  end.

Section MultiArray.
  Import ListNotations.

  Variable A : Type.

  Open Scope uint63_scope.
  Open Scope Z_scope.

  Remark size_Z_pos :
    forall fmt, 0 <= size_Z fmt.
  Proof.
    induction fmt.
    - simpl. lia.
    - simpl.
      assert (0 <= to_Z a < wB). apply to_Z_bounded. destruct fmt. lia. lia.
  Qed.

  Remark size_Z_is_size_for_less_than_wB :
    forall fmt,
      size_Z fmt < wB ->
      size_Z fmt = to_Z (size fmt).
  Proof.
    induction fmt.
    - intro. simpl. rewrite to_Z_0. auto.
    - intro. simpl in *.
      assert (0 <= to_Z a < wB). apply to_Z_bounded.
      assert (0 <= size_Z fmt). apply size_Z_pos.
      destruct fmt. auto.
      rewrite mul_spec.
      case_eq (to_Z a =? 0) ; intro.
      apply Z.eqb_eq in H2. rewrite Z.mod_small ; lia.
      apply Z.eqb_neq in H2. rewrite <- IHfmt.
      rewrite Z.mod_small. lia. lia. nia.
  Qed.

  Close Scope Z_scope.

  Lemma build_index_return_when_same_length :
    forall format0 index i,
      build_index format0 index = Some i ->
      length format0 = length index.
  Proof.
    induction format0.
    - intros. simpl in H. simpl.
      destruct index ; auto.
      inversion H.
    - induction index.
      + intros. simpl in H. destruct format0 ; inversion H.
      + intros.
        simpl. assert (length format0 = length index).
        simpl in H. destruct format0. destruct index.
        simpl. auto.
        destruct (a0 <? a). simpl in H ; inversion H.
        inversion H.
        destruct (a0 <? a).
        destruct (build_index (i0 :: format0) index) eqn: Heq.
        eapply IHformat0. apply Heq. inversion H. inversion H. auto.
  Qed.

  Open Scope Z_scope.

  Variable arr : @MultiArray A.
  Hypothesis arr_format_is_small : (size_Z arr.(format) < wB).
  Hypothesis arr_is_well_formated : (PArray.length arr.(data) = size arr.(format)).

  Definition fmt : list int := arr.(format).
  Lemma fmt_is_small :
    (size_Z fmt < wB).
  Proof.
    unfold fmt. auto.
  Qed.

  Lemma build_index_in_bound_if_well_formated :
    forall index i,
      build_index fmt index = Some i ->
      (i <? size fmt)%uint63 = true.
  Proof.
    intro index.
    assert (fmt_is_small : size_Z fmt < wB). apply fmt_is_small.
    revert fmt_is_small.
    revert index.
    generalize fmt as format0.
    induction format0, index ;
      try (intros ; simpl in H ; try destruct format0 ; inversion H ; fail).
    intros.
    simpl in H.
    destruct format0. destruct index.
    {
      destruct (i <? a)%uint63 eqn: Heq. inversion H. subst. simpl.
      rewrite ltb_spec in *. auto. inversion H.
    }
    {
      destruct (i <? a)%uint63.
      simpl in H ; inversion H.
      inversion H.
    }
    destruct (i <? a)%uint63 eqn: Hineq.
    destruct (build_index (i1 :: format0) index) eqn: Heq.
    assert (0 <= to_Z a < wB). apply to_Z_bounded.
    assert (0 <= to_Z i < wB). apply to_Z_bounded.
    assert (0 <= to_Z i1 < wB). apply to_Z_bounded.
    assert (0 <= to_Z i2 < wB). apply to_Z_bounded.
    assert (0 <= to_Z (size format0) < wB). apply to_Z_bounded.
    assert (0 <= size_Z format0). apply size_Z_pos.
    apply IHformat0 in Heq.
    inversion H. subst. clear H. simpl.
    simpl in Heq.
    rewrite ltb_spec in *.
    simpl in fmt_is_small0.
    destruct format0. simpl in *.
    repeat (
      rewrite mul_spec in *
      || rewrite add_spec in *
      || rewrite Z.mod_small
      || rewrite <-size_Z_is_size_for_less_than_wB) ; auto ; try nia.
    rewrite mul_spec in Heq. rewrite Z.mod_small in Heq.
    assert (0 < to_Z i1). nia.
    assert (0 < to_Z a). lia.
    assert (φ (i1) * size_Z (i0::format0) < wB). nia.
    assert (size_Z (i0::format0) < wB). nia.
    rewrite <-size_Z_is_size_for_less_than_wB in Heq ; auto.
    repeat (
      rewrite mul_spec in *
      || rewrite add_spec in *
      || rewrite Z.mod_small
      || rewrite <-size_Z_is_size_for_less_than_wB) ; auto ; try nia.
    assert (0 < to_Z a). lia.
    split. lia.
    rewrite <-size_Z_is_size_for_less_than_wB. nia.
    case_eq (to_Z i1 =? 0) ; intro.
    apply Z.eqb_eq in H6. rewrite H6 in Heq. simpl in Heq.
    rewrite Zmod_0_l in Heq. lia.
    apply Z.eqb_neq in H6.
    assert (φ (i1) * size_Z (i0::format0) < wB). nia.
    nia. simpl. simpl in fmt_is_small0. rewrite ltb_spec in Hineq. nia.
    inversion H. inversion H.
  Qed.

  Remark well_formated_rec_then_correct_index :
    forall format0,
      size_Z format0 < wB ->
    forall index,
      0 < to_Z (size format0) ->
      well_formated_rec index format0 = true ->
      build_index format0 index <> None.
  Proof.
    intros format0 H index. revert H.
    revert index.
    revert format0.
    induction format0, index ; simpl ; intros format0_is_small ; intros.
    - rewrite to_Z_0 in H. lia.
    - rewrite to_Z_0 in H. lia.
    - simpl in H0. inversion H0.
    - destruct format0. destruct index.
      destruct (i <? a)%uint63 eqn: Heq. discriminate.
      simpl in H0. inversion H0.
      destruct (i <? a)%uint63 eqn: Hineq ;
        simpl in H0 ;  inversion H0.
      destruct (i <? a)%uint63 eqn: Hineq.
      destruct (build_index (i0 :: format0) index) eqn: Heq. discriminate.
      contradict Heq. rewrite ltb_spec in Hineq.
      assert (0 <= to_Z i < wB). apply to_Z_bounded.
      assert (0 <= to_Z a < wB). apply to_Z_bounded.
      assert (0 <= to_Z (size (i0 :: format0)) < wB). apply to_Z_bounded.
      assert (size_Z (i0 :: format0) < wB). nia.
      assert (0 < to_Z a). nia.
      apply IHformat0.
      rewrite mul_spec in H. rewrite Z.mod_small in H.
      nia. split. nia. rewrite size_Z_is_size_for_less_than_wB in format0_is_small.
      lia. lia. rewrite mul_spec in H. rewrite Z.mod_small in H. lia.
      split. lia. rewrite size_Z_is_size_for_less_than_wB in format0_is_small.
      lia. auto. auto. simpl in H0. inversion H0.
    Qed.

  Remark well_formated_then_correct_index :
    forall index,
      0 < to_Z (size arr.(format)) ->
      well_formated index arr = true ->
      build_index arr.(format) index <> None.
  Proof.
    intros.
    apply well_formated_rec_then_correct_index ; auto.
  Qed.

  Lemma get_set_same :
    forall a index,
      0 < size_Z arr.(format) ->
      well_formated index arr = true ->
      get_val index (set_val a index arr) = Some a.
  Proof.
    intros.
    unfold get_val, set_val.
    destruct (build_index (format arr) index) eqn: Heq.
    simpl. rewrite Heq. rewrite get_set_same. auto.
    rewrite arr_is_well_formated.
    eapply build_index_in_bound_if_well_formated.
    apply Heq.
    contradict Heq. apply well_formated_then_correct_index ; auto.
    rewrite size_Z_is_size_for_less_than_wB in H ; auto.
  Qed.

  Lemma get_make :
    forall a index,
      0 < size_Z arr.(format) ->
      well_formated index arr = true ->
      @get_val A index (make_multiarray fmt a) = Some a.
  Proof.
    intros.
    unfold get_val, make_multiarray. simpl in *.
    destruct (build_index fmt index) eqn: Heq.
    rewrite get_make. auto.
    contradict Heq. apply well_formated_then_correct_index ; auto.
    rewrite size_Z_is_size_for_less_than_wB in H ; auto.
  Qed.

  Lemma make_is_correct_length :
    forall a : A,
      (size fmt <=? max_length)%uint63 = true ->
      PArray.length (make_multiarray fmt a).(data) = size fmt.
  Proof.
    intros.
    unfold make_multiarray.
    simpl. rewrite length_make. rewrite H. auto.
  Qed.
End MultiArray.
