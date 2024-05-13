Require Import Arith.
Require Import Nat.
Require Import Bool.

Ltac intro_forall :=
    match goal with
      | [|- forall _, _ -> _] =>
          let n := fresh "n" in
          intro n
    end.

Ltac simpl_match :=
    match goal with
      | [|- context [
               match ?cond with
                 | _ => _
               end
      ]] =>
          let H := fresh "H" in
          let n := fresh "n" in
          case_eq cond ; intro_forall || idtac ; intro H ; rewrite H in * || idtac ; simpl
      | [H : context [
                 match ?cond with
                 | _ => _
                 end
      ] |- _] =>
          let H0 := fresh "H" in
          let n := fresh "n" in
          case_eq cond ; intro_forall || idtac ; intro H0 ; rewrite H0 in * ; simpl in H
    end.

Ltac get_term_head term :=
    match term with
      | ?id _ => get_term_head id
      | ?id => id
    end.

Ltac simpl_arith_bool :=
    match goal with
      | [H : context [
                 (_ =? _) = true
               ] |- _] =>
          apply PeanoNat.Nat.eqb_eq in H
      | [H : context [
                 (_ =? _) = false
               ] |- _] =>
          apply PeanoNat.Nat.eqb_neq in H
      | [H : context [
                 (_ <? _) = true
               ] |- _] =>
          apply PeanoNat.Nat.ltb_lt in H
      | [H : context [
                 (_ <? _) = false
                ] |- _] =>
          apply PeanoNat.Nat.ltb_ge in H
      | [H : context [
                 (_ <=? _) = true
                ] |- _] =>
          apply PeanoNat.Nat.leb_le in H
      | [H : context [
                 (_ <=? _) = false
                ] |- _] =>
          apply PeanoNat.Nat.leb_gt in H
      | [H : context [
                 (_ && _) = true
                ] |- _] =>
          apply andb_true_iff in H ; destruct H
      | [H : context [
                 (_ && _) = false
                ] |- _] =>
          apply andb_false_iff in H ; destruct H
      | [H : context [
                 (_ || _) = true
                ] |- _] =>
          apply orb_true_iff in H ; destruct H
      | [H : context [
                 (_ || _) = false
                ] |- _] =>
          apply orb_false_iff in H ; destruct H
      | [|- (_ =? _) = true] =>
          apply PeanoNat.Nat.eqb_eq
      | [|- (_ =? _) = false] =>
          apply PeanoNat.Nat.eqb_neq
      | [|- (_ <? _) = true] =>
          apply PeanoNat.Nat.ltb_lt
      | [|- (_ <? _) = false] =>
          apply PeanoNat.Nat.ltb_ge
      | [|- (_ <=? _) = true] =>
          apply PeanoNat.Nat.leb_le
      | [|- (_ <=? _) = false] =>
          apply PeanoNat.Nat.leb_gt
      | [|- (_ && _) = true] =>
          apply andb_true_iff ; split
      | [|- (_ && _) = false] =>
          apply andb_false_iff
      | [|- (_ || _) = true] =>
          apply orb_true_iff
      | [|- (_ || _) = false] =>
          apply orb_false_iff ; split
   end.

  Ltac create_sig typ a out :=
    let typ' := eval unfold typ in typ in
    match typ' with
      | sig ?P =>
          let H := fresh "H" in
          assert (H : P a) ; [
              auto |
              pose (exist P a H) as out
            ]
    end.
