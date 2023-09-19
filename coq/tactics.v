Require Export Metalib.Metatheory.
Require Export Metalib.LibTactics.
Require Export ssreflect.
Require Import Coq.Lists.List. 

(* Additional tactics for working with Metalib *)

(* destruct pairs in the hypothesis list *)
Ltac split_hyp :=
  repeat (
      match goal with
        | [ H : _ /\ _ |- _ ] => destruct H
      end).

(* eliminate explicit equalities in the hypothesis list *)
Ltac invert_equality := 
  repeat match goal with 
    | [H : (_,_) = (_,_) |- _ ] => inversion H; subst; clear H
    | [H : (_,_,_) = (_,_,_) |- _ ] => inversion H; subst; clear H
    | [H : (_,_,_,_) = (_,_,_,_) |- _ ] => inversion H; subst; clear H
    | [H : [_] ++ _ = [_] ++ _ |- _ ] => inversion H; subst; clear H
    | [H : ( _ :: _ ) = ( _ :: _ )  |- _ ] => inversion H; subst; clear H
  end.

(* specialize an IH to a fresh variable. *)
Ltac spec y := 
  let h0 := fresh in 
  repeat match goal with 
    [H0 : forall x : atom, x \notin ?L -> _ |- _ ] => 
     specialize (H0 y ltac:(auto)) 
  | [H0 : forall x : atom, x `notin` ?L -> _ |- _ ] => 
     specialize (H0 y ltac:(auto))
  | [H0 : forall x : atom, _ |- _ ] => 
     specialize (H0 y)
  | [H0 : forall x : var, _ |- _ ] => 
     specialize (H0 y)

end.

(* work with ssrbool *)
Ltac fix_bools :=
  repeat lazymatch goal with 
    | [ H : ?x <? ?y = true |- _ ] => rewrite Nat.ltb_lt in H
    | [ H : ?x <=? ?y = true |- _ ] => rewrite Nat.leb_le in H
    | [ H : ?x <? ?y = false |- _ ] => rewrite Nat.ltb_ge in H
    | [ H : ?x <=? ?y = false |- _ ] => rewrite Nat.leb_gt in H
  end.
