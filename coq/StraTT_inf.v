Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export StraTT_ott.

Local Set Warnings "-non-recursive". 

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme tm_ind' := Induction for tm Sort Prop.

Combined Scheme tm_mutind from tm_ind'.

Scheme tm_rec' := Induction for tm Sort Set.

Combined Scheme tm_mutrec from tm_rec'.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_tm_wrt_tm_rec (n1 : nat) (x1 : var) (A1 : tm) {struct A1} : tm :=
  match A1 with
    | a_Type => a_Type
    | a_Arrow A2 B1 => a_Arrow (close_tm_wrt_tm_rec n1 x1 A2) (close_tm_wrt_tm_rec n1 x1 B1)
    | a_Pi A2 j1 B1 => a_Pi (close_tm_wrt_tm_rec n1 x1 A2) j1 (close_tm_wrt_tm_rec (S n1) x1 B1)
    | a_Abs a1 => a_Abs (close_tm_wrt_tm_rec (S n1) x1 a1)
    | a_App a1 b1 => a_App (close_tm_wrt_tm_rec n1 x1 a1) (close_tm_wrt_tm_rec n1 x1 b1)
    | a_Bottom => a_Bottom
    | a_Absurd b1 => a_Absurd (close_tm_wrt_tm_rec n1 x1 b1)
    | a_Var_f x2 => if (x1 == x2) then (a_Var_b n1) else (a_Var_f x2)
    | a_Var_b n2 => if (lt_ge_dec n2 n1) then (a_Var_b n2) else (a_Var_b (S n2))
    | a_Const x2 i1 => a_Const x2 i1
  end.

Definition close_tm_wrt_tm x1 A1 := close_tm_wrt_tm_rec 0 x1 A1.


(* *********************************************************************** *)
(** * Size *)

Definition size_nat (i1 : nat) : nat := 1
.

Fixpoint size_tm (A1 : tm) {struct A1} : nat :=
  match A1 with
    | a_Type => 1
    | a_Arrow A2 B1 => 1 + (size_tm A2) + (size_tm B1)
    | a_Pi A2 j1 B1 => 1 + (size_tm A2) + (size_nat j1) + (size_tm B1)
    | a_Abs a1 => 1 + (size_tm a1)
    | a_App a1 b1 => 1 + (size_tm a1) + (size_tm b1)
    | a_Bottom => 1
    | a_Absurd b1 => 1 + (size_tm b1)
    | a_Var_f x1 => 1
    | a_Var_b n1 => 1
    | a_Const x1 i1 => 1 + (size_nat i1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_tm_wrt_tm : nat -> tm -> Prop :=
  | degree_wrt_tm_a_Type : forall n1,
    degree_tm_wrt_tm n1 (a_Type)
  | degree_wrt_tm_a_Arrow : forall n1 A1 B1,
    degree_tm_wrt_tm n1 A1 ->
    degree_tm_wrt_tm n1 B1 ->
    degree_tm_wrt_tm n1 (a_Arrow A1 B1)
  | degree_wrt_tm_a_Pi : forall n1 A1 j1 B1,
    degree_tm_wrt_tm n1 A1 ->
    degree_tm_wrt_tm (S n1) B1 ->
    degree_tm_wrt_tm n1 (a_Pi A1 j1 B1)
  | degree_wrt_tm_a_Abs : forall n1 a1,
    degree_tm_wrt_tm (S n1) a1 ->
    degree_tm_wrt_tm n1 (a_Abs a1)
  | degree_wrt_tm_a_App : forall n1 a1 b1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 b1 ->
    degree_tm_wrt_tm n1 (a_App a1 b1)
  | degree_wrt_tm_a_Bottom : forall n1,
    degree_tm_wrt_tm n1 (a_Bottom)
  | degree_wrt_tm_a_Absurd : forall n1 b1,
    degree_tm_wrt_tm n1 b1 ->
    degree_tm_wrt_tm n1 (a_Absurd b1)
  | degree_wrt_tm_a_Var_f : forall n1 x1,
    degree_tm_wrt_tm n1 (a_Var_f x1)
  | degree_wrt_tm_a_Var_b : forall n1 n2,
    lt n2 n1 ->
    degree_tm_wrt_tm n1 (a_Var_b n2)
  | degree_wrt_tm_a_Const : forall n1 x1 i1,
    degree_tm_wrt_tm n1 (a_Const x1 i1).

Scheme degree_tm_wrt_tm_ind' := Induction for degree_tm_wrt_tm Sort Prop.

Combined Scheme degree_tm_wrt_tm_mutind from degree_tm_wrt_tm_ind'.

#[export] Hint Constructors degree_tm_wrt_tm : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_tm : tm -> Set :=
  | lc_set_a_Type :
    lc_set_tm (a_Type)
  | lc_set_a_Arrow : forall A1 B1,
    lc_set_tm A1 ->
    lc_set_tm B1 ->
    lc_set_tm (a_Arrow A1 B1)
  | lc_set_a_Pi : forall A1 j1 B1,
    lc_set_tm A1 ->
    (forall x1 : var, lc_set_tm (open_tm_wrt_tm B1 (a_Var_f x1))) ->
    lc_set_tm (a_Pi A1 j1 B1)
  | lc_set_a_Abs : forall a1,
    (forall x1 : var, lc_set_tm (open_tm_wrt_tm a1 (a_Var_f x1))) ->
    lc_set_tm (a_Abs a1)
  | lc_set_a_App : forall a1 b1,
    lc_set_tm a1 ->
    lc_set_tm b1 ->
    lc_set_tm (a_App a1 b1)
  | lc_set_a_Bottom :
    lc_set_tm (a_Bottom)
  | lc_set_a_Absurd : forall b1,
    lc_set_tm b1 ->
    lc_set_tm (a_Absurd b1)
  | lc_set_a_Var_f : forall x1,
    lc_set_tm (a_Var_f x1)
  | lc_set_a_Const : forall x1 i1,
    lc_set_tm (a_Const x1 i1).

Scheme lc_tm_ind' := Induction for lc_tm Sort Prop.

Combined Scheme lc_tm_mutind from lc_tm_ind'.

Scheme lc_set_tm_ind' := Induction for lc_set_tm Sort Prop.

Combined Scheme lc_set_tm_mutind from lc_set_tm_ind'.

Scheme lc_set_tm_rec' := Induction for lc_set_tm Sort Set.

Combined Scheme lc_set_tm_mutrec from lc_set_tm_rec'.

#[export] Hint Constructors lc_tm : core lngen.

#[export] Hint Constructors lc_set_tm : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_tm_wrt_tm A1 := forall x1, lc_tm (open_tm_wrt_tm A1 (a_Var_f x1)).

#[export] Hint Unfold body_tm_wrt_tm : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

#[export] Hint Resolve Nat.add_le_mono : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_nat_min_mutual :
(forall i1, 1 <= size_nat i1).
Proof.
default_simp.
Qed.

(* end hide *)

Lemma size_nat_min :
forall i1, 1 <= size_nat i1.
Proof.
pose proof size_nat_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_nat_min : lngen.

(* begin hide *)

Lemma size_tm_min_mutual :
(forall A1, 1 <= size_tm A1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_tm_min :
forall A1, 1 <= size_tm A1.
Proof.
pose proof size_tm_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_tm_min : lngen.

(* begin hide *)

Lemma size_tm_close_tm_wrt_tm_rec_mutual :
(forall A1 x1 n1,
  size_tm (close_tm_wrt_tm_rec n1 x1 A1) = size_tm A1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_tm_close_tm_wrt_tm_rec :
forall A1 x1 n1,
  size_tm (close_tm_wrt_tm_rec n1 x1 A1) = size_tm A1.
Proof.
pose proof size_tm_close_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_tm_close_tm_wrt_tm_rec : lngen.
#[export] Hint Rewrite size_tm_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_tm_close_tm_wrt_tm :
forall A1 x1,
  size_tm (close_tm_wrt_tm x1 A1) = size_tm A1.
Proof.
unfold close_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve size_tm_close_tm_wrt_tm : lngen.
#[export] Hint Rewrite size_tm_close_tm_wrt_tm using solve [auto] : lngen.

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec_mutual :
(forall A1 A2 n1,
  size_tm A1 <= size_tm (open_tm_wrt_tm_rec n1 A2 A1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec :
forall A1 A2 n1,
  size_tm A1 <= size_tm (open_tm_wrt_tm_rec n1 A2 A1).
Proof.
pose proof size_tm_open_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

Lemma size_tm_open_tm_wrt_tm :
forall A1 A2,
  size_tm A1 <= size_tm (open_tm_wrt_tm A1 A2).
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve size_tm_open_tm_wrt_tm : lngen.

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec_var_mutual :
(forall A1 x1 n1,
  size_tm (open_tm_wrt_tm_rec n1 (a_Var_f x1) A1) = size_tm A1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec_var :
forall A1 x1 n1,
  size_tm (open_tm_wrt_tm_rec n1 (a_Var_f x1) A1) = size_tm A1.
Proof.
pose proof size_tm_open_tm_wrt_tm_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_tm_open_tm_wrt_tm_rec_var : lngen.
#[export] Hint Rewrite size_tm_open_tm_wrt_tm_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_tm_open_tm_wrt_tm_var :
forall A1 x1,
  size_tm (open_tm_wrt_tm A1 (a_Var_f x1)) = size_tm A1.
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve size_tm_open_tm_wrt_tm_var : lngen.
#[export] Hint Rewrite size_tm_open_tm_wrt_tm_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_tm_wrt_tm_S_mutual :
(forall n1 A1,
  degree_tm_wrt_tm n1 A1 ->
  degree_tm_wrt_tm (S n1) A1).
Proof.
apply_mutual_ind degree_tm_wrt_tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_tm_wrt_tm_S :
forall n1 A1,
  degree_tm_wrt_tm n1 A1 ->
  degree_tm_wrt_tm (S n1) A1.
Proof.
pose proof degree_tm_wrt_tm_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_S : lngen.

Lemma degree_tm_wrt_tm_O :
forall n1 A1,
  degree_tm_wrt_tm O A1 ->
  degree_tm_wrt_tm n1 A1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_O : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec_mutual :
(forall A1 x1 n1,
  degree_tm_wrt_tm n1 A1 ->
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 A1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec :
forall A1 x1 n1,
  degree_tm_wrt_tm n1 A1 ->
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 A1).
Proof.
pose proof degree_tm_wrt_tm_close_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_close_tm_wrt_tm_rec : lngen.

(* end hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm :
forall A1 x1,
  degree_tm_wrt_tm 0 A1 ->
  degree_tm_wrt_tm 1 (close_tm_wrt_tm x1 A1).
Proof.
unfold close_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_close_tm_wrt_tm : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv_mutual :
(forall A1 x1 n1,
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 A1) ->
  degree_tm_wrt_tm n1 A1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv :
forall A1 x1 n1,
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 A1) ->
  degree_tm_wrt_tm n1 A1.
Proof.
pose proof degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_inv :
forall A1 x1,
  degree_tm_wrt_tm 1 (close_tm_wrt_tm x1 A1) ->
  degree_tm_wrt_tm 0 A1.
Proof.
unfold close_tm_wrt_tm; eauto with lngen.
Qed.

#[export] Hint Immediate degree_tm_wrt_tm_close_tm_wrt_tm_inv : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec_mutual :
(forall A1 A2 n1,
  degree_tm_wrt_tm (S n1) A1 ->
  degree_tm_wrt_tm n1 A2 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 A2 A1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec :
forall A1 A2 n1,
  degree_tm_wrt_tm (S n1) A1 ->
  degree_tm_wrt_tm n1 A2 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 A2 A1).
Proof.
pose proof degree_tm_wrt_tm_open_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm :
forall A1 A2,
  degree_tm_wrt_tm 1 A1 ->
  degree_tm_wrt_tm 0 A2 ->
  degree_tm_wrt_tm 0 (open_tm_wrt_tm A1 A2).
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_open_tm_wrt_tm : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv_mutual :
(forall A1 A2 n1,
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 A2 A1) ->
  degree_tm_wrt_tm (S n1) A1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv :
forall A1 A2 n1,
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 A2 A1) ->
  degree_tm_wrt_tm (S n1) A1.
Proof.
pose proof degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_inv :
forall A1 A2,
  degree_tm_wrt_tm 0 (open_tm_wrt_tm A1 A2) ->
  degree_tm_wrt_tm 1 A1.
Proof.
unfold open_tm_wrt_tm; eauto with lngen.
Qed.

#[export] Hint Immediate degree_tm_wrt_tm_open_tm_wrt_tm_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_tm_wrt_tm_rec_inj_mutual :
(forall A1 A2 x1 n1,
  close_tm_wrt_tm_rec n1 x1 A1 = close_tm_wrt_tm_rec n1 x1 A2 ->
  A1 = A2).
Proof.
apply_mutual_ind tm_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_inj :
forall A1 A2 x1 n1,
  close_tm_wrt_tm_rec n1 x1 A1 = close_tm_wrt_tm_rec n1 x1 A2 ->
  A1 = A2.
Proof.
pose proof close_tm_wrt_tm_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_tm_wrt_tm_rec_inj : lngen.

(* end hide *)

Lemma close_tm_wrt_tm_inj :
forall A1 A2 x1,
  close_tm_wrt_tm x1 A1 = close_tm_wrt_tm x1 A2 ->
  A1 = A2.
Proof.
unfold close_tm_wrt_tm; eauto with lngen.
Qed.

#[export] Hint Immediate close_tm_wrt_tm_inj : lngen.

(* begin hide *)

Lemma close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_mutual :
(forall A1 x1 n1,
  x1 `notin` fv_tm A1 ->
  close_tm_wrt_tm_rec n1 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x1) A1) = A1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_open_tm_wrt_tm_rec :
forall A1 x1 n1,
  x1 `notin` fv_tm A1 ->
  close_tm_wrt_tm_rec n1 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x1) A1) = A1.
Proof.
pose proof close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_tm_wrt_tm_rec_open_tm_wrt_tm_rec : lngen.
#[export] Hint Rewrite close_tm_wrt_tm_rec_open_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_tm_wrt_tm_open_tm_wrt_tm :
forall A1 x1,
  x1 `notin` fv_tm A1 ->
  close_tm_wrt_tm x1 (open_tm_wrt_tm A1 (a_Var_f x1)) = A1.
Proof.
unfold close_tm_wrt_tm; unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve close_tm_wrt_tm_open_tm_wrt_tm : lngen.
#[export] Hint Rewrite close_tm_wrt_tm_open_tm_wrt_tm using solve [auto] : lngen.

(* begin hide *)

Lemma open_tm_wrt_tm_rec_close_tm_wrt_tm_rec_mutual :
(forall A1 x1 n1,
  open_tm_wrt_tm_rec n1 (a_Var_f x1) (close_tm_wrt_tm_rec n1 x1 A1) = A1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_close_tm_wrt_tm_rec :
forall A1 x1 n1,
  open_tm_wrt_tm_rec n1 (a_Var_f x1) (close_tm_wrt_tm_rec n1 x1 A1) = A1.
Proof.
pose proof open_tm_wrt_tm_rec_close_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_tm_wrt_tm_rec_close_tm_wrt_tm_rec : lngen.
#[export] Hint Rewrite open_tm_wrt_tm_rec_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_tm_wrt_tm_close_tm_wrt_tm :
forall A1 x1,
  open_tm_wrt_tm (close_tm_wrt_tm x1 A1) (a_Var_f x1) = A1.
Proof.
unfold close_tm_wrt_tm; unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve open_tm_wrt_tm_close_tm_wrt_tm : lngen.
#[export] Hint Rewrite open_tm_wrt_tm_close_tm_wrt_tm using solve [auto] : lngen.

(* begin hide *)

Lemma open_tm_wrt_tm_rec_inj_mutual :
(forall A2 A1 x1 n1,
  x1 `notin` fv_tm A2 ->
  x1 `notin` fv_tm A1 ->
  open_tm_wrt_tm_rec n1 (a_Var_f x1) A2 = open_tm_wrt_tm_rec n1 (a_Var_f x1) A1 ->
  A2 = A1).
Proof.
apply_mutual_ind tm_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_inj :
forall A2 A1 x1 n1,
  x1 `notin` fv_tm A2 ->
  x1 `notin` fv_tm A1 ->
  open_tm_wrt_tm_rec n1 (a_Var_f x1) A2 = open_tm_wrt_tm_rec n1 (a_Var_f x1) A1 ->
  A2 = A1.
Proof.
pose proof open_tm_wrt_tm_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_tm_wrt_tm_rec_inj : lngen.

(* end hide *)

Lemma open_tm_wrt_tm_inj :
forall A2 A1 x1,
  x1 `notin` fv_tm A2 ->
  x1 `notin` fv_tm A1 ->
  open_tm_wrt_tm A2 (a_Var_f x1) = open_tm_wrt_tm A1 (a_Var_f x1) ->
  A2 = A1.
Proof.
unfold open_tm_wrt_tm; eauto with lngen.
Qed.

#[export] Hint Immediate open_tm_wrt_tm_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_of_lc_tm_mutual :
(forall A1,
  lc_tm A1 ->
  degree_tm_wrt_tm 0 A1).
Proof.
apply_mutual_ind lc_tm_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_tm_wrt_tm_of_lc_tm :
forall A1,
  lc_tm A1 ->
  degree_tm_wrt_tm 0 A1.
Proof.
pose proof degree_tm_wrt_tm_of_lc_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_tm_wrt_tm_of_lc_tm : lngen.

(* begin hide *)

Lemma lc_tm_of_degree_size_mutual :
forall i1,
(forall A1,
  size_tm A1 = i1 ->
  degree_tm_wrt_tm 0 A1 ->
  lc_tm A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind tm_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_tm_of_degree :
forall A1,
  degree_tm_wrt_tm 0 A1 ->
  lc_tm A1.
Proof.
intros A1; intros;
pose proof (lc_tm_of_degree_size_mutual (size_tm A1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_tm_of_degree : lngen.

Ltac nat_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac tm_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_tm_wrt_tm_of_lc_tm in J1; clear H
          end).

Lemma lc_a_Pi_exists :
forall x1 A1 j1 B1,
  lc_tm A1 ->
  lc_tm (open_tm_wrt_tm B1 (a_Var_f x1)) ->
  lc_tm (a_Pi A1 j1 B1).
Proof.
intros; tm_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_a_Abs_exists :
forall x1 a1,
  lc_tm (open_tm_wrt_tm a1 (a_Var_f x1)) ->
  lc_tm (a_Abs a1).
Proof.
intros; tm_lc_exists_tac; eauto 6 with lngen.
Qed.

#[export] Hint Extern 1 (lc_tm (a_Pi _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_Pi_exists x1) : core.

#[export] Hint Extern 1 (lc_tm (a_Abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_Abs_exists x1) : core.

Lemma lc_body_tm_wrt_tm :
forall A1 A2,
  body_tm_wrt_tm A1 ->
  lc_tm A2 ->
  lc_tm (open_tm_wrt_tm A1 A2).
Proof.
unfold body_tm_wrt_tm;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
tm_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_tm_wrt_tm : lngen.

Lemma lc_body_a_Pi_3 :
forall A1 j1 B1,
  lc_tm (a_Pi A1 j1 B1) ->
  body_tm_wrt_tm B1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_a_Pi_3 : lngen.

Lemma lc_body_a_Abs_1 :
forall a1,
  lc_tm (a_Abs a1) ->
  body_tm_wrt_tm a1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_a_Abs_1 : lngen.

(* begin hide *)

Lemma lc_tm_unique_mutual :
(forall A1 (proof2 proof3 : lc_tm A1), proof2 = proof3).
Proof.
apply_mutual_ind lc_tm_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_tm_unique :
forall A1 (proof2 proof3 : lc_tm A1), proof2 = proof3.
Proof.
pose proof lc_tm_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_tm_unique : lngen.

(* begin hide *)

Lemma lc_tm_of_lc_set_tm_mutual :
(forall A1, lc_set_tm A1 -> lc_tm A1).
Proof.
apply_mutual_ind lc_set_tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_tm_of_lc_set_tm :
forall A1, lc_set_tm A1 -> lc_tm A1.
Proof.
pose proof lc_tm_of_lc_set_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_tm_of_lc_set_tm : lngen.

(* begin hide *)

Lemma lc_set_tm_of_lc_tm_size_mutual :
forall i1,
(forall A1,
  size_tm A1 = i1 ->
  lc_tm A1 ->
  lc_set_tm A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind tm_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_tm_of_lc_tm
 | apply lc_set_nat_of_lc_nat];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_tm_of_lc_tm :
forall A1,
  lc_tm A1 ->
  lc_set_tm A1.
Proof.
intros A1; intros;
pose proof (lc_set_tm_of_lc_tm_size_mutual (size_tm A1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_tm_of_lc_tm : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_tm_wrt_tm_rec_degree_tm_wrt_tm_mutual :
(forall A1 x1 n1,
  degree_tm_wrt_tm n1 A1 ->
  x1 `notin` fv_tm A1 ->
  close_tm_wrt_tm_rec n1 x1 A1 = A1).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_degree_tm_wrt_tm :
forall A1 x1 n1,
  degree_tm_wrt_tm n1 A1 ->
  x1 `notin` fv_tm A1 ->
  close_tm_wrt_tm_rec n1 x1 A1 = A1.
Proof.
pose proof close_tm_wrt_tm_rec_degree_tm_wrt_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_tm_wrt_tm_rec_degree_tm_wrt_tm : lngen.
#[export] Hint Rewrite close_tm_wrt_tm_rec_degree_tm_wrt_tm using solve [auto] : lngen.

(* end hide *)

Lemma close_tm_wrt_tm_lc_tm :
forall A1 x1,
  lc_tm A1 ->
  x1 `notin` fv_tm A1 ->
  close_tm_wrt_tm x1 A1 = A1.
Proof.
unfold close_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve close_tm_wrt_tm_lc_tm : lngen.
#[export] Hint Rewrite close_tm_wrt_tm_lc_tm using solve [auto] : lngen.

(* begin hide *)

Lemma open_tm_wrt_tm_rec_degree_tm_wrt_tm_mutual :
(forall A2 A1 n1,
  degree_tm_wrt_tm n1 A2 ->
  open_tm_wrt_tm_rec n1 A1 A2 = A2).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_degree_tm_wrt_tm :
forall A2 A1 n1,
  degree_tm_wrt_tm n1 A2 ->
  open_tm_wrt_tm_rec n1 A1 A2 = A2.
Proof.
pose proof open_tm_wrt_tm_rec_degree_tm_wrt_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_tm_wrt_tm_rec_degree_tm_wrt_tm : lngen.
#[export] Hint Rewrite open_tm_wrt_tm_rec_degree_tm_wrt_tm using solve [auto] : lngen.

(* end hide *)

Lemma open_tm_wrt_tm_lc_tm :
forall A2 A1,
  lc_tm A2 ->
  open_tm_wrt_tm A2 A1 = A2.
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve open_tm_wrt_tm_lc_tm : lngen.
#[export] Hint Rewrite open_tm_wrt_tm_lc_tm using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_tm_close_tm_wrt_tm_rec_mutual :
(forall A1 x1 n1,
  fv_tm (close_tm_wrt_tm_rec n1 x1 A1) [=] remove x1 (fv_tm A1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_tm_close_tm_wrt_tm_rec :
forall A1 x1 n1,
  fv_tm (close_tm_wrt_tm_rec n1 x1 A1) [=] remove x1 (fv_tm A1).
Proof.
pose proof fv_tm_close_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_close_tm_wrt_tm_rec : lngen.
#[export] Hint Rewrite fv_tm_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_tm_close_tm_wrt_tm :
forall A1 x1,
  fv_tm (close_tm_wrt_tm x1 A1) [=] remove x1 (fv_tm A1).
Proof.
unfold close_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve fv_tm_close_tm_wrt_tm : lngen.
#[export] Hint Rewrite fv_tm_close_tm_wrt_tm using solve [auto] : lngen.

(* begin hide *)

Lemma fv_tm_open_tm_wrt_tm_rec_lower_mutual :
(forall A1 A2 n1,
  fv_tm A1 [<=] fv_tm (open_tm_wrt_tm_rec n1 A2 A1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_tm_open_tm_wrt_tm_rec_lower :
forall A1 A2 n1,
  fv_tm A1 [<=] fv_tm (open_tm_wrt_tm_rec n1 A2 A1).
Proof.
pose proof fv_tm_open_tm_wrt_tm_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_open_tm_wrt_tm_rec_lower : lngen.

(* end hide *)

Lemma fv_tm_open_tm_wrt_tm_lower :
forall A1 A2,
  fv_tm A1 [<=] fv_tm (open_tm_wrt_tm A1 A2).
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve fv_tm_open_tm_wrt_tm_lower : lngen.

(* begin hide *)

Lemma fv_tm_open_tm_wrt_tm_rec_upper_mutual :
(forall A1 A2 n1,
  fv_tm (open_tm_wrt_tm_rec n1 A2 A1) [<=] fv_tm A2 `union` fv_tm A1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_tm_open_tm_wrt_tm_rec_upper :
forall A1 A2 n1,
  fv_tm (open_tm_wrt_tm_rec n1 A2 A1) [<=] fv_tm A2 `union` fv_tm A1.
Proof.
pose proof fv_tm_open_tm_wrt_tm_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_open_tm_wrt_tm_rec_upper : lngen.

(* end hide *)

Lemma fv_tm_open_tm_wrt_tm_upper :
forall A1 A2,
  fv_tm (open_tm_wrt_tm A1 A2) [<=] fv_tm A2 `union` fv_tm A1.
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve fv_tm_open_tm_wrt_tm_upper : lngen.

(* begin hide *)

Lemma fv_tm_subst_tm_fresh_mutual :
(forall A1 A2 x1,
  x1 `notin` fv_tm A1 ->
  fv_tm (subst_tm A2 x1 A1) [=] fv_tm A1).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_tm_subst_tm_fresh :
forall A1 A2 x1,
  x1 `notin` fv_tm A1 ->
  fv_tm (subst_tm A2 x1 A1) [=] fv_tm A1.
Proof.
pose proof fv_tm_subst_tm_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_subst_tm_fresh : lngen.
#[export] Hint Rewrite fv_tm_subst_tm_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_tm_subst_tm_lower_mutual :
(forall A1 A2 x1,
  remove x1 (fv_tm A1) [<=] fv_tm (subst_tm A2 x1 A1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_tm_subst_tm_lower :
forall A1 A2 x1,
  remove x1 (fv_tm A1) [<=] fv_tm (subst_tm A2 x1 A1).
Proof.
pose proof fv_tm_subst_tm_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_subst_tm_lower : lngen.

(* begin hide *)

Lemma fv_tm_subst_tm_notin_mutual :
(forall A1 A2 x1 x2,
  x2 `notin` fv_tm A1 ->
  x2 `notin` fv_tm A2 ->
  x2 `notin` fv_tm (subst_tm A2 x1 A1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_tm_subst_tm_notin :
forall A1 A2 x1 x2,
  x2 `notin` fv_tm A1 ->
  x2 `notin` fv_tm A2 ->
  x2 `notin` fv_tm (subst_tm A2 x1 A1).
Proof.
pose proof fv_tm_subst_tm_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_subst_tm_notin : lngen.

(* begin hide *)

Lemma fv_tm_subst_tm_upper_mutual :
(forall A1 A2 x1,
  fv_tm (subst_tm A2 x1 A1) [<=] fv_tm A2 `union` remove x1 (fv_tm A1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_tm_subst_tm_upper :
forall A1 A2 x1,
  fv_tm (subst_tm A2 x1 A1) [<=] fv_tm A2 `union` remove x1 (fv_tm A1).
Proof.
pose proof fv_tm_subst_tm_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_tm_subst_tm_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_tm_close_tm_wrt_tm_rec_mutual :
(forall A2 A1 x1 x2 n1,
  degree_tm_wrt_tm n1 A1 ->
  x1 <> x2 ->
  x2 `notin` fv_tm A1 ->
  subst_tm A1 x1 (close_tm_wrt_tm_rec n1 x2 A2) = close_tm_wrt_tm_rec n1 x2 (subst_tm A1 x1 A2)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_close_tm_wrt_tm_rec :
forall A2 A1 x1 x2 n1,
  degree_tm_wrt_tm n1 A1 ->
  x1 <> x2 ->
  x2 `notin` fv_tm A1 ->
  subst_tm A1 x1 (close_tm_wrt_tm_rec n1 x2 A2) = close_tm_wrt_tm_rec n1 x2 (subst_tm A1 x1 A2).
Proof.
pose proof subst_tm_close_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_close_tm_wrt_tm_rec : lngen.

Lemma subst_tm_close_tm_wrt_tm :
forall A2 A1 x1 x2,
  lc_tm A1 ->  x1 <> x2 ->
  x2 `notin` fv_tm A1 ->
  subst_tm A1 x1 (close_tm_wrt_tm x2 A2) = close_tm_wrt_tm x2 (subst_tm A1 x1 A2).
Proof.
unfold close_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve subst_tm_close_tm_wrt_tm : lngen.

(* begin hide *)

Lemma subst_tm_degree_tm_wrt_tm_mutual :
(forall A1 A2 x1 n1,
  degree_tm_wrt_tm n1 A1 ->
  degree_tm_wrt_tm n1 A2 ->
  degree_tm_wrt_tm n1 (subst_tm A2 x1 A1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_degree_tm_wrt_tm :
forall A1 A2 x1 n1,
  degree_tm_wrt_tm n1 A1 ->
  degree_tm_wrt_tm n1 A2 ->
  degree_tm_wrt_tm n1 (subst_tm A2 x1 A1).
Proof.
pose proof subst_tm_degree_tm_wrt_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_degree_tm_wrt_tm : lngen.

(* begin hide *)

Lemma subst_tm_fresh_eq_mutual :
(forall A2 A1 x1,
  x1 `notin` fv_tm A2 ->
  subst_tm A1 x1 A2 = A2).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_fresh_eq :
forall A2 A1 x1,
  x1 `notin` fv_tm A2 ->
  subst_tm A1 x1 A2 = A2.
Proof.
pose proof subst_tm_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_fresh_eq : lngen.
#[export] Hint Rewrite subst_tm_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tm_fresh_same_mutual :
(forall A2 A1 x1,
  x1 `notin` fv_tm A1 ->
  x1 `notin` fv_tm (subst_tm A1 x1 A2)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_fresh_same :
forall A2 A1 x1,
  x1 `notin` fv_tm A1 ->
  x1 `notin` fv_tm (subst_tm A1 x1 A2).
Proof.
pose proof subst_tm_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_fresh_same : lngen.

(* begin hide *)

Lemma subst_tm_fresh_mutual :
(forall A2 A1 x1 x2,
  x1 `notin` fv_tm A2 ->
  x1 `notin` fv_tm A1 ->
  x1 `notin` fv_tm (subst_tm A1 x2 A2)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_fresh :
forall A2 A1 x1 x2,
  x1 `notin` fv_tm A2 ->
  x1 `notin` fv_tm A1 ->
  x1 `notin` fv_tm (subst_tm A1 x2 A2).
Proof.
pose proof subst_tm_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_fresh : lngen.

Lemma subst_tm_lc_tm :
forall A1 A2 x1,
  lc_tm A1 ->
  lc_tm A2 ->
  lc_tm (subst_tm A2 x1 A1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tm_lc_tm : lngen.

(* begin hide *)

Lemma subst_tm_open_tm_wrt_tm_rec_mutual :
(forall A3 A1 A2 x1 n1,
  lc_tm A1 ->
  subst_tm A1 x1 (open_tm_wrt_tm_rec n1 A2 A3) = open_tm_wrt_tm_rec n1 (subst_tm A1 x1 A2) (subst_tm A1 x1 A3)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tm_open_tm_wrt_tm_rec :
forall A3 A1 A2 x1 n1,
  lc_tm A1 ->
  subst_tm A1 x1 (open_tm_wrt_tm_rec n1 A2 A3) = open_tm_wrt_tm_rec n1 (subst_tm A1 x1 A2) (subst_tm A1 x1 A3).
Proof.
pose proof subst_tm_open_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

Lemma subst_tm_open_tm_wrt_tm :
forall A3 A1 A2 x1,
  lc_tm A1 ->
  subst_tm A1 x1 (open_tm_wrt_tm A3 A2) = open_tm_wrt_tm (subst_tm A1 x1 A3) (subst_tm A1 x1 A2).
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve subst_tm_open_tm_wrt_tm : lngen.

Lemma subst_tm_open_tm_wrt_tm_var :
forall A2 A1 x1 x2,
  x1 <> x2 ->
  lc_tm A1 ->
  open_tm_wrt_tm (subst_tm A1 x1 A2) (a_Var_f x2) = subst_tm A1 x1 (open_tm_wrt_tm A2 (a_Var_f x2)).
Proof.
intros; rewrite subst_tm_open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve subst_tm_open_tm_wrt_tm_var : lngen.

(* begin hide *)

Lemma subst_tm_spec_rec_mutual :
(forall A1 A2 x1 n1,
  subst_tm A2 x1 A1 = open_tm_wrt_tm_rec n1 A2 (close_tm_wrt_tm_rec n1 x1 A1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tm_spec_rec :
forall A1 A2 x1 n1,
  subst_tm A2 x1 A1 = open_tm_wrt_tm_rec n1 A2 (close_tm_wrt_tm_rec n1 x1 A1).
Proof.
pose proof subst_tm_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_spec_rec : lngen.

(* end hide *)

Lemma subst_tm_spec :
forall A1 A2 x1,
  subst_tm A2 x1 A1 = open_tm_wrt_tm (close_tm_wrt_tm x1 A1) A2.
Proof.
unfold close_tm_wrt_tm; unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve subst_tm_spec : lngen.

(* begin hide *)

Lemma subst_tm_subst_tm_mutual :
(forall A1 A2 A3 x2 x1,
  x2 `notin` fv_tm A2 ->
  x2 <> x1 ->
  subst_tm A2 x1 (subst_tm A3 x2 A1) = subst_tm (subst_tm A2 x1 A3) x2 (subst_tm A2 x1 A1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_subst_tm :
forall A1 A2 A3 x2 x1,
  x2 `notin` fv_tm A2 ->
  x2 <> x1 ->
  subst_tm A2 x1 (subst_tm A3 x2 A1) = subst_tm (subst_tm A2 x1 A3) x2 (subst_tm A2 x1 A1).
Proof.
pose proof subst_tm_subst_tm_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_subst_tm : lngen.

(* begin hide *)

Lemma subst_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_mutual :
(forall A2 A1 x1 x2 n1,
  x2 `notin` fv_tm A2 ->
  x2 `notin` fv_tm A1 ->
  x2 <> x1 ->
  degree_tm_wrt_tm n1 A1 ->
  subst_tm A1 x1 A2 = close_tm_wrt_tm_rec n1 x2 (subst_tm A1 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x2) A2))).
Proof.
apply_mutual_ind tm_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec :
forall A2 A1 x1 x2 n1,
  x2 `notin` fv_tm A2 ->
  x2 `notin` fv_tm A1 ->
  x2 <> x1 ->
  degree_tm_wrt_tm n1 A1 ->
  subst_tm A1 x1 A2 = close_tm_wrt_tm_rec n1 x2 (subst_tm A1 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x2) A2)).
Proof.
pose proof subst_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec : lngen.

(* end hide *)

Lemma subst_tm_close_tm_wrt_tm_open_tm_wrt_tm :
forall A2 A1 x1 x2,
  x2 `notin` fv_tm A2 ->
  x2 `notin` fv_tm A1 ->
  x2 <> x1 ->
  lc_tm A1 ->
  subst_tm A1 x1 A2 = close_tm_wrt_tm x2 (subst_tm A1 x1 (open_tm_wrt_tm A2 (a_Var_f x2))).
Proof.
unfold close_tm_wrt_tm; unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve subst_tm_close_tm_wrt_tm_open_tm_wrt_tm : lngen.

Lemma subst_tm_a_Pi :
forall x2 A2 j1 B1 A1 x1,
  lc_tm A1 ->
  x2 `notin` fv_tm A1 `union` fv_tm B1 `union` singleton x1 ->
  subst_tm A1 x1 (a_Pi A2 j1 B1) = a_Pi (subst_tm A1 x1 A2) (j1) (close_tm_wrt_tm x2 (subst_tm A1 x1 (open_tm_wrt_tm B1 (a_Var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tm_a_Pi : lngen.

Lemma subst_tm_a_Abs :
forall x2 a1 A1 x1,
  lc_tm A1 ->
  x2 `notin` fv_tm A1 `union` fv_tm a1 `union` singleton x1 ->
  subst_tm A1 x1 (a_Abs a1) = a_Abs (close_tm_wrt_tm x2 (subst_tm A1 x1 (open_tm_wrt_tm a1 (a_Var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tm_a_Abs : lngen.

(* begin hide *)

Lemma subst_tm_intro_rec_mutual :
(forall A1 x1 A2 n1,
  x1 `notin` fv_tm A1 ->
  open_tm_wrt_tm_rec n1 A2 A1 = subst_tm A2 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x1) A1)).
Proof.
apply_mutual_ind tm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tm_intro_rec :
forall A1 x1 A2 n1,
  x1 `notin` fv_tm A1 ->
  open_tm_wrt_tm_rec n1 A2 A1 = subst_tm A2 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x1) A1).
Proof.
pose proof subst_tm_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tm_intro_rec : lngen.
#[export] Hint Rewrite subst_tm_intro_rec using solve [auto] : lngen.

Lemma subst_tm_intro :
forall x1 A1 A2,
  x1 `notin` fv_tm A1 ->
  open_tm_wrt_tm A1 A2 = subst_tm A2 x1 (open_tm_wrt_tm A1 (a_Var_f x1)).
Proof.
unfold open_tm_wrt_tm; default_simp.
Qed.

#[export] Hint Resolve subst_tm_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
