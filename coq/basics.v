
Require Export Metalib.LibTactics.

Require Export ssreflect.

Require Export Coq.Program.Equality.  (* for dependent induction *)

Require Export Lia.
Require Export StraTT.StraTT_inf.
Require Export StraTT.tactics.
Require Export StraTT.axioms.

Set Implicit Arguments.

(* Some notations for open and close *)
Module SubstNotations.
  Declare Scope lc_scope.
  Delimit Scope lc_scope with tm.
  Notation "t [ x ~> u ]" := (subst_tm u x t)
    (at level 10, left associativity, x constr) : lc_scope.
  Notation "t ^ x"    := (open_tm_wrt_tm t (a_Var_f x)) : lc_scope.
  Notation open t1 t2 := (open_tm_wrt_tm t1 t2).
  Notation close x t  := (close_tm_wrt_tm x t).
End SubstNotations.

Import SubstNotations.
Local Open Scope lc_scope.

Scheme DSig_ind := Induction for DSig Sort Prop
  with DCtx_ind := Induction for DCtx Sort Prop
  with DTyping_ind := Induction for DTyping Sort Prop.
Combined Scheme DSig_DCtx_DTyping_ind from DSig_ind , DCtx_ind , DTyping_ind.

Lemma incr_open : forall a b k,
    incr k (open_tm_wrt_tm a b) = open_tm_wrt_tm (incr k a) (incr k b).
Proof.
  unfold open_tm_wrt_tm.
  generalize 0.
  move=> n a.
  move: n.
  induction a.
  all: intros n0 b k0.
  all: simpl; auto.
  all: try rewrite IHa1.
  all: try rewrite IHa2.
  all: try rewrite IHa.
  all: auto.
  destruct (lt_eq_lt_dec n n0); simpl; auto.
  destruct s; simpl; auto.
Qed.

(* local closure *)

Lemma lc_incr : forall k B, lc_tm B -> lc_tm (incr k B).
Proof.
  induction 1; simpl; eauto.
  - eapply lc_a_Pi; auto. intro x.
  specialize (H1 x).
  rewrite incr_open in H1. simpl in H1.
  auto.
  - eapply lc_a_Abs; auto. intro x.
  specialize (H0 x).
  rewrite incr_open in H0. simpl in H0.
  auto.
Qed.

#[export] Hint Resolve lc_incr : lc.

Lemma DEquiv_lc : forall {S A B}, DEquiv S A B -> lc_tm A /\ lc_tm B.
Proof.
induction 1; split_hyp; split; eauto with lc.
- inversion H. eapply lc_body_tm_wrt_tm; eauto.
- pick fresh x.
  specialize (H x Fr).
  eapply lc_a_Abs_exists with (x1:=x).
  rewrite H.
  eauto.
- pick fresh x.
  edestruct H1; eauto.
  eapply lc_a_Pi_exists with (x1 := x); eauto.
- pick fresh x.
  edestruct H1; eauto.
  eapply lc_a_Pi_exists with (x1 := x); eauto.
- pick fresh x.
  edestruct H0; eauto.
  eapply lc_a_Abs_exists with (x1:=x); eauto.
- pick fresh x.
  edestruct H0; eauto.
  eapply lc_a_Abs_exists with (x1:=x); eauto.
Qed.

Lemma DEquiv_lc1 : forall {S A B}, DEquiv S A B -> lc_tm A.
Proof. intros; eapply DEquiv_lc; eauto. Qed.
Lemma DEquiv_lc2 : forall {S A B}, DEquiv S A B -> lc_tm B.
Proof. intros; eapply DEquiv_lc; eauto. Qed.

Lemma DSig_DCtx_DTyping_lc :
  (forall S, DSig S -> forall x a A k, binds x (Def a k A) S -> lc_tm a /\ lc_tm A) /\
  (forall S G, DCtx S G ->  forall x A k, binds x (Tm A k) G -> lc_tm A) /\
  (forall S G a A k, DTyping S G a A k -> lc_tm a /\ lc_tm A).
Proof.
  eapply DSig_DCtx_DTyping_ind.
  all: intros; split_hyp; try split; eauto.
  all: try solve [inversion H].
  all: try solve [inversion H0].
  all: try solve [inversion H2; try inversion H5; subst; eauto; edestruct H; eauto].
  all: try solve [inversion H1; try inversion H3; subst; eauto; edestruct H; eauto].
  - edestruct H0; eauto with lc.
  - pick fresh x.
    edestruct H0; eauto.
    eapply lc_a_Pi_exists with (x1 := x); eauto.
  - pick fresh x.
    edestruct H1; eauto.
    eapply lc_a_Abs_exists with (x1 := x); eauto.
  - pick fresh x.
    edestruct H0; eauto.
    eapply lc_a_Abs_exists with (x1 := x); eauto.
  - pick fresh x.
    edestruct H0; eauto.
    eapply lc_a_Pi_exists with (x1 := x); eauto.
  - inversion H2.
    eapply lc_body_tm_wrt_tm; eauto.
Qed.

Lemma DTyping_lc1 : forall {S G a A k}, DTyping S G a A k -> lc_tm a.
Proof.
  move:  DSig_DCtx_DTyping_lc => [ _ [ _ h]].
  intros. edestruct h; eauto. Qed.

Lemma DTyping_lc2 : forall {S G a A k}, DTyping S G a A k -> lc_tm A.
Proof.
  move:  DSig_DCtx_DTyping_lc => [ _ [ _ h]].
  intros. edestruct h; eauto. Qed.

Lemma DCtx_lc : forall {S G}, DCtx S G -> forall x A k, binds x (Tm A k) G -> lc_tm A.
Proof.
  move:  DSig_DCtx_DTyping_lc => [ _ [ h _]].
  intros. eauto. Qed.

Lemma DSig_lc1 : forall {S}, DSig S -> forall x a A k, binds x (Def a k A) S -> lc_tm a.
Proof.
  move:  DSig_DCtx_DTyping_lc => [ h _].
  intros. edestruct h; eauto. Qed.

Lemma DSig_lc2 : forall {S}, DSig S -> forall x a A k, binds x (Def a k A) S -> lc_tm A.
Proof.
  move:  DSig_DCtx_DTyping_lc => [ h _].
  intros. edestruct h; eauto. Qed.

#[export] Hint Resolve DTyping_lc1 DTyping_lc2 DEquiv_lc1
  DEquiv_lc2 DCtx_lc DSig_lc1 DSig_lc2 : lc.

#[export] Hint Resolve DTyping_lc1 DEquiv_lc1 DSig_lc1 : lc1.

#[export] Hint Resolve DTyping_lc2 DEquiv_lc2 DSig_lc2 : lc2.

(* ---------------------------------------------------------------------- *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C1 := gather_atoms_with (fun x : context => dom x) in
  let C2 := gather_atoms_with (fun x : signature => dom x) in
  let D := gather_atoms_with (fun x => fv_tm x) in
  constr:(A \u B \u C1 \u C2 \u D).

Lemma subst_tm_var : forall a x, subst_tm a x (a_Var_f x) = a.
Proof. intros. simpl. destruct (x == x). auto. done. Qed.
Lemma subst_tm_var_neq : forall a x y, y <> x -> subst_tm a x (a_Var_f y) = a_Var_f y.
Proof. intros. simpl. destruct (y == x). done. auto. Qed.

#[export] Hint Rewrite subst_tm_var : lngen.
#[export] Hint Rewrite subst_tm_var_neq using solve [auto] : lngen.
#[export] Hint Rewrite subst_tm_open_tm_wrt_tm : lngen.
#[export] Hint Rewrite fv_tm_subst_tm_upper : lngen.

(* When proving substitution lemmas, look for a hypothesis that uses
   "open" and rewrite it to push the substitution into the term *)
Ltac rewrite_subst_open_hyp :=
  match goal with
      [ H0 : context [((?t ^ ?y) [?x ~> ?u])] |- _ ] =>
        repeat rewrite subst_tm_open_tm_wrt_tm in H0; auto;
        repeat rewrite subst_tm_var_neq in H0; auto
      | [ H0 : context [(subst_tm ?x ?u (open_tm_wrt_tm ?t (a_Var_f ?y)))] |- _ ] =>
        repeat rewrite subst_tm_open_tm_wrt_tm in H0; auto;
        repeat rewrite subst_tm_var_neq in H0; auto
    end.

Lemma fv_incr : forall k a,
    fv_tm (incr k a) = fv_tm a.
Proof.
  induction a; intros; simpl; auto; f_equal; auto.
Qed.

Lemma DTyping_fv :
    (forall S, DSig S -> forall a k A x, binds x (Def a k A) S -> fv_tm a [<=] dom S /\ fv_tm A [<=] dom S) /\
    (forall S G, DCtx S G -> forall A k x, binds x (Tm A k) G -> fv_tm A [<=] dom G \u dom S) /\
    (forall S G a A k, DTyping S G a A k -> fv_tm a [<=] dom G \u dom S /\ fv_tm A [<=] dom G \u dom S).
Proof.
  eapply DSig_DCtx_DTyping_ind; simpl.
  all: intros.
  all: try solve [inversion H].

  all: try fsetdec.
  all: try (match goal with [H : binds _ _ _ |- _ ] =>
                              apply binds_cons_1 in H; destruct H end).
  all: split_hyp.
  all: try match goal with [ H : Tm _ _ = Tm _ _ |- _ ] => inversion H ; subst; clear H end.
  all: try match goal with [ H : Def _ _ _ = Def _ _ _ |- _ ] => inversion H ; subst; clear H end.

  all: try split.
  all: eauto using KeySetProperties.subset_add_2.
  all: try (match goal with
    [ H : binds _ (Def _ _ _) _ , H0 : forall a k A x, binds _ (Def _ _ _) _ -> _|- _ ] =>
      move:(H0 _ _ _ _ H) => h1; split_hyp end).

  all: try (match goal with
    [ H : binds _ (Tm _ _) _ , H0 : forall k A x, binds _ (Tm _ _) _ -> _|- _ ] =>
      move: (H0 _ _ _ H) => h; split_hyp end).

  all: try rewrite fv_incr.
  all: try fsetdec.

  all: try (match goal with [H : binds _ _ _ |- _ ] =>
     apply binds_In in H end).

  all: subst.
  all: eauto.
  all: try fsetdec.
  all: pick fresh y; repeat spec y.
  all: split_hyp.
  all: simpl in *.
  all: try (match goal with [H : fv_tm (open_tm_wrt_tm _ _) [<=] _ |- _ ] =>
                              rewrite <- fv_tm_open_tm_wrt_tm_lower in H end).
  all: try (match goal with [ |- union _ _ [<=] _] => eapply AtomSetProperties.union_subset_3 end).
  all: simpl in *.
  all: try rewrite fv_incr.
  all: eauto.
  all: try (match goal with [H : fv_tm (open_tm_wrt_tm _ _) [<=] _ |- _ ] =>
                              rewrite <- fv_tm_open_tm_wrt_tm_lower in H end).
  all: repeat match goal with [ H : empty [<=] _ |- _ ] => clear H end.
  have: y `notin` fv_tm B; fsetdec; clear Fr; fsetdec.
  clear H H0 H4. have: y `notin` fv_tm b; fsetdec; clear Fr; fsetdec.
  clear H H2. have: y `notin` fv_tm b; fsetdec; clear Fr; fsetdec.
  clear H H0. have: y `notin` fv_tm B; fsetdec; clear Fr; fsetdec.
  rewrite fv_tm_open_tm_wrt_tm_upper. clear Fr. fsetdec.
Qed.

Lemma DSig_uniq : forall S, DSig S -> uniq S.
Proof. induction 1; eauto. Qed.

Lemma DCtx_uniq : forall S G, DCtx S G -> uniq G.
Proof. induction 1; eauto. Qed.
