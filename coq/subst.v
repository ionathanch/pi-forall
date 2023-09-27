Require Export StraTT.StraTT_inf.
Require Export StraTT.tactics.
Require Export StraTT.basics.
Require Export StraTT.ctx.
Require Export StraTT.restrict.

Set Implicit Arguments.

Import SubstNotations.
Local Open Scope lc_scope.

(* -------------------------------------------------------------------------- *)
(* All judgements are stable under substitution. *)

Definition map_assn f a :=
  match a with
  | Tm A k => Tm (f A k) k
  end.

Definition f (j:nat) B x := (map_assn (fun A k => subst_tm B x A)).

Definition subst_ctx j (b:tm) (x:var) (F:context) :=  map (f j b x) F.

Lemma DEquiv_subst : forall S A B x a, DEquiv S A B -> DSig S -> x `notin` dom S ->
                                lc_tm a -> DEquiv S (subst_tm a x A) (subst_tm a x B).
Proof.
  induction 1; intros; simpl; eauto with lngen.
  - (* beta *)
    autorewrite with lngen; auto.
    eapply DE_Beta; eauto with lngen.
    move: (subst_tm_lc_tm _ _ x H ltac:(eauto)) => h. simpl in h.
    auto.
  - (* eta *)
    pick fresh y and apply DE_Eta.
    spec y.
    replace (b' [x ~> a] ^ y) with ((b' ^ y)[x ~> a]).
    rewrite H. simpl. destruct (y == x). subst. fsetdec. auto.
    autorewrite with lngen; auto.
    eapply subst_tm_lc_tm; eauto.
  - (* const *)
    have DT: DTyping S nil a0 A k.
    eapply DSig_regularity; eauto.
    move: (DTyping_fv) => [_ [_ FV]].
    edestruct FV; eauto.
    have NI: (x `notin` fv_tm a0).
    fsetdec.
    rewrite subst_tm_fresh_eq.
    rewrite fv_incr. auto.
    eauto.
  - (* pi *)
    pick fresh y and apply DE_Pi; eauto.
    spec y.
    rewrite_subst_open_hyp.
  - (* abs *)
    pick fresh y and apply DE_Abs; eauto.
    spec y.
    rewrite_subst_open_hyp.
Qed.

Lemma DCtx_DTyping_subst : forall S1 F b B j, DTyping S1 F b B j ->
  ((forall S, DSig S -> S1 = S -> True) /\
    (forall S G, DCtx S G -> forall E x, (G = E ++ x ~ Tm B j ++ F) -> S1 = S -> DCtx S (subst_ctx j b x E ++ F)) /\
   (forall S G a A k, DTyping S G a A k -> forall E x, (G = E ++ x ~ Tm B j ++ F) -> S1 = S ->
                                         DTyping S (subst_ctx j b x E ++ F) (subst_tm b x a) (subst_tm b x A) k)).
Proof.
  intros.
  eapply DSig_DCtx_DTyping_ind; intros; auto.
  - try solve [destruct E; simpl in *; done].
  - simpl in H2; destruct E; inversion H2; subst; clear H2; eauto.
  simpl. econstructor; eauto.
  unfold subst_ctx. simpl_env in *. fsetdec.
  - (* const *)
    simpl.
    have DT: DTyping S nil a A j0.
    eapply DSig_regularity; eauto.
    + (* eapply DT_Const; eauto.
         eapply DCtx_DSig; eauto. *)
      move: (DTyping_fv) => [_ [_ FV]].
      edestruct (FV _ _ _ _ _ DT).
      rewrite subst_tm_fresh_eq.
      rewrite fv_incr.
      subst.
      move: (DCtx_disjoint d) => h. destruct_uniq. fsetdec.
      eauto.
  - (* var *)
    subst. rename b into bb. rename b0 into b.
    destruct (x == x0).
    + subst. apply binds_mid_eq in b.
      ++ inversion b. subst. rewrite subst_tm_var.
         move: DTyping_fv => [_ [_ h1]]. move: (h1 _ _ _ _ _ H) => [h0 h2].
         move: (DCtx_uniq d) => u.
         move: (DCtx_disjoint d)=> uu. destruct_uniq.
         rewrite subst_tm_fresh_eq.
         fsetdec.
         eapply DTyping_weakening1; auto.
         apply DTyping_cumul with (j := j); auto.
      ++ eauto using DCtx_uniq.
    + rewrite subst_tm_var_neq. auto.
      move: (binds_remove_mid _ _ _ _ _ _ _ b n) => h0.
      eapply DCtx_regularity in b; eauto.
      destruct (binds_app_1 _ _ _ _ _ h0).
      ++ (* x0 after type substitution *)
        eapply DT_Var with (j := j0); auto.
        eapply binds_app_2.
        unfold subst_ctx.
        eapply binds_map with (f:= f j bb x0) in H1.
        simpl in H1. eauto.
     ++ (* x0 before type substutution *)
       have h1: (DTyping S F A a_Type j0).
       * eapply DCtx_regularity with (x := x); eauto.
         eapply DCtx_app.
         eapply DCtx_app. eauto.
       * apply DTyping_fv in h1. split_hyp.
         move: (DCtx_uniq d) => u.
         move: (DCtx_disjoint d) => uu.
         destruct_uniq.
         rewrite subst_tm_fresh_eq. fsetdec.
         eapply DT_Var with (j := j0); auto.
  - (* arrow *)
    simpl. eauto.
  - (* pi *)
    simpl.
    pick fresh y and apply DT_Pi; eauto.
    repeat spec y.
    rename H1 into IH.
    specialize (IH (y ~ Tm A j0 ++ E) x ltac:(subst G; auto)).
    rewrite_subst_open_hyp.
    eauto with lc.
  - (* abstm *)
    subst. simpl.
    pick fresh y and apply DT_AbsTm; eauto.
    repeat spec y.
    rename H2 into IH.
    specialize (IH (y ~ (Tm A k) ++ E) x).
    specialize (IH ltac:(reflexivity)).
    simpl in IH.
    simpl_env in IH.
    rewrite_subst_open_hyp.
    eauto with lc.
  - (* absty *)
    subst. simpl.
    pick fresh y and apply DT_AbsTy; eauto.
    repeat spec y.
    rename H1 into IH.
    specialize (IH (y ~ (Tm A j0) ++ E) x).
    specialize (IH ltac:(reflexivity)).
    simpl in IH.
    simpl_env in IH.
    rewrite_subst_open_hyp;
    eauto with lc.
  - (* apptm *)
    subst; simpl.
    eauto.
  - (* appty *)
    subst; simpl.
    rewrite subst_tm_open_tm_wrt_tm; eauto with lc.
  - (* absurd *)
    subst; simpl. eauto.
  - (* cumul *)
    subst; simpl.
    eapply DT_Conv; eauto.
    eapply DEquiv_subst; eauto with lc.
    eapply DCtx_DSig.
    eapply DTyping_DCtx.
    eauto.
    move: (DTyping_DCtx d) => dd.
    move: (DCtx_disjoint dd) => u.
    destruct_uniq. fsetdec.
Unshelve.
all: exact nil.
Qed.

(* Special case of substitution lemma, when the variable assumption is the most
   recently added one to the context. *)
Lemma DTyping_subst1 :
  forall S E x B j k a A  b,
    DTyping S E b B j ->
    DTyping S ((x ~ (Tm B j)) ++ E) a A k ->
    DTyping S E (subst_tm b x a) (subst_tm b x A) k.
Proof.
  intros.
  apply (DCtx_DTyping_subst) in H.
  move: H => [_ [h0 h1]].
  specialize (h1 _ _ _ _ _ H0 nil x ltac:(reflexivity)).
  simpl_env in h1.
  eauto.
Qed.

(* Renaming lemma when the variable does not appear in the type. *)
Lemma DTyping_rename1 : forall y x S A j G b B k,
 DTyping S (y ~ Tm A j ++ G) (b ^ y) B k ->
 x `notin` dom G \u dom S ->
 y `notin` fv_tm b \u fv_tm B ->
 DTyping S (x ~ Tm A j ++ G) (b ^ x) B k.
Proof.
  intros.
  destruct (x == y). subst. auto.
  move: (DTyping_DCtx H) => h. inversion h. subst.
  replace B with (subst_tm (a_Var_f x) y B); auto.
  rewrite (subst_tm_intro y). auto.
  eapply DTyping_subst1; eauto.
  eapply DTyping_weakening; eauto using DTyping_DCtx.
  econstructor; eauto.
  eapply DTyping_weakening1; eauto using DTyping_DCtx.
  rewrite subst_tm_fresh_eq.  auto.
  auto.
Unshelve.
exact 0.
Qed.

(* Renaming lemma when the variable appears in the type. *)
Lemma DTyping_rename2 : forall y x S A j G b B k,
 DTyping S (y ~ Tm A j ++ G) (b ^ y) (B ^ y) k ->
 x `notin` dom G \u dom S ->
 y `notin` fv_tm b \u fv_tm B ->
 DTyping S (x ~ Tm A j ++ G) (b ^ x) (B ^ x) k.
Proof.
  intros.
  destruct (x == y). subst. auto.
  move: (DTyping_DCtx H) => h. inversion h. subst.
  rewrite (subst_tm_intro y b). auto.
  rewrite (subst_tm_intro y B). auto.
  eapply DTyping_subst1; eauto.
  eapply DTyping_weakening; eauto using DTyping_DCtx.
  econstructor; eauto.
  eapply DTyping_weakening1; eauto using DTyping_DCtx.
Unshelve.
exact 0.
Qed.
