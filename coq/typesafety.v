Require Export StraTT.StraTT_inf.
Require Export StraTT.tactics.
Require Export StraTT.basics.
Require Export StraTT.ctx.
Require Export StraTT.subst.
Require Export StraTT.inversion.

Set Implicit Arguments.

Import SubstNotations.
Local Open Scope lc_scope.

(* This is for context conversion.
   We can replace with context with an equivalent one. *)

Inductive Ctx_DEquiv S : context -> context -> Prop :=
 | ctx_equiv_nil : Ctx_DEquiv S nil nil
 | ctx_equiv_cons : forall x i A1 A2 G1 G2,
     DEquiv S A1 A2 ->
     Ctx_DEquiv S G1 G2 ->
     DTyping S G2 A2 a_Type i ->
     x `notin` dom G1 \u dom G2 ->
     Ctx_DEquiv S (x ~ (Tm A1 i) ++ G1) (x ~ Tm A2 i ++ G2).

#[global] Hint Constructors Ctx_DEquiv : core.

Lemma binds_Ctx_DEquiv : forall S G1 G2,
    Ctx_DEquiv S G1 G2 -> forall x A1 i, binds x (Tm A1 i) G1 ->
    exists A2, binds x (Tm A2 i) G2 /\ DEquiv S A1 A2.
Proof.
  induction 1; intros; eauto. inversion H.
  edestruct (binds_cons_1 _ _ _ _ _ _ H3); eauto; split_hyp.
  - subst. inversion H5. subst.
    exists A2. split; eauto.
  - edestruct IHCtx_DEquiv; eauto. split_hyp.
    exists x1. split; eauto.
Qed.

Lemma Ctx_DEquiv_refl : forall S G, DCtx S G ->
    Ctx_DEquiv S G G.
Proof.
  induction 1.
  auto.
  econstructor; eauto with lc.
Qed.

#[local] Hint Resolve Ctx_DEquiv_refl : core.

Lemma DCtx_DTyping_conversion :
  (forall S, DSig S -> True) /\
  (forall S G1,
    DCtx S G1 ->
    forall G2, Ctx_DEquiv S G1 G2 -> DCtx S G2 /\
    forall x A j, binds x (Tm A j) G1
           -> DTyping S G2 A a_Type j) /\
  (forall S G1 a A k,
    DTyping S G1 a A k ->
    forall G2, Ctx_DEquiv S G1 G2 -> DTyping S G2 a A k).
Proof.
  eapply DSig_DCtx_DTyping_ind; intros; eauto.
  - split; inversion H0; subst; auto.
    intros. inversion H1.
  - split.
    inversion H1; subst; eauto with ctx.
    inversion H1; subst. clear H1.
    intros.
    specialize (H _ ltac:(eauto)). split_hyp.
    destruct (binds_cons_1 _ _ _ _ _ _ H1).
    + split_hyp. inversion H4. subst.
      eapply DTyping_weakening1.
      eauto.
      econstructor; eauto.
    + eapply DTyping_weakening1.
      eauto.
      econstructor; eauto.
  - specialize (H _ H0).
    move: H => [h0 _].
    eauto.
  - specialize (H _ H1).
    move: H => [h0 _].
    eauto.
  - specialize (H _ H0).
    move: H => [h0 bb].
    move: (binds_Ctx_DEquiv ltac:(eauto) _ _ _ b)=> b1; eauto.
    destruct b1 as [A2 [b2 Eq]].
    apply bb in b.
    eapply DT_Conv with (A := A2); eauto.
    apply DTyping_cumul with (j := j); auto.
  - pick fresh x and apply DT_Pi; eauto.
    spec x.
    eapply H0. eauto with lc.
  - pick fresh x and apply DT_AbsTm; eauto.
    spec x.
    eapply H1. eauto with lc.
  - pick fresh x and apply DT_AbsTy; eauto.
    spec x.
    eapply H0. eauto with lc.
  - specialize (H _ H0).
    move: H => [h0 _].
    eauto.
Unshelve.
exact 0.
Qed.

Lemma DCtx_conversion :
  (forall S G1 a A k,
    DTyping S G1 a A k -> forall G2, Ctx_DEquiv S G1 G2 -> DTyping S G2 a A k).
Proof.
  intros.
  eapply DCtx_DTyping_conversion; eauto.
Qed.

Lemma Reduce_Preservation : forall S G a b,
    Reduce S a b
    -> forall A k, DTyping S G a A k ->  DTyping S G b A k.
Proof.
  induction 1; intros B k0 DT.
  - (* beta *)
    move: (DTyping_a_App_inversion DT) => [ARR|PI].
    -- (* arrow *)
      move: ARR => [A [DABS Da]].
      pick fresh x.
      move: (DTyping_regularity DABS) => h.
      eapply DTyping_a_Arrow_inversion in h. split_hyp.
      eapply (@DTyping_a_Abs_inversion x) in DABS; eauto.
      move: DABS => [j1 [A1 [A2 [h [X | Y]]]]]. split_hyp. subst.
      ++ have E1: (DEquiv S A1 A). eapply DEquiv_Arrow_inj1; eauto.
         have E2: (DEquiv S A2 B). eapply DEquiv_Arrow_inj2; eauto.
         subst.
         move: (DTyping_DCtx h) => DC. inversion DC. subst.
         rewrite (subst_tm_intro x); auto.
         replace B with (subst_tm a x B). 2: rewrite subst_tm_fresh_eq; auto.
         eapply DT_Conv with (k:=k0) (B:=A1) in Da; eauto.
         eapply DTyping_subst1; eauto.
         eapply DT_Conv; eauto.
         eapply DTyping_regularity.
         eapply DTyping_weakening1; eauto.
      ++ move: Y => [A3 Z]. split_hyp. subst.
         (* impossible. by consistency of DEquiv *)
         eapply ineq_Arrow_Pi in H3. contradiction.
    -- (* pi *)
      move: PI => [j [A0 [B0 [TABS [Ta EQ]]]]].
      move: (DTyping_regularity TABS) => h.
      pick fresh x.
      eapply (@DTyping_a_Pi_inversion x) in h. split_hyp.
      eapply (@DTyping_a_Abs_inversion x) in TABS; eauto.
      move: TABS => [j1 [A1 [A2 [h [X | Y]]]]]. split_hyp.
      ++ (* impossible. by consistency of DEquiv *)
        apply DE_Sym in H4.
        eapply ineq_Arrow_Pi in H4. contradiction.
      ++ move: Y => [A3 Z]. split_hyp. subst.
      (* Consistency of DEquiv *)
      have E1: (DEquiv S A1 A0).  eapply DEquiv_Pi_inj1; eauto.
      have E2: (DEquiv S (open B0 a) (open A3 a)).
               eapply DEquiv_Pi_inj3; eauto with lc.
      have E3: (j = j1). eapply DEquiv_Pi_inj2; eauto.
      subst.
      eapply DT_Conv with (A:= open A3 a); auto.
      rewrite (subst_tm_intro x b); auto.
      rewrite (subst_tm_intro x A3); auto.
      simpl_env in h.
      eapply DTyping_subst1; eauto.
      eapply DCtx_conversion; eauto with ctx.
      eapply DTyping_regularity; eauto.
      eapply DE_Sym. eapply DE_Trans; eauto.
      ++ auto.
  - have DS: DSig S. eauto with ctx.
    move: (DTyping_a_Const_inversion DT) => [a0 [A0 [j h]]].
    split_hyp.
    have U :uniq S. eauto using DSig_uniq.
    eapply DT_Conv with (A := (incr i A0)); auto.
    2: { eapply DTyping_regularity; eauto. }
    replace G with (G ++ nil). 2: simpl_env; auto.
    eapply DTyping_weakening1 with (E:=nil)(F:=G).
    2: {  simpl_env; eauto with ctx. }

    move: (binds_unique _ _ _ _ _ H H1 U) => u. inversion u. subst.
    apply DSig_regularity in H1; auto. split_hyp.
    replace nil with (IncG i nil). 2: { auto. }
    apply DTyping_cumul with (j := i + j); auto. lia.
    eapply DTyping_incr; eauto.
  - (* app cong *)
    move: (DTyping_a_App_inversion DT) => [ARR|PI].
    ++ move: ARR => [A [Tb Ta]].
       apply IHReduce in Tb.
       eapply DT_AppTm; eauto.
    ++ move: PI => [j [A0 [B0 [Tb [Ta E]]]]].
       apply IHReduce in Tb.
       eapply DT_Conv with (A:= open B0 a).
       eapply DT_AppTy; eauto.
       pick fresh x.
       move: (DTyping_regularity Tb) => TPi.
       move: (@DTyping_a_Pi_inversion x _ _ _ _ _ _ TPi ltac:(auto)) => h. split_hyp. auto.
       eapply DTyping_regularity; eauto.
       eapply DE_Sym; auto.
  - (* absurd cong *)
    move: (DTyping_regularity DT) => TB.
    move: (DTyping_a_Absurd_inversion DT) => Tb.
    econstructor; eauto.
Qed.

Inductive Value : tm -> Prop :=
 | V_Abs  : forall b, Value (a_Abs b)
 | V_Type : Value a_Type
 | V_Pi   : forall A k B, Value (a_Pi A k B)
 | V_Arrow : forall A B, Value (a_Arrow A B)
 | V_Bottom : Value a_Bottom.

#[global] Hint Constructors Value : core.

Lemma canonical_Arrow : forall S A B b k,
    DTyping S nil b (a_Arrow A B) k -> Value b -> exists a, b = a_Abs a.
Proof.
  intros.
  dependent induction H; subst.
  all: match goal with [ H2 : Value _ |- _ ] => inversion H2 ; subst end.
  all: try solve [eexists; eauto].
  - apply DTyping_a_Type_inversion in H.
    assert False. eapply ineq_Arrow_Type. eapply DE_Sym. eapply DE_Trans; eauto.
    contradiction.
  - pick fresh x.
    eapply (@DTyping_a_Pi_inversion1 x) in H; eauto. split_hyp.
    assert False. eapply ineq_Arrow_Type. eapply DE_Trans. eapply DE_Sym; eauto. eauto.
    contradiction.
  - eapply DTyping_a_Arrow_inversion1 in H; eauto. split_hyp.
    assert False. eapply ineq_Arrow_Type. eapply DE_Trans. eapply DE_Sym; eauto. eauto.
    contradiction.
  - eapply DTyping_a_Bottom_inversion in H; eauto.
    assert False. eapply ineq_Arrow_Type. eapply DE_Sym. eapply DE_Trans; eauto.
    contradiction.
Qed.

Lemma canonical_Pi : forall S A j B b k,
    DTyping S nil b (a_Pi A j B) k -> Value b -> exists a, b = a_Abs a.
Proof.
  intros.
  dependent induction H; subst.
  all: match goal with [ H2 : Value _ |- _ ] => inversion H2 ; subst end.
  all: try solve [eexists; eauto].
  - apply DTyping_a_Type_inversion in H.
    assert False. eapply ineq_Pi_Type. eapply DE_Sym. eapply DE_Trans; eauto.
    contradiction.
  - pick fresh x.
    eapply (@DTyping_a_Pi_inversion1 x) in H; eauto. split_hyp.
    assert False. eapply ineq_Pi_Type. eapply DE_Trans. eapply DE_Sym; eauto. eauto.
    contradiction.
  - eapply DTyping_a_Arrow_inversion1 in H; eauto. split_hyp.
    assert False. eapply ineq_Pi_Type. eapply DE_Trans. eapply DE_Sym; eauto. eauto.
    contradiction.
  - eapply DTyping_a_Bottom_inversion in H; eauto.
    assert False. eapply ineq_Pi_Type. eapply DE_Sym. eapply DE_Trans; eauto.
    contradiction.
Qed.

Lemma canonical_Bottom : forall S b k,
    DTyping S nil b a_Bottom k -> Value b -> False.
Proof.
  intros.
  dependent induction H; subst.
  all: match goal with [ H2 : Value _ |- _ ] => inversion H2 ; subst end.
  - pick fresh x.
    eapply (@DTyping_a_Abs_inversion x) in H; eauto.
    destruct H as (j1 & A1 & A2 & h1 & h2).
    destruct h2 as [[h2 h3]| [A3 [h2 h3]]].
    + assert False. eapply ineq_Arrow_Bottom.
      eapply DE_Sym. eapply DE_Trans; eauto.
      contradiction.
    + assert False. eapply ineq_Pi_Bottom.
      eapply DE_Sym. eapply DE_Trans; eauto.
      contradiction.
  - apply DTyping_a_Type_inversion in H.
    assert False. eapply ineq_Type_Bottom.
    eapply DE_Sym. eapply DE_Trans; eauto.
    contradiction.
  - pick fresh x.
    eapply (@DTyping_a_Pi_inversion1 x) in H; eauto. split_hyp.
    assert False. eapply ineq_Type_Bottom. eapply DE_Trans. eapply DE_Sym; eauto. eauto.
    contradiction.
  - eapply DTyping_a_Arrow_inversion1 in H; eauto. split_hyp.
    assert False. eapply ineq_Type_Bottom. eapply DE_Trans. eapply DE_Sym; eauto. eauto.
    contradiction.
  - eapply DTyping_a_Bottom_inversion in H; eauto.
    assert False. eapply ineq_Type_Bottom. eapply DE_Sym. eapply DE_Trans; eauto.
    contradiction.
Qed.

Lemma Reduce_Progress : forall S a A k,
    DTyping S nil a A k -> Value a \/ exists b, Reduce S a b.
Proof.
  intros S a A k H.
  dependent induction H; intros.
  (* already values *)
  all: try solve [left; eauto].
  (* easy step: constants *)
  all: try solve [right; eexists; eauto].
  (* no variables *)
  all: try solve [inversion H].
  (* beta arrow *)
  - destruct IHDTyping1 as [|[b' Hb]]; eauto.
    + move: (canonical_Arrow H H1) => [ b' EQ].
      subst.
      right.
      exists (open b' a).
      econstructor; eauto with lc.
    + right. eexists. eauto with lc.
  (* beta pi *)
  - destruct IHDTyping1 as [|[b' Hb]]; eauto.
    + move: (canonical_Pi ltac:(eauto) ltac:(eauto)) => [ b' EQ].
      subst.
      right.
      exists (open b' a).
      econstructor; eauto with lc.
    + right. eexists. eauto with lc.
  - (* absurd *)
    right.
    destruct IHDTyping2; auto.
    move: (canonical_Bottom H0 H1) => h. contradiction.
    destruct H1 as [b' hb'].
    exists (a_Absurd b'). eauto.
  - destruct IHDTyping1 as [|[b' Hb]]; eauto.
Unshelve.
all: exact nil.
Qed.

(* Evaluation will either step to a value or diverge *)
CoInductive Eval S a : Prop :=
| E_Value : Value a -> Eval S a
| E_Step b : Reduce S a b -> Eval S b -> Eval S a.

CoFixpoint TypeSafety : forall S a A k,
  DTyping S nil a A k -> Eval S a.
Proof.
  intros S a A k H.
  destruct (Reduce_Progress H) as [v | [b r]].
  - now constructor.
  - eapply E_Step; eauto.
    eapply TypeSafety.
    eapply Reduce_Preservation; eauto.
Qed.