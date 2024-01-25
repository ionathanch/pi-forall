Require Export StraTT.StraTT_inf.
Require Export StraTT.tactics.
Require Export StraTT.basics.
Require Export StraTT.ctx.
Require Export StraTT.subst.
Require Export StraTT.restrict.

Set Implicit Arguments.

Import SubstNotations.
Local Open Scope lc_scope.

Lemma DTyping_a_Pi_inversion1 : forall x S G j A B C k,
    DTyping S G (a_Pi A j B) C k ->
    x `notin` dom G \u dom S ->
    DEquiv S C a_Type /\ DTyping S G A a_Type j /\
    j < k /\ DTyping S (x ~ Tm A j ++ G) (open_tm_wrt_tm B (a_Var_f x)) a_Type k.
Proof.
  intros. dependent induction H.
  + split. auto. clear H1. repeat split; auto.
    pick fresh y. repeat spec y.
    eapply DTyping_rename1; eauto.
  + specialize (IHDTyping1 _ _ _ ltac:(auto) ltac:(auto)).
    destruct IHDTyping1; split_hyp.
    repeat split; auto.
    eapply DE_Trans. eapply DE_Sym; eauto. eauto.
Qed.

(*
Lemma DTyping_a_Pi_inversion1 : forall x S G j A B C k,
    DTyping S G (a_Pi A j B) C k ->
    DEquiv S C a_Type ->
    x `notin` dom G \u dom S ->
    DTyping S G A a_Type j /\
    j < k /\ DTyping S (x ~ Tm A j ++ G) (open_tm_wrt_tm B (a_Var_f x)) a_Type k.
Proof.
  intros. dependent induction H.
  + split. auto. clear H1. split. auto.
    pick fresh y. repeat spec y.
    eapply DTyping_rename1; eauto.
  + have EQ: DEquiv S A0 a_Type. eapply DE_Trans; eauto.
    specialize (IHDTyping1 _ _ _ ltac:(reflexivity) ltac:(auto) ltac:(auto)).
    destruct IHDTyping1; split_hyp.
    repeat split; auto. lia. eapply DT_Conv; eauto using DTyping_DCtx.
Qed.
*)

Lemma DTyping_a_Pi_inversion : forall x S G j A B k,
    DTyping S G (a_Pi A j B) a_Type k ->
    x `notin` dom G \u dom S ->
    DTyping S G A a_Type j /\
    j < k /\ DTyping S (x ~ Tm A j ++ G) (open_tm_wrt_tm B (a_Var_f x)) a_Type k.
Proof.
  intros.
  eapply DTyping_a_Pi_inversion1; eauto.
Qed.

Lemma DTyping_a_Arrow_inversion1 : forall S G A B C k,
    DTyping S G (a_Arrow A B) C k -> DEquiv S C a_Type /\
    DTyping S G A a_Type k /\ DTyping S G B a_Type k.
Proof.
  intros.
  dependent induction H.
  + repeat split; eauto.
  + edestruct IHDTyping1; eauto.
Qed.

Lemma DTyping_a_Arrow_inversion : forall S G A B k,
    DTyping S G (a_Arrow A B) a_Type k ->
    DTyping S G A a_Type k /\ DTyping S G B a_Type k.
Proof.
  intros.
  eapply DTyping_a_Arrow_inversion1; eauto.
Qed.

(* --------------- regularity ----------------- *)

Lemma DTyping_regularity : (forall S G a A k, DTyping S G a A k -> DTyping S G A a_Type k).
Proof.
  induction 1; eauto.
  - (* const *)
    have DS: DSig S. eapply DCtx_DSig; eauto.
    eapply DSig_regularity in H; auto. split_hyp.
    replace a_Type with (incr i a_Type); auto.
    replace G with (G ++ nil).
    eapply DTyping_weakening1; eauto.
    replace nil with (IncG i nil); auto.
    apply DTyping_cumul with (j := i + j); auto.
    eapply DTyping_incr; auto.
    all: simpl_env; auto.
  - (* var *)
    apply DTyping_cumul with (j := j); auto.
    eapply DCtx_regularity in H0; eauto.
  - eapply DT_Type; eauto. eapply DTyping_DCtx; eauto.
  - apply DTyping_a_Arrow_inversion in IHDTyping1. split_hyp. eauto.
  - pick fresh x.
    move: (@DTyping_a_Pi_inversion x _ _ _ _ _ _ IHDTyping1 ltac:(auto)) => h0.
    destruct h0; split_hyp.
    + rewrite (subst_tm_intro x). auto.
      replace (a_Type) with (subst_tm a x a_Type).
      eapply DTyping_subst1; eauto. simpl; auto.
Qed.

(* Just convenient to have... *)
Corollary DTyping_regularity_a_Pi : forall L S G b A j B k,
  (forall x, x `notin` L -> DTyping S (x ~ Tm A j ++ G) (b ^ x) (B ^ x) k) ->
  (forall x, x `notin` L -> DTyping S (x ~ Tm A j ++ G) (B ^ x) a_Type k).
Proof.
  intros.
  specialize (H x H0).
  apply (DTyping_regularity H).
Qed.

Lemma PiLT : forall S G b A j B k, DTyping S G b (a_Pi A j B) k -> j < k.
intros.
move: (DTyping_regularity H) => h0.
pick fresh y.
eapply DTyping_a_Pi_inversion in h0. split_hyp. auto. eauto.
Qed.

Lemma DTyping_a_Abs_inversion :
  forall x S G b B k, DTyping S G (a_Abs b) B k ->
       x `notin` dom G \u dom S ->
       exists j1 j2 A1 A2,
       DTyping S (x ~ Tm A1 j1 ++ G) (b ^ x) A2 j2 /\
         ((DEquiv S B (a_Arrow A1 A2) /\ j1 = j2 /\ j2 <= k) \/
         (exists A3, (DEquiv S B (a_Pi A1 j1 A3)) /\ A2 = (A3 ^ x)
                     /\ j1 < j2 /\ j1 < k /\ j2 <= k
                     /\ x `notin` fv_tm A3)).
Proof.
  intros.
  dependent induction H.
  + exists k. exists k. exists A. exists B.
    split.
    pick fresh y. spec y.
    eapply DTyping_rename1; eauto.
    left. split; eauto with lc.
  + exists j. exists k. exists A. exists (B ^ x).
    pick fresh y. spec y.
    split.
    eapply DTyping_rename2; eauto.
    right.
    exists B. split; auto with lc.
    eapply DE_Refl; eauto.
    eapply (lc_a_Pi_exists y); eauto with lc.
    repeat split; eauto.
    move: DTyping_fv => [_ [_ h]].
    move: (h _ _ _ _ _ H0) => [f1 f2].
    simpl in f2.
    rewrite <- fv_tm_open_tm_wrt_tm_lower in f2. fsetdec.
  + edestruct IHDTyping1 as [j0 [j2 [A2 [A3 h]]]]. eauto. auto.
    split_hyp.
    have DC: DCtx S (x ~ Tm A2 j0 ++ G). eauto with ctx.
    inversion DC. subst.
    destruct H4.
    ++ exists j0. exists j2. exists A2. exists A3.
       split_hyp. subst.
       split. eapply DT_Conv; eauto.
       eapply DT_Conv; eauto.
       eapply DTyping_regularity; eauto.
       eapply DE_Refl; eauto with lc.
       left. split. eapply DE_Trans; eauto. lia.
    ++ move: H4 => [A4 h].  split_hyp. subst.
       exists j0. exists j2. exists A2. exists (A4 ^ x).
       split.
       auto.
       right.
       exists A4.
       repeat split.
       eapply DE_Trans. eapply DE_Sym. eauto. eauto.
       all: try lia.
    move: DTyping_fv => [_ [_ h]].
    move: (h _ _ _ _ _ H3) => [f1 f2].
    simpl in f2.
    rewrite <- fv_tm_open_tm_wrt_tm_lower in f2. fsetdec.
Unshelve.
all: exact nil.
Qed.

Lemma DTyping_a_App_inversion :
  forall S G b0 b1 B k, DTyping S G (a_App b0 b1) B k ->
    (exists A, DTyping S G b0 (a_Arrow A B) k /\ DTyping S G b1 A k) \/
    (exists j A B0, DTyping S G b0 (a_Pi A j B0) k /\ DTyping S G b1 A j
                    /\ DEquiv S B (open B0 b1)).
Proof.
  intros.
  dependent induction H.
  + left. clear IHDTyping1 IHDTyping2.
    eexists. eauto.
  + right. repeat eexists. eauto. eauto.
    eapply DE_Refl.
    have LC: lc_tm (a_Pi A j B). eauto with lc.
    inversion LC.
    pick fresh x.
    rewrite (subst_tm_intro x); auto.
    eapply subst_tm_lc_tm; eauto with lc.
  + edestruct IHDTyping1; eauto.
    ++ left. move: H2 => [A0 [TA1 TA2]].
       move: (DTyping_regularity TA1) => h.
       apply DTyping_a_Arrow_inversion in h. split_hyp.
       eexists. split.
       eapply DT_Conv. eauto.
       2: { eapply DE_Arrow. eapply DE_Refl. eauto with lc. auto. }
       eapply DT_Arrow; eauto. auto.
    ++ right. move: H2 => [i [A0 [B0 T]]]. split_hyp. subst.
       move: (DTyping_regularity H2) => h.
       pick fresh x.
       eapply DTyping_a_Pi_inversion in h; eauto. split_hyp.
       eexists. eexists. eexists.
       repeat split; eauto.
Unshelve.
all: exact nil.
Qed.

Lemma DTyping_a_Const_inversion :
  forall S G x i B k,
    DTyping S G (a_Const x i) B k ->
    exists a A j,
      j + i <= k /\ binds x (Def A j a) S /\ DEquiv S B (incr i A).
Proof.
  intros.
  dependent induction H.
  + exists a. exists A. exists j.
    repeat split; eauto with lc. lia.
  + edestruct IHDTyping1; eauto.
    rename x0 into a0.
    move: H2 => [A0 [j0 h]]. split_hyp.
    exists a0. exists A0. exists j0.
    repeat split; eauto with lc.
Qed.

Lemma DTyping_a_Type_inversion : forall S G A0 j,
    DTyping S G a_Type A0 j -> DEquiv S a_Type A0.
Proof.
  intros. dependent induction H.
  eauto.
  eapply DE_Trans; eauto.
Qed.

Lemma DTyping_a_Bottom_inversion : forall S G A0 j,
    DTyping S G a_Bottom A0 j -> DEquiv S a_Type A0.
Proof.
  intros. dependent induction H.
  eauto.
  eapply DE_Trans; eauto.
Qed.

Lemma DTyping_a_Absurd_inversion : forall  S G b A k, 
    DTyping S G (a_Absurd b) A k -> 
    DTyping S G b a_Bottom k.
Proof.
  intros. dependent induction H.
  eauto.
  move: (IHDTyping1 b ltac:(eauto)) => h.
  auto.
Qed.
  
