Require Export StraTT.StraTT_inf.
Require Export StraTT.tactics.
Require Export StraTT.basics.
Require Export StraTT.ctx.

Set Implicit Arguments.

Import SubstNotations.
Local Open Scope lc_scope.


(* -------------------------------------------------------------------------- *)

(* Move everything at level j to level k *)
Definition refocus (j k i : nat) :=
  match (i == j) with left _ => k | right _ => i end.

(* float index j in the context to k *)
Definition float j k (G : context) := 
  map (fun '(Tm A i) => Tm A (refocus j k i)) G.                            

Lemma binds_float : forall G x A k k0, 
 binds x (Tm A k) G ->
 binds x (Tm A k0) (float k k0 (restrict G k)).
Proof. 
  intros. unfold float.
  remember (fun '(Tm A0 i) => Tm A0 (refocus k k0 i)) as f.
  replace (Tm A k0) with (f (Tm A k)).
  eapply binds_map_2.
  eapply restrict_binds; auto.
  rewrite Heqf. unfold refocus. rewrite eq_dec_refl. auto.
Qed.

Lemma binds_floatn't : forall G x A j k k0, j < k ->
  binds x (Tm A j) G ->
  binds x (Tm A j) (float k k0 (restrict G k)).
Proof.
  intros. unfold float.
  remember (fun '(Tm A0 i) => Tm A0 (refocus k k0 i)) as f.
  replace (Tm A j) with (f (Tm A j)).
  eapply binds_map_2.
  eapply restrict_binds; auto. lia.
  rewrite Heqf. unfold refocus. f_equal.
  destruct (j == k) eqn:h.
  + lia.
  + rewrite h; auto.
Qed.

(* TRUE but unused. *)
Lemma SubG_restrict : forall i j G, i <= j -> SubG (restrict G j) (restrict G i).
intros. induction G; simpl; auto.
destruct a. destruct a0.
destruct (k <=? j) eqn:E1; destruct (k <=? i) eqn:E2.
all: fix_bools.
all: eauto. 
econstructor; eauto.
econstructor; eauto.
lia.
Qed. 

Lemma SubG_float_lt : forall i j k1 k2 G, 
    i < j -> i <= k2 ->
    SubG (float j k1 (restrict G j)) (float i k2 (restrict G i)).
Proof.
  alist induction G; intros; try destruct a; simpl.
  auto.
  destruct (k <=? j) eqn:E1; destruct (k <=? i) eqn:E2; fix_bools.
  all: simpl.
  all: eauto.
  all: try econstructor; eauto.
  econstructor; eauto.
  + unfold refocus. destruct (k == i) eqn:E3; rewrite E3; destruct (k == j) eqn:E4; rewrite E4.
    lia. lia. lia. auto.
  + lia.
Qed.

(* This is really more of a weakening than a narrowing. *)
Lemma SubG_float_leq : forall i j k G, 
    i <= j -> j <= k -> 
    SubG (float j k (restrict G j)) (float i k (restrict G i)).
Proof. intros j k k0 G. 
       alist induction G; intros; try destruct a; simpl; auto.
       destruct (k1 <=? k) eqn:E1; destruct (k1 <=? j) eqn:E2.
       all: fix_bools.
       all: simpl.
       all: try econstructor; eauto.
       econstructor; eauto.
       + unfold refocus.
         destruct (k1 == k) eqn:E3; rewrite E3;
           destruct (k1 == j) eqn:E4; rewrite E4.
         all: lia.
       + lia.
Qed.

Lemma SubG_float_eq : forall j k G, j <= k ->
  SubG G (float j k (restrict G j)).
Proof.
  intros j k G.
  alist induction G; intros; try destruct a; simpl; auto.
  destruct (k0 <=? j) eqn:E1.
  all: fix_bools.
  all: simpl.
  all: try econstructor; eauto.
  econstructor; eauto.
  unfold refocus.
  destruct (k0 == j) eqn:E2; rewrite E2.
  all: lia.
Qed.

Lemma DCtx_DTyping_float_restrict : 
  (forall S, 
      DSig S -> True) /\
  (forall S G, 
      DCtx S G -> 
      forall j k, 
        j <= k 
        -> DCtx S (float j k (restrict G j))) /\
  (forall S G a A j,
      DTyping S G a A j ->
      (forall k, 
          j <= k 
          -> DTyping S (float j k (restrict G j)) a A k)).
Proof.
  eapply DSig_DCtx_DTyping_ind; intros; eauto.
  (* cons *)
  - rename k into i. 
    rename k0 into k. 
    simpl.
    (* only care about bindings kept by j restriction *)
    destruct (i <=? j) eqn:E; simpl; auto.
    econstructor; eauto.
    unfold refocus.
    destruct (i == j) eqn:F; fix_bools.
    + (* raise index. *)
      move: (H0 k ltac:(lia)) => h0. 
      subst.
      auto.
    + (* leave alone, but raise context *)
      eapply DTyping_SubG.
      eapply H0. lia. auto.
      eapply SubG_float_lt; eauto. lia.
    + rewrite dom_map. rewrite restrict_dom. auto.
  - (* const *)
    have DS: DSig S. eauto with ctx.
    move: (DSig_regularity DS _ _ _ _ b) => [Ta TA].
    eapply DTyping_incr with (j := i) in TA.
    eapply DT_Const; eauto. lia.
  - (* var *)
    destruct (j == k).
    + subst. 
      eapply DT_Var with (j := k0); eauto.
      eapply binds_float; eauto.
    + have * : j < k by lia.
      eapply DT_Var with (j := j); auto.
      eapply binds_floatn't with (k := k) (k0 := k0); auto. lia.
  - (* Pi *) 
    pick fresh x and apply DT_Pi; try lia.
    -- eapply DTyping_SubG with (G:= (float j j (restrict G j))); eauto.
       pick fresh y. spec y. move: (H0 k0 ltac:(auto)) => h0.
       simpl in h0. rewrite leb_correct in h0. lia.
       move: (DTyping_DCtx h0) => DC. inversion DC. subst. auto.
       eapply SubG_float_lt; eauto. 
    -- spec x.
       specialize (H0 k0 ltac:(lia)).
       simpl in H0.
       rewrite leb_correct in H0. lia.
       simpl in H0.
       unfold refocus in H0.
       destruct (j == k) eqn:E. subst. lia. 
       simpl_env in H0. auto.
  - (* AbsTm *)
    pick fresh x and apply DT_AbsTm; eauto.
    spec x.
    specialize (H1 k0 ltac:(lia)). simpl in H1.
    rewrite Nat.leb_refl in H1. simpl in H1.
    replace (refocus k k0 k) with k0 in H1.
    eauto.
    unfold refocus. rewrite eq_dec_refl. auto.
  - pick fresh x and apply DT_AbsTy; eauto; try lia.
    -- eapply DTyping_SubG with (G:= (float j j (restrict G j))); eauto.
       pick fresh y. spec y. move: (H0 k0 ltac:(auto)) => h0.
       simpl in h0. rewrite leb_correct in h0. lia.
       move: (DTyping_DCtx h0) => DC. inversion DC. subst. auto.
       eapply SubG_float_lt; eauto. 
    -- spec x.
       specialize (H0 k0 ltac:(lia)).
       simpl in H0.
       rewrite leb_correct in H0. lia.
       simpl in H0.
       unfold refocus in H0.
       destruct (j == k) eqn:E. subst. lia. 
       simpl_env in H0. auto.
  - eapply DT_AppTy; eauto; try lia.
    eapply DTyping_SubG with (G := (float j j (restrict G j))); eauto.
    move: (H0 k0 ltac:(lia)) => h0.
    eapply DTyping_DCtx; eauto.
    eapply SubG_float_lt; auto.
Qed.

Lemma DTyping_float_restrict : 
  (forall S G a A j,
      DTyping S G a A j ->
      (forall k, 
          j <= k 
          -> DTyping S (float j k (restrict G j)) a A k)).
Proof.
  intros.
  eapply DCtx_DTyping_float_restrict; eauto.
Qed.

Lemma DTyping_float1 :
  forall S G x A b B j k, j <= k ->
    DTyping S G A a_Type k ->
    DTyping S (x ~ Tm A j ++ G) b B j ->
    DTyping S (x ~ Tm A k ++ G) b B k.
Proof.
  intros.
  have ctx : DCtx S (x ~ Tm A j ++ G) by eapply DTyping_DCtx; eauto.
  inversion ctx; subst.
  apply DTyping_float_restrict with (k := k) in H1; auto.
  eapply DTyping_SubG; eauto.
  + simpl. rewrite Nat.leb_refl. simpl.
    unfold refocus. destruct (j == j) eqn: h.
    - rewrite h. simpl_env.
      apply sub_cons; auto.
      apply SubG_float_eq; lia.
    - contradiction.
Qed.


Lemma DTyping_cumul : forall S G a A j k, j <= k ->
  DTyping S G a A j -> DTyping S G a A k.
Proof.
  induction 2; eauto.
  - eapply DT_Const; eauto. lia.
  - eapply DT_Var; eauto. lia.
  - eapply DT_Pi; eauto. lia.
  - eapply DT_AbsTm; eauto. intros.
    eapply DTyping_float1 with (j := k0); auto.
  - eapply DT_AbsTy; eauto. lia.
  - eapply DT_AppTy; eauto. lia.
Qed.

Lemma DCtx_cumul : forall S G x A j k, j <= k ->
  DCtx S (x ~ Tm A j ++ G) ->
  DCtx S (x ~ Tm A k ++ G).
Proof.
  intros.
  inversion H0; subst.
  apply DG_Cons; auto.
  eapply DTyping_cumul; eauto.
Qed.
