Require Export StraTT.incr.

Set Implicit Arguments.

Import SubstNotations.
Local Open Scope lc_scope.

(*
What happens to the judgements when we change the context?

We can restrict the context (see `restrict`)
We can weaken the context
We can narrow and weaken the context

All judgements are stable under increment.

 *)

Lemma DCtx_disjoint : forall S G, DCtx S G -> disjoint S G.
Proof. induction 1; eauto. Qed.

(* ----------------------- all / all2  ---------------------------- *)

(* These take a predicate on terms to a predicate on contexts. *)

Inductive all (P :nat -> Prop) : context -> Prop :=
  | all_nil : all P nil
  | all_cons : forall x A j G, P j -> all P G -> all P (x ~ (Tm A j) ++ G).

#[local] Hint Constructors all : core.

Inductive all2 (P :nat -> nat -> Prop) : context -> context -> Prop :=
  | all2_nil : all2 P nil nil
  | all2_cons : forall x A j1 j2 G1 G2,
      P j1 j2 -> all2 P G1 G2 -> all2 P (x ~ (Tm A j1) ++ G1) (x ~ Tm A j2 ++ G2).

#[local] Hint Constructors all2 : core.

(* If we know that the predicate holds for the context, then we know that
   it holds for all assumptions bound in the context *)

Lemma all_binds : forall P G1 x A i1,
    binds x (Tm A i1) G1 -> all P G1
    -> P i1.
Proof.
  intros P G1.
  induction G1; intros.
  - inversion H.
  - destruct a as [y [B i2]].
    inversion H0. subst.
    move: (binds_cons_1 _ _ _ _ _ _ H) => h.
    destruct h.
    ++ split_hyp. inversion H1. inversion H2. subst.
       auto.
    ++ eauto.
Qed.

Lemma all2_binds : forall P G1 G2 x A i1,
    binds x (Tm A i1) G1 -> all2 P G1 G2
    -> exists i2, binds x (Tm A i2) G2 /\ P i1 i2.
Proof.
  intros P G1.
  induction G1; intros.
  - inversion H.
  - destruct a as [y [B i2]].
    inversion H0. subst.
    move: (binds_cons_1 _ _ _ _ _ _ H) => h.
    destruct h.
    ++ split_hyp. inversion H1. inversion H2. subst.
       exists j2. eauto.
    ++ edestruct IHG1; eauto.
       split_hyp.
       exists x0. eauto.
Qed.

(* we can replace the predicate with something logically weaker *)

Lemma all_weaken : forall (P1 P2 : nat -> Prop) G,
    (forall x, P1 x -> P2 x) -> all P1 G -> all P2 G.
Proof.
  intros. induction H0; eauto.
Qed.

Lemma all2_weaken : forall (P1 P2 : nat -> nat -> Prop) G1 G2,
    (forall x y, P1 x y -> P2 x y) -> all2 P1 G1 G2 -> all2 P2 G1 G2.
Proof.
  intros. induction H0; eauto.
Qed.

(* --------------- restrict ---------------- *)

Fixpoint restrict (G:context) k :=
  match G with
  | nil => nil
  | (x,Tm A j)::G' => if j <=? k then (x, Tm A j) :: restrict G' k else restrict G' k
  end.

Lemma restrict_dom : forall k G, dom (restrict G k) [<=] dom G.
Proof. intros k G; induction G; simpl; auto.
fsetdec.
destruct a; destruct a0.
destruct (k0 <=? k). simpl_env. fsetdec. fsetdec.
Qed.

#[global] Hint Rewrite restrict_dom : rewr_list.

Lemma restrict_binds : forall x A k G k0,
  binds x (Tm A k) G ->
  k <= k0 ->
  binds x (Tm A k) (restrict G k0).
Proof.
  intros.
  alist induction G; simpl; try destruct a; auto.
  destruct (binds_cons_1 _ _ _ _ _ _ H).
  split_hyp. inversion H2. subst.
  rewrite leb_correct; auto.
  destruct (k1 <=? k0);  eauto.
Qed.

#[local] Hint Resolve restrict_binds : core.

(* Lemma 11 (restriction) in the paper *)
Lemma DSig_DCtx_DTyping_restriction :
  (forall S, DSig S -> True) /\
  (forall S G, DCtx S G -> forall k, DCtx S (restrict G k)) /\
  (forall S G a A j, DTyping S G a A j -> forall k, j <= k -> DTyping S (restrict G k) a A j).
Proof.
eapply DSig_DCtx_DTyping_ind; intros; subst; eauto.
- simpl. destruct (k <=? k0) eqn:E.
  + rewrite Nat.leb_le in E.
    econstructor; eauto. rewrite restrict_dom. auto.
  + eauto.
- eapply DT_Var; eauto.
  apply restrict_binds; eauto. lia.
- have h: j <= k0 by lia.
  pick fresh y and apply DT_Pi; eauto.
  spec y.
  specialize (H0 k0 ltac:(lia)).
  simpl in H0.
  rewrite leb_correct in H0; auto.
- pick fresh y and apply DT_AbsTm; eauto.
  spec y.
  specialize (H1 k0 ltac:(lia)).
  simpl in H1.
  rewrite leb_correct in H1; auto.
- have h: j <= k0 by lia.
  pick fresh y and apply DT_AbsTy; eauto.
  spec y.
  specialize (H0 k0 ltac:(lia)).
  simpl in H0.
  rewrite leb_correct in H0; auto.
- have h: j <= k0 by lia.
  eapply DT_AppTy; eauto.
Qed.

Lemma DTyping_restrict :
  (forall S G a A j, DTyping S G a A j -> forall k, j <= k -> DTyping S (restrict G k) a A j).
eapply  DSig_DCtx_DTyping_restriction .
Qed.

Lemma DCtx_restrict :
  (forall S G, DCtx S G -> forall k, DCtx S (restrict G k)).
eapply DSig_DCtx_DTyping_restriction.
Qed.

(* ----------------------- inversion for DCtx ---------------------- *)

Lemma DCtx_app : forall S E F, DCtx S (E ++ F) -> DCtx S F.
Proof.
  induction E; intros; simpl_env in *; auto.
  inversion H; eauto.
Qed.

(* ----------------------- weakening ---------------------------- *)

Lemma DSig_DEquiv_weakening :
  forall S A B, DEquiv S A B ->
            forall F, DSig (F ++ S) ->
                      DEquiv (F ++ S) A B.
Proof.
  induction 1; eauto.
Qed.

Lemma DSig_DCtx_DTyping_weakening :
  (forall S,
    DSig S -> True) /\
  (forall S G,
    DCtx S G -> forall F, DSig (F ++ S) -> disjoint (F ++ S) G ->
    DCtx (F ++ S) G) /\
  (forall S G a A j,
    DTyping S G a A j -> forall F, DSig (F ++ S) -> disjoint (F ++ S) G ->
    DTyping (F ++ S) G a A j).
Proof.
  eapply DSig_DCtx_DTyping_ind; auto.
  all: intros; eauto using DSig_DEquiv_weakening.
  all: destruct_uniq.
  econstructor; eauto.
  pick fresh x and apply DT_Pi; eauto.
  spec x. eapply H0; auto.
  pick fresh x and apply DT_AbsTm; eauto.
  spec x. eapply H1; auto.
  pick fresh x and apply DT_AbsTy; eauto.
  spec x. eapply H0; auto.
Qed.

Lemma DSig_DCtx_weakening :
  (forall S G ,
    DCtx S G  -> forall F, DSig (F ++ S) -> disjoint (F ++ S) G ->
    DCtx (F ++ S) G ).
Proof.
  intros.
  eapply DSig_DCtx_DTyping_weakening; eauto.
Qed.

Lemma DSig_DTyping_weakening :
  (forall S G a A j,
    DTyping S G a A j -> forall F, DSig (F ++ S) -> disjoint (F ++ S) G ->
    DTyping (F ++ S) G a A j).
Proof.
  intros.
  eapply DSig_DCtx_DTyping_weakening; eauto.
Qed.

Lemma DTyping_weakening :
  forall S F E a A j,
    DTyping S (F ++ E) a A j -> forall G, DCtx S (F ++ G ++ E)  ->
    DTyping S (F ++ G ++ E) a A j.
Proof.
  intros.
  dependent induction H.
  all: eauto.
  - pick fresh x and apply DT_Pi; eauto.
    spec x.
    match goal with [ |- DTyping S (x ~ ?a ++ ?F ++ ?G ++ ?E) _ _ _ ] =>
       specialize (H1 ((x ~ a) ++ F) E);  apply H1 end.
    reflexivity.
    eapply DG_Cons; eauto.
  - pick fresh x and apply DT_AbsTm; auto.
    repeat spec x.
    match goal with [ H2 : forall F E : list (atom * assn), _ |- DTyping S (x ~ ?a ++ ?F ++ ?G ++ ?E) _ _ _ ] =>
       specialize (H2 ((x ~ a) ++ F) E);
       apply H2 end.
    reflexivity.
    simpl_env.
    eapply DG_Cons; auto.
  - pick fresh x and apply DT_AbsTy; auto.
    repeat spec x.
    match goal with [ H2 : forall F E : list (atom * assn), _ |- DTyping S (x ~ ?a ++ ?F ++ ?G ++ ?E) _ _ _ ] =>
       specialize (H2 ((x ~ a) ++ F) E);
       apply H2 end.
    reflexivity.
    simpl_env.
    eapply DG_Cons; auto.
Qed.

Lemma DTyping_weakening1 :
  forall S F E a A j,
    DTyping S E a A j -> DCtx S (F ++ E) ->
    DTyping S (F ++ E) a A j.
Proof.
  intros.
  eapply DTyping_weakening with (F:=nil);
  eauto.
Qed.

(* ------------------------------ Ctx regularity --------------------- *)

Lemma DSig_regularity : forall S, DSig S -> forall x a k A,
      binds x (Def A k a) S ->
      DTyping S nil a A k /\ DTyping S nil A a_Type k.
Proof.
  induction 1; intros.
  inversion H.
  match goal with [ H2 : binds ?x ?a1 (?y ~ ?a2 ++ ?G) |- _ ] =>
                    apply binds_cons_1 in H2;
                    destruct H2 as [[e1 e2]|b0]; first inversion e2; subst end.
  all: try split.
  eapply DSig_DTyping_weakening; eauto.
  eapply DSig_DTyping_weakening; eauto.
  edestruct IHDSig; eauto.
  eapply DSig_DTyping_weakening; eauto.
  edestruct IHDSig; eauto.
  eapply DSig_DTyping_weakening; eauto.
Qed.

Lemma DCtx_regularity : forall S G, DCtx S G -> forall x A k,
  binds x (Tm A k) G ->
  DTyping S G A a_Type k.
Proof. induction 1; intros.
       all: try match goal with [ H : binds ?x ?a ?nil |- _ ] => inversion H end.
       all: try match goal with [ H2 : binds ?x ?a1 (?y ~ ?a2 ++ ?G) |- _ ] =>
                           apply binds_cons_1 in H2;
                           destruct H2 as [[e1 e2]|b0]; first inversion e2; subst end.
       all: try match goal with [ H : (_,_) = (_,_) |- _ ] => inversion H ; subst; clear H end.
       all: eauto using DTyping_weakening1.
Qed.

(* Lemma 9 (regularity) in the paper *)
Lemma DCtx_DSig : forall S G, DCtx S G -> DSig S.
Proof. induction 1; auto. Qed.
Lemma DTyping_DCtx : forall S G a A k, DTyping S G a A k -> DCtx S G.
Proof. induction 1; auto. Qed.

#[export] Hint Resolve DCtx_DSig DTyping_DCtx : ctx.

(* ----------- Can narrow the variables in the context (and weaken) ------------------------ *)

Inductive SubA : assn -> assn -> Prop :=
  | sub_Tm : forall A j k, j <= k -> SubA (Tm A j) (Tm A k).

Inductive SubG : context -> context -> Prop :=
  | sub_nil : SubG nil nil
  | sub_cons : forall x a1 a2 G1 G2,
      SubG G1 G2 ->
      SubA a1 a2 ->
      SubG ((x ~ a1) ++ G1) ((x ~ a2) ++ G2)
  | sub_weak : forall x a G1 G2,
      SubG G1 G2 ->
      SubG ((x ~ a) ++ G1) G2.

#[export] Hint Constructors SubA SubG : core.

Lemma SubA_refl : forall A, SubA A A.
Proof.
intro a. destruct a; eauto with ctx.
Qed.

Lemma SubG_refl : forall G, SubG G G.
Proof. induction G; eauto with ctx.
destruct a. econstructor; eauto using SubA_refl.
Qed.

Lemma SubG_dom : forall G1 G2, SubG G1 G2 -> dom G2 [<=] dom G1.
Proof. induction 1; eauto; simpl; try fsetdec. Qed.

Lemma SubG_uniq : forall G1 G2, SubG G1 G2 -> uniq G1 -> uniq G2.
Proof.
  induction 1; eauto. intros. destruct_uniq.
  move: (SubG_dom H) => h. solve_uniq.
  intros. destruct_uniq.
  move: (SubG_dom H) => h. solve_uniq.
Qed.

Lemma SubG_app: forall F1 G1,
    SubG F1 G1 -> forall F2 G2, SubG F2 G2 -> SubG (F1 ++ F2) (G1 ++ G2).
Proof.
  induction 1. simpl. auto.
  intros.
  simpl_env.
  econstructor. eauto. auto.
  econstructor. eauto.
Qed.

Lemma SubG_binds : forall G1 G2,
    SubG G2 G1 ->
    forall x a1, binds x a1 G1 -> exists a2, binds x a2 G2 /\ SubA a2 a1.
Proof.
  induction 1. intros. inversion H.
  intros.
  match goal with [ H1 : binds ?x _ _ |- _ ] =>
                    apply binds_cons_1 in H1;
                    destruct H1 as [[e1 e2] | b0] end.
 inversion e2. subst. eauto.
 edestruct IHSubG; eauto.
 destruct H1. exists x1. split; eauto.
 intros.
 edestruct IHSubG; eauto. split_hyp. exists x1.  split; eauto.
Qed.

(* Lemma 7 (weakening) in the paper *)
Lemma DTyping_SubG :
  forall S G a A k, DTyping S G a A k -> forall G', DCtx S G' -> SubG G' G -> DTyping S G' a A k.
Proof.
  induction 1; intros; eauto with ctx lngen.
  - (* var case *)
    match goal with [b : binds _ _ _  |- _ ] => eapply SubG_binds in b;
                                              eauto; destruct b as [j1 [bj le]] end.
    inversion le. subst. clear le.
    eapply DT_Var; eauto. lia.
  - (* Pi case *)
    pick fresh x and apply DT_Pi; eauto with ctx.
    repeat spec x.
    eapply H1. eauto using DTyping_DCtx. econstructor; eauto using SubA_refl.
  - (* absTm case *)
    pick fresh x and apply DT_AbsTm; eauto with ctx.
    repeat spec x.
    eapply H2. econstructor; eauto using DTyping_DCtx.
    econstructor; eauto using SubA_refl.
  - (* absTy case *)
    pick fresh x and apply DT_AbsTy; eauto with ctx.
    repeat spec x.
    eapply H1. econstructor; eauto using DTyping_DCtx.
    econstructor; eauto using SubA_refl.
Unshelve.
exact 0.
Qed.
