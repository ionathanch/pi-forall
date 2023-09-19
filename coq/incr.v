Require Export StraTT.basics.

Set Implicit Arguments.

(* --------------- Properties about the increment operation -------------------- *)

(* incr 0 is an identity function *)
Lemma incr_refl : forall a, incr 0 a = a.
Proof.
  induction a; simpl; f_equal; eauto.
Qed.

(* successive increments can be combined *)
Lemma incr_incr : forall a j k, incr j (incr k a) = incr (j + k) a.
  intros a.
  dependent induction a. 
  all: intros j0 k0.
  all: simpl.
  all: try solve [f_equal; auto; try lia].
Qed.

(* does not change the size of the term *)
Lemma size_incr : forall a j, size_tm (incr j a) <= size_tm a.
Proof. induction a; intros j0;  simpl.
       all: try lia.
       all: try specialize (IHa1 j0).
       all: try specialize (IHa2 j0). 
       all: try specialize (IHa j0). 
       all: try unfold size_nat. 
       all: try lia.
Qed.
       
(* incr commutes with substitution *)
Lemma subst_tm_incr : forall A k B x, 
    subst_tm (incr k B) x (incr k A) = incr k (subst_tm B x A).
Proof. 
  induction A; intros; simpl; f_equal; auto.
  destruct (x == x0); simpl; auto.
Qed.


(* ------------------------------ Judgements stable under increment  --------------------- *)

Definition inc_assn k := fun s => 
                           match s with 
                           | Tm A j => Tm (incr k A) (k + j) 
                           end.
  
Definition IncG k (G : context) := map (inc_assn k) G.

Lemma DEquiv_incr : forall S A B j,  DEquiv S A B ->
  DEquiv S (incr j A) (incr j B).
Proof.
  induction 1; simpl; eauto with lc.
  - (* beta *)
    rewrite incr_open.
    eapply DE_Beta; eauto with lc.
    inversion H.
    apply lc_a_Abs. intro x. specialize (H2 x).
    replace (a_Var_f x) with (incr j (a_Var_f x)).
    rewrite <- incr_open.
    apply lc_incr.
    auto.
    reflexivity.
  - pick fresh x and apply DE_Eta.
    spec x.
    replace (a_Var_f x) with (incr j (a_Var_f x)).
    rewrite <- incr_open.
    rewrite H.
    reflexivity.
    reflexivity.
    eauto with lc.
  - rewrite incr_incr. eauto.
  - pick fresh x and apply DE_Pi; auto.
    repeat spec x.
    repeat rewrite incr_open in H1.
    simpl in H1.
    auto.
  - pick fresh x and apply DE_Abs; auto.
    spec x.
    repeat rewrite incr_open in H0.
    simpl in H0.
    auto.
Qed.

Lemma incr_binds :
  forall x A j G i,
    binds x (Tm A j) G ->
    binds x (Tm (incr i A) (i + j)) (IncG i G).
Proof.
  intros.
  alist induction G; simpl; auto.
  destruct (binds_cons_1 _ _ _ _ _ _ H) as [[xeq Tmeq] | bindsG];
  subst; auto.
Qed.

Lemma DTyping_DCtx_incr : 
  (forall S, DSig S -> True) /\
  (forall S G, DCtx S G -> forall j, DCtx S (IncG j G)) /\
  (forall S G a A k, DTyping S G a A k -> forall j, DTyping S (IncG j G) (incr j a) (incr j A) (j + k)).
Proof.                                              
  eapply DSig_DCtx_DTyping_ind.
  all: intros; simpl; simpl_env; eauto.
  all: repeat match goal with [ H : forall j:Datatypes.nat, _ , j : Datatypes.nat |- _ ] => specialize (H j) end.
  all: unfold IncG in *.
  all: simpl in *. simpl_env in *.
  - (* ctx cons *)
    econstructor; eauto.
  - (* const *)
    rewrite incr_incr.
    econstructor; eauto. lia.
  - (* var case *)
    eapply DT_Var with (j := j0 + j); eauto.
    eapply incr_binds; eauto.
    lia.
  - (* pi case *)
    pick fresh x and apply DT_Pi. 
    eauto.
    replace (a_Var_f x) with (incr j0 (a_Var_f x)); auto.
    rewrite <- incr_open.
    repeat spec x.
    simpl; eauto.
    lia.
  - (* abs *)
    pick fresh x and apply DT_AbsTm; eauto.
    + replace (a_Var_f x) with (incr j (a_Var_f x)); auto.
    repeat rewrite <- incr_open.
    repeat spec x.
    simpl; eauto. 
  - (* abs *)
    pick fresh x and apply DT_AbsTy; eauto.
    + replace (a_Var_f x) with (incr j0 (a_Var_f x)); auto.
    repeat rewrite <- incr_open.
    repeat spec x.
    simpl; eauto. 
    + lia.
  - (* app *)
    rewrite incr_open.
    eapply DT_AppTy; eauto.
    lia.
  - (* conv *)
    eapply DT_Conv; eauto.
    eapply DEquiv_incr; eauto.
Qed.

Lemma DCtx_incr : forall S G, DCtx S G -> forall j, DCtx S (IncG j G).
Proof. eapply DTyping_DCtx_incr; eauto. Qed.

Lemma DTyping_incr : forall S G a A k, DTyping S G a A k -> forall j, DTyping S (IncG j G) (incr j a) (incr j A) (j + k).
Proof. eapply DTyping_DCtx_incr; eauto. Qed.


