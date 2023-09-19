(* generated by Ott 0.33, locally-nameless lngen from: ./StraTT.ott *)
Require Import Metalib.Metatheory.
  Require Export Metalib.LibLNgen.
  
(** syntax *)
Definition n : Set := nat.

Inductive tm : Set :=  (*r terms and types *)
 | a_Type : tm (*r universe *)
 | a_Arrow (A:tm) (B:tm) (*r nondependent function type *)
 | a_Pi (A:tm) (j:nat) (B:tm) (*r dependent function type *)
 | a_Abs (a:tm) (*r function *)
 | a_App (a:tm) (b:tm) (*r application *)
 | a_Bottom : tm (*r empty type *)
 | a_Absurd (b:tm) (*r ex falso quodlibet *)
 | a_Var_b (_:nat) (*r variable *)
 | a_Var_f (x:var) (*r variable *)
 | a_Const (x:var) (i:nat) (*r displaced constants *).

Inductive clos : Set := 
.

Inductive def : Set :=  (*r signature definitions *)
 | Def (A:tm) (k:nat) (a:tm).

Inductive assn : Set :=  (*r context assumptions *)
 | Tm (A:tm) (k:nat).

Inductive value : Set := 
 | v_Lift (A:tm) (ne5:ne)
 | v_Abs (cl:clos)
 | v_Pi (v:value) (cl:clos)
 | v_Type : value
with nf : Set := 
 | nf_Lower (A:tm) (v:value)
with ne : Set := 
 | ne_IVar (i:nat)
 | ne_App (ne5:ne) (nf5:nf).

Definition signature : Set := list ( atom * def ).

Definition context : Set := list ( atom * assn ).

Definition env : Set := list value.

Definition nat : Set := nat.

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_tm_wrt_tm_rec (k:nat) (A5:tm) (A_6:tm) {struct A_6}: tm :=
  match A_6 with
  | a_Type => a_Type 
  | (a_Arrow A B) => a_Arrow (open_tm_wrt_tm_rec k A5 A) (open_tm_wrt_tm_rec k A5 B)
  | (a_Pi A j B) => a_Pi (open_tm_wrt_tm_rec k A5 A) j (open_tm_wrt_tm_rec (S k) A5 B)
  | (a_Abs a) => a_Abs (open_tm_wrt_tm_rec (S k) A5 a)
  | (a_App a b) => a_App (open_tm_wrt_tm_rec k A5 a) (open_tm_wrt_tm_rec k A5 b)
  | a_Bottom => a_Bottom 
  | (a_Absurd b) => a_Absurd (open_tm_wrt_tm_rec k A5 b)
  | (a_Var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => a_Var_b nat
        | inleft (right _) => A5
        | inright _ => a_Var_b (nat - 1)
      end
  | (a_Var_f x) => a_Var_f x
  | (a_Const x i) => a_Const x i
end.

Fixpoint open_ne_wrt_tm_rec (k:nat) (A5:tm) (ne_6:ne) {struct ne_6}: ne :=
  match ne_6 with
  | (ne_IVar i) => ne_IVar i
  | (ne_App ne5 nf5) => ne_App (open_ne_wrt_tm_rec k A5 ne5) (open_nf_wrt_tm_rec k A5 nf5)
end
with open_nf_wrt_tm_rec (k:nat) (A5:tm) (nf5:nf) : nf :=
  match nf5 with
  | (nf_Lower A v) => nf_Lower (open_tm_wrt_tm_rec k A5 A) (open_value_wrt_tm_rec k A5 v)
end
with open_value_wrt_tm_rec (k:nat) (A5:tm) (v5:value) {struct v5}: value :=
  match v5 with
  | (v_Lift A ne5) => v_Lift (open_tm_wrt_tm_rec k A5 A) (open_ne_wrt_tm_rec k A5 ne5)
  | (v_Abs cl) => v_Abs cl
  | (v_Pi v cl) => v_Pi (open_value_wrt_tm_rec k A5 v) cl
  | v_Type => v_Type 
end.

Definition open_def_wrt_tm_rec (k:nat) (A5:tm) (def5:def) : def :=
  match def5 with
  | (Def A k a) => Def (open_tm_wrt_tm_rec k A5 A) k (open_tm_wrt_tm_rec k A5 a)
end.

Definition open_assn_wrt_tm_rec (k:nat) (A5:tm) (assn5:assn) : assn :=
  match assn5 with
  | (Tm A k) => Tm (open_tm_wrt_tm_rec k A5 A) k
end.

Definition open_ne_wrt_tm A5 ne_6 := open_ne_wrt_tm_rec 0 ne_6 A5.

Definition open_nf_wrt_tm A5 nf5 := open_nf_wrt_tm_rec 0 nf5 A5.

Definition open_value_wrt_tm A5 v5 := open_value_wrt_tm_rec 0 v5 A5.

Definition open_def_wrt_tm A5 def5 := open_def_wrt_tm_rec 0 def5 A5.

Definition open_assn_wrt_tm A5 assn5 := open_assn_wrt_tm_rec 0 assn5 A5.

Definition open_tm_wrt_tm A5 A_6 := open_tm_wrt_tm_rec 0 A_6 A5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_tm *)
Inductive lc_tm : tm -> Prop :=    (* defn lc_tm *)
 | lc_a_Type : 
     (lc_tm a_Type)
 | lc_a_Arrow : forall (A B:tm),
     (lc_tm A) ->
     (lc_tm B) ->
     (lc_tm (a_Arrow A B))
 | lc_a_Pi : forall (A:tm) (j:nat) (B:tm),
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     (lc_tm (a_Pi A j B))
 | lc_a_Abs : forall (a:tm),
      ( forall x , lc_tm  ( open_tm_wrt_tm a (a_Var_f x) )  )  ->
     (lc_tm (a_Abs a))
 | lc_a_App : forall (a b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm (a_App a b))
 | lc_a_Bottom : 
     (lc_tm a_Bottom)
 | lc_a_Absurd : forall (b:tm),
     (lc_tm b) ->
     (lc_tm (a_Absurd b))
 | lc_a_Var_f : forall (x:var),
     (lc_tm (a_Var_f x))
 | lc_a_Const : forall (x:var) (i:nat),
     (lc_tm (a_Const x i)).

(* defns LC_def *)
Inductive lc_def : def -> Prop :=    (* defn lc_def *)
 | lc_Def : forall (A:tm) (k:nat) (a:tm),
     (lc_tm A) ->
     (lc_tm a) ->
     (lc_def (Def A k a)).

(* defns LC_assn *)
Inductive lc_assn : assn -> Prop :=    (* defn lc_assn *)
 | lc_Tm : forall (A:tm) (k:nat),
     (lc_tm A) ->
     (lc_assn (Tm A k)).

(* defns LC_ne_nf_value *)
Inductive lc_ne : ne -> Prop :=    (* defn lc_ne *)
 | lc_ne_IVar : forall (i:nat),
     (lc_ne (ne_IVar i))
 | lc_ne_App : forall (ne5:ne) (nf5:nf),
     (lc_ne ne5) ->
     (lc_nf nf5) ->
     (lc_ne (ne_App ne5 nf5))
with lc_nf : nf -> Prop :=    (* defn lc_nf *)
 | lc_nf_Lower : forall (A:tm) (v:value),
     (lc_tm A) ->
     (lc_value v) ->
     (lc_nf (nf_Lower A v))
with lc_value : value -> Prop :=    (* defn lc_value *)
 | lc_v_Lift : forall (A:tm) (ne5:ne),
     (lc_tm A) ->
     (lc_ne ne5) ->
     (lc_value (v_Lift A ne5))
 | lc_v_Abs : forall (cl:clos),
     (lc_value (v_Abs cl))
 | lc_v_Pi : forall (v:value) (cl:clos),
     (lc_value v) ->
     (lc_value (v_Pi v cl))
 | lc_v_Type : 
     (lc_value v_Type).
(** free variables *)
Fixpoint fv_tm (A5:tm) : vars :=
  match A5 with
  | a_Type => {}
  | (a_Arrow A B) => (fv_tm A) \u (fv_tm B)
  | (a_Pi A j B) => (fv_tm A) \u (fv_tm B)
  | (a_Abs a) => (fv_tm a)
  | (a_App a b) => (fv_tm a) \u (fv_tm b)
  | a_Bottom => {}
  | (a_Absurd b) => (fv_tm b)
  | (a_Var_b nat) => {}
  | (a_Var_f x) => {{x}}
  | (a_Const x i) => {}
end.

Fixpoint fv_ne (ne_6:ne) : vars :=
  match ne_6 with
  | (ne_IVar i) => {}
  | (ne_App ne5 nf5) => (fv_ne ne5) \u (fv_nf nf5)
end
with fv_nf (nf5:nf) : vars :=
  match nf5 with
  | (nf_Lower A v) => (fv_tm A) \u (fv_value v)
end
with fv_value (v5:value) : vars :=
  match v5 with
  | (v_Lift A ne5) => (fv_tm A) \u (fv_ne ne5)
  | (v_Abs cl) => {}
  | (v_Pi v cl) => (fv_value v)
  | v_Type => {}
end.

Definition fv_def (def5:def) : vars :=
  match def5 with
  | (Def A k a) => (fv_tm A) \u (fv_tm a)
end.

Definition fv_assn (assn5:assn) : vars :=
  match assn5 with
  | (Tm A k) => (fv_tm A)
end.

(** substitutions *)
Fixpoint subst_tm (A5:tm) (x5:var) (A_6:tm) {struct A_6} : tm :=
  match A_6 with
  | a_Type => a_Type 
  | (a_Arrow A B) => a_Arrow (subst_tm A5 x5 A) (subst_tm A5 x5 B)
  | (a_Pi A j B) => a_Pi (subst_tm A5 x5 A) j (subst_tm A5 x5 B)
  | (a_Abs a) => a_Abs (subst_tm A5 x5 a)
  | (a_App a b) => a_App (subst_tm A5 x5 a) (subst_tm A5 x5 b)
  | a_Bottom => a_Bottom 
  | (a_Absurd b) => a_Absurd (subst_tm A5 x5 b)
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => (if eq_var x x5 then A5 else (a_Var_f x))
  | (a_Const x i) => a_Const x i
end.

Fixpoint subst_ne (A5:tm) (x5:var) (ne_6:ne) {struct ne_6} : ne :=
  match ne_6 with
  | (ne_IVar i) => ne_IVar i
  | (ne_App ne5 nf5) => ne_App (subst_ne A5 x5 ne5) (subst_nf A5 x5 nf5)
end
with subst_nf (A5:tm) (x5:var) (nf5:nf) {struct nf5} : nf :=
  match nf5 with
  | (nf_Lower A v) => nf_Lower (subst_tm A5 x5 A) (subst_value A5 x5 v)
end
with subst_value (A5:tm) (x5:var) (v5:value) {struct v5} : value :=
  match v5 with
  | (v_Lift A ne5) => v_Lift (subst_tm A5 x5 A) (subst_ne A5 x5 ne5)
  | (v_Abs cl) => v_Abs cl
  | (v_Pi v cl) => v_Pi (subst_value A5 x5 v) cl
  | v_Type => v_Type 
end.

Definition subst_def (A5:tm) (x5:var) (def5:def) : def :=
  match def5 with
  | (Def A k a) => Def (subst_tm A5 x5 A) k (subst_tm A5 x5 a)
end.

Definition subst_assn (A5:tm) (x5:var) (assn5:assn) : assn :=
  match assn5 with
  | (Tm A k) => Tm (subst_tm A5 x5 A) k
end.


Fixpoint incr (k:nat) (a_6:tm) {struct a_6}: tm :=
  match a_6 with
  | a_Type        => a_Type
  | (a_Arrow A B) => a_Arrow (incr k A) (incr k B)
  | (a_Pi A j B)  => a_Pi (incr k A) (k + j) (incr k B)
  | (a_Abs a)     => a_Abs (incr k a)
  | (a_App a b)   => a_App (incr k a) (incr k b)
  | a_Bottom      => a_Bottom
  | (a_Absurd a)  => a_Absurd (incr k a)
  | (a_Var_b i)   => a_Var_b i
  | (a_Var_f x)   => a_Var_f x
  | (a_Const x i) => a_Const x (k + i)
end.



(** definitions *)

(* defns JEq *)
Inductive Equiv : tm -> tm -> Prop :=    (* defn Equiv *)
 | E_Refl : forall (a:tm),
     lc_tm a ->
     Equiv a a
 | E_Sym : forall (a b:tm),
     Equiv b a ->
     Equiv a b
 | E_Trans : forall (a c b:tm),
     Equiv a b ->
     Equiv b c ->
     Equiv a c
 | E_Beta : forall (b a:tm),
     lc_tm (a_Abs b) ->
     lc_tm a ->
     Equiv (a_App  ( (a_Abs b) )  a)  (open_tm_wrt_tm  b   a ) 
 | E_Eta : forall (L:vars) (b' b:tm),
      ( forall x , x \notin  L  ->   ( open_tm_wrt_tm b' (a_Var_f x) )   =  (a_App b (a_Var_f x))  )  ->
     Equiv (a_Abs b') b
 | E_Arrow : forall (A B A' B':tm),
     Equiv A A' ->
     Equiv B B' ->
     Equiv (a_Arrow A B) (a_Arrow A' B')
 | E_Pi : forall (L:vars) (A:tm) (k:nat) (B A' B':tm),
     Equiv A A' ->
      ( forall x , x \notin  L  -> Equiv  ( open_tm_wrt_tm B (a_Var_f x) )   ( open_tm_wrt_tm B' (a_Var_f x) )  )  ->
     Equiv (a_Pi A k B) (a_Pi A' k B')
 | E_Abs : forall (L:vars) (b b':tm),
      ( forall x , x \notin  L  -> Equiv  ( open_tm_wrt_tm b (a_Var_f x) )   ( open_tm_wrt_tm b' (a_Var_f x) )  )  ->
     Equiv (a_Abs b) (a_Abs b')
 | E_App : forall (b a b' a':tm),
     Equiv a a' ->
     Equiv b b' ->
     Equiv (a_App b a) (a_App b' a')
 | E_Absurd : forall (b b':tm),
     Equiv b b' ->
     Equiv (a_Absurd b) (a_Absurd b').

(* defns JTyping *)
Inductive Ctx : context -> Prop :=    (* defn Ctx *)
 | G_Empty : 
     Ctx  nil 
 | G_Cons : forall (G:context) (x:var) (A:tm) (k:nat),
     Ctx G ->
     Typing G A a_Type k ->
      ~ AtomSetImpl.In  x  (dom  G )  ->
     Ctx  (  ( x ~ (Tm A k) )  ++ G ) 
with Typing : context -> tm -> tm -> nat -> Prop :=    (* defn Typing *)
 | T_Type : forall (G:context) (k:nat),
     Ctx G ->
     Typing G a_Type a_Type k
 | T_Var : forall (G:context) (x:var) (A:tm) (k j:nat),
      binds  x  (Tm  A j )  G  ->
     Ctx G ->
      j  <=  k  ->
     Typing G (a_Var_f x) A k
 | T_Arrow : forall (G:context) (A B:tm) (k:nat),
     Typing G A a_Type k ->
     Typing G B a_Type k ->
     Typing G (a_Arrow A B) a_Type k
 | T_Pi : forall (L:vars) (G:context) (A:tm) (j:nat) (B:tm) (k:nat),
     Typing G A a_Type j ->
      ( forall x , x \notin  L  -> Typing  (  ( x ~ (Tm A j) )  ++ G )   ( open_tm_wrt_tm B (a_Var_f x) )  a_Type k )  ->
      j  <  k  ->
     Typing G (a_Pi A j B) a_Type k
 | T_AbsTm : forall (L:vars) (G:context) (b A B:tm) (k:nat),
     Typing G A a_Type k ->
     Typing G B a_Type k ->
      ( forall x , x \notin  L  -> Typing  (  ( x ~ (Tm A k) )  ++ G )   ( open_tm_wrt_tm b (a_Var_f x) )  B k )  ->
     Typing G (a_Abs b) (a_Arrow A B) k
 | T_AbsTy : forall (L:vars) (G:context) (b A:tm) (j:nat) (B:tm) (k:nat),
     Typing G A a_Type j ->
      ( forall x , x \notin  L  -> Typing  (  ( x ~ (Tm A j) )  ++ G )   ( open_tm_wrt_tm b (a_Var_f x) )   ( open_tm_wrt_tm B (a_Var_f x) )  k )  ->
      j  <  k  ->
     Typing G (a_Abs b) (a_Pi A j B) k
 | T_AppTm : forall (G:context) (b a B:tm) (k:nat) (A:tm),
     Typing G b (a_Arrow A B) k ->
     Typing G a A k ->
     Typing G (a_App b a) B k
 | T_AppTy : forall (G:context) (b a B:tm) (k:nat) (A:tm) (j:nat),
     Typing G b (a_Pi A j B) k ->
     Typing G a A j ->
     Typing G (a_App b a)  (open_tm_wrt_tm  B   a )  k
 | T_Bottom : forall (G:context) (k:nat),
     Ctx G ->
     Typing G a_Bottom a_Type k
 | T_Absurd : forall (G:context) (b A:tm) (k:nat),
     Typing G A a_Type k ->
     Typing G b a_Bottom k ->
     Typing G (a_Absurd b) A k
 | T_Cumul : forall (G:context) (a B:tm) (k:nat) (A:tm),
     Typing G a A k ->
     Typing G B a_Type k ->
     Equiv A B ->
     Ctx G ->
     Typing G a B k.

(* defns JFakeTyping *)
Inductive FakeTyping : context -> tm -> tm -> nat -> Prop :=    (* defn FakeTyping *)
 | U_AbsTy : forall (L:vars) (G:context) (b A B:tm) (k j:nat),
     Typing G A a_Type j ->
      ( forall x , x \notin  L  -> Typing  (  ( x ~ (Tm A j) )  ++ G )   ( open_tm_wrt_tm b (a_Var_f x) )  B k )  ->
      j  <  k  ->
     FakeTyping G (a_Abs b)  (a_Pi  A  0  B )  k
 | U_Pi : forall (G:context) (x:var) (A B:tm) (k j:nat),
     Typing G A a_Type j ->
     Typing  (  ( x ~ (Tm A j) )  ++ G )  B a_Type k ->
      j  <  k  ->
     FakeTyping G  (a_Pi  A  0  B )  a_Type k.

(* defns JDEq *)
Inductive DEquiv : signature -> tm -> tm -> Prop :=    (* defn DEquiv *)
 | DE_Refl : forall (S:signature) (a:tm),
     lc_tm a ->
     DEquiv S a a
 | DE_Sym : forall (S:signature) (a b:tm),
     DEquiv S b a ->
     DEquiv S a b
 | DE_Trans : forall (S:signature) (a c b:tm),
     DEquiv S a b ->
     DEquiv S b c ->
     DEquiv S a c
 | DE_Beta : forall (S:signature) (b a:tm),
     lc_tm (a_Abs b) ->
     lc_tm a ->
     DEquiv S (a_App  ( (a_Abs b) )  a)  (open_tm_wrt_tm  b   a ) 
 | DE_Eta : forall (L:vars) (S:signature) (b' b:tm),
      ( forall x , x \notin  L  ->   ( open_tm_wrt_tm b' (a_Var_f x) )   =  (a_App b (a_Var_f x))  )  ->
      lc_tm  b  ->
     DEquiv S (a_Abs b') b
 | DE_Delta : forall (S:signature) (x:var) (i:nat) (a A:tm) (k:nat),
      binds  x  (Def  A k a )  S  ->
      lc_tm  a  ->
     DEquiv S (a_Const x i)  (incr  i   a ) 
 | DE_Arrow : forall (S:signature) (A B A' B':tm),
     DEquiv S A A' ->
     DEquiv S B B' ->
     DEquiv S (a_Arrow A B) (a_Arrow A' B')
 | DE_Pi : forall (L:vars) (S:signature) (A:tm) (k:nat) (B A' B':tm),
     DEquiv S A A' ->
      ( forall x , x \notin  L  -> DEquiv S  ( open_tm_wrt_tm B (a_Var_f x) )   ( open_tm_wrt_tm B' (a_Var_f x) )  )  ->
     DEquiv S (a_Pi A k B) (a_Pi A' k B')
 | DE_Abs : forall (L:vars) (S:signature) (b b':tm),
      ( forall x , x \notin  L  -> DEquiv S  ( open_tm_wrt_tm b (a_Var_f x) )   ( open_tm_wrt_tm b' (a_Var_f x) )  )  ->
     DEquiv S (a_Abs b) (a_Abs b')
 | DE_App : forall (S:signature) (b a b' a':tm),
     DEquiv S a a' ->
     DEquiv S b b' ->
     DEquiv S (a_App b a) (a_App b' a')
 | DE_Absurd : forall (S:signature) (b b':tm),
     DEquiv S b b' ->
     DEquiv S (a_Absurd b) (a_Absurd b').

(* defns JDTyping *)
Inductive DSig : signature -> Prop :=    (* defn DSig *)
 | D_Empty : 
     DSig  nil 
 | D_Cons : forall (S:signature) (x:var) (A:tm) (k:nat) (a:tm),
     DSig S ->
     DTyping S  nil  A a_Type k ->
     DTyping S  nil  a A k ->
      ~ AtomSetImpl.In  x  (dom  S )  ->
     DSig  (  ( x ~ (Def A k a) )  ++ S ) 
with DCtx : signature -> context -> Prop :=    (* defn DCtx *)
 | DG_Empty : forall (S:signature),
     DSig S ->
     DCtx S  nil 
 | DG_Cons : forall (S:signature) (G:context) (x:var) (A:tm) (k:nat),
     DCtx S G ->
     DTyping S G A a_Type k ->
      ~ AtomSetImpl.In  x  (dom  G )  ->
      ~ AtomSetImpl.In  x  (dom  S )  ->
     DCtx S  (  ( x ~ (Tm A k) )  ++ G ) 
with DTyping : signature -> context -> tm -> tm -> nat -> Prop :=    (* defn DTyping *)
 | DT_Type : forall (S:signature) (G:context) (k:nat),
     DCtx S G ->
     DTyping S G a_Type a_Type k
 | DT_Const : forall (S:signature) (G:context) (x:var) (i:nat) (A:tm) (k j:nat) (a:tm),
      binds  x  (Def  A j a )  S  ->
     DCtx S G ->
     DSig S ->
       ( i  +  j )   <=  k  ->
     DTyping S G (a_Const x i)  (incr  i   A )  k
 | DT_Var : forall (S:signature) (G:context) (x:var) (A:tm) (k j:nat),
      binds  x  (Tm  A j )  G  ->
     DCtx S G ->
      j  <=  k  ->
     DTyping S G (a_Var_f x) A k
 | DT_Arrow : forall (S:signature) (G:context) (A B:tm) (k:nat),
     DTyping S G A a_Type k ->
     DTyping S G B a_Type k ->
     DTyping S G (a_Arrow A B) a_Type k
 | DT_Pi : forall (L:vars) (S:signature) (G:context) (A:tm) (j:nat) (B:tm) (k:nat),
     DTyping S G A a_Type j ->
      ( forall x , x \notin  L  -> DTyping S  (  ( x ~ (Tm A j) )  ++ G )   ( open_tm_wrt_tm B (a_Var_f x) )  a_Type k )  ->
      j  <  k  ->
     DTyping S G (a_Pi A j B) a_Type k
 | DT_AbsTm : forall (L:vars) (S:signature) (G:context) (b A B:tm) (k:nat),
     DTyping S G A a_Type k ->
     DTyping S G B a_Type k ->
      ( forall x , x \notin  L  -> DTyping S  (  ( x ~ (Tm A k) )  ++ G )   ( open_tm_wrt_tm b (a_Var_f x) )  B k )  ->
     DTyping S G (a_Abs b) (a_Arrow A B) k
 | DT_AbsTy : forall (L:vars) (S:signature) (G:context) (b A:tm) (j:nat) (B:tm) (k:nat),
     DTyping S G A a_Type j ->
      ( forall x , x \notin  L  -> DTyping S  (  ( x ~ (Tm A j) )  ++ G )   ( open_tm_wrt_tm b (a_Var_f x) )   ( open_tm_wrt_tm B (a_Var_f x) )  k )  ->
      j  <  k  ->
     DTyping S G (a_Abs b) (a_Pi A j B) k
 | DT_AppTm : forall (S:signature) (G:context) (b a B:tm) (k:nat) (A:tm),
     DTyping S G b (a_Arrow A B) k ->
     DTyping S G a A k ->
     DTyping S G (a_App b a) B k
 | DT_AppTy : forall (S:signature) (G:context) (b a B:tm) (k:nat) (A:tm) (j:nat),
     DTyping S G b (a_Pi A j B) k ->
     DTyping S G a A j ->
      j  <  k  ->
     DTyping S G (a_App b a)  (open_tm_wrt_tm  B   a )  k
 | DT_Bottom : forall (S:signature) (G:context) (k:nat),
     DCtx S G ->
     DTyping S G a_Bottom a_Type k
 | DT_Absurd : forall (S:signature) (G:context) (b A:tm) (k:nat),
     DTyping S G A a_Type k ->
     DTyping S G b a_Bottom k ->
     DTyping S G (a_Absurd b) A k
 | DT_Conv : forall (S:signature) (G:context) (a B:tm) (k:nat) (A:tm),
     DTyping S G a A k ->
     DTyping S G B a_Type k ->
     DEquiv S A B ->
     DTyping S G a B k.

(* defns JSub *)
Inductive CtxSub : context -> context -> Prop :=    (* defn CtxSub *)
 | S_Nil : 
     CtxSub  nil   nil 
 | S_Cons : forall (G1:context) (x:var) (A:tm) (j:nat) (G2:context) (k:nat),
     lc_tm A ->
      j  <=  k  ->
     CtxSub G1 G2 ->
     CtxSub  (  ( x ~ (Tm A j) )  ++ G1 )   (  ( x ~ (Tm A k) )  ++ G2 ) 
 | S_Weak : forall (G1:context) (x:var) (A:tm) (k:nat) (G2:context),
     lc_tm A ->
     CtxSub G1 G2 ->
     CtxSub  (  ( x ~ (Tm A k) )  ++ G1 )  G2.

(* defns AReduce *)
Inductive Reduce : signature -> tm -> tm -> Prop :=    (* defn Reduce *)
 | R_Beta : forall (S:signature) (b a:tm),
     lc_tm (a_Abs b) ->
     lc_tm a ->
     Reduce S (a_App  ( (a_Abs b) )  a)  (open_tm_wrt_tm  b   a ) 
 | R_Delta : forall (S:signature) (x:var) (i:nat) (a A:tm) (k:nat),
      binds  x  (Def  A k a )  S  ->
     Reduce S (a_Const x i)  (incr  i   a ) 
 | R_App : forall (S:signature) (b a b':tm),
     lc_tm a ->
     Reduce S b b' ->
     Reduce S (a_App b a) (a_App b' a).

(* defns AWHNF *)
Inductive WHNF : signature -> tm -> tm -> Prop :=    (* defn WHNF *)
 | W_Refl : forall (S:signature) (a:tm),
     lc_tm a ->
     WHNF S a a
 | W_Trans : forall (S:signature) (a c b:tm),
     Reduce S a b ->
     WHNF S b c ->
     WHNF S a c.

(* defns AEq *)
Inductive Convert : signature -> tm -> tm -> Prop :=    (* defn Convert *)
 | Conv_Refl : forall (S:signature) (a:tm),
     lc_tm a ->
     Convert S a a
 | Conv_Arrow : forall (S:signature) (A B A' B':tm),
     Convert S A A' ->
     Convert S B B' ->
     Convert S (a_Arrow A B) (a_Arrow A' B')
 | Conv_Pi : forall (L:vars) (S:signature) (A:tm) (k:nat) (B A' B':tm),
     Convert S A A' ->
      ( forall x , x \notin  L  -> Convert S  ( open_tm_wrt_tm B (a_Var_f x) )   ( open_tm_wrt_tm B' (a_Var_f x) )  )  ->
     Convert S (a_Pi A k B) (a_Pi A' k B')
 | Conv_Abs : forall (L:vars) (S:signature) (b b':tm),
      ( forall x , x \notin  L  -> Convert S  ( open_tm_wrt_tm b (a_Var_f x) )   ( open_tm_wrt_tm b' (a_Var_f x) )  )  ->
     Convert S (a_Abs b) (a_Abs b')
 | Conv_Absurd : forall (S:signature) (b b':tm),
     Convert S b b' ->
     Convert S (a_Absurd b) (a_Absurd b')
 | Conv_EtaL : forall (L:vars) (S:signature) (b' b:tm),
      ( forall x , x \notin  L  -> Convert S  ( open_tm_wrt_tm b' (a_Var_f x) )  (a_App b (a_Var_f x)) )  ->
     Convert S (a_Abs b') b
 | Conv_EtaR : forall (L:vars) (S:signature) (b b':tm),
      ( forall x , x \notin  L  -> Convert S (a_App b (a_Var_f x))  ( open_tm_wrt_tm b' (a_Var_f x) )  )  ->
     Convert S b (a_Abs b')
 | Conv_Whnf : forall (S:signature) (a b a' b':tm),
     WHNF S a a' ->
     WHNF S b b' ->
     Convert S a' b' ->
     Convert S a b
 | Conv_App : forall (S:signature) (b a b' a':tm),
     Convert S a a' ->
     Convert S b b' ->
     Convert S (a_App b a) (a_App b' a').


(** infrastructure *)
Hint Constructors Equiv Ctx Typing FakeTyping DEquiv DSig DCtx DTyping CtxSub Reduce WHNF Convert lc_tm lc_def lc_assn lc_ne lc_nf lc_value : core.


