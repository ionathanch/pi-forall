open import common
import accessibility
import syntactics
import reduction

module semantics
  (Level : Set)
  (_<_ : Level → Level → Set)
  (trans< : ∀ {i j k} → i < j → j < k → i < k)
  (wf : accessibility.WF Level _<_) where
open accessibility Level _<_
open syntactics Level
open reduction Level

{----------------------------------------------------------
  Semantic well-typedness:
    ∗       ∈ ⟦∗⟧ₖ       = ⊤
    mty     ∈ ⟦∗⟧ₖ       = ⊤
    Π a j b ∈ ⟦∗⟧ₖ       = j < k ∧ a ∈ ⟦∗⟧ⱼ ∧ (∀ x → x ∈ ⟦a⟧ⱼ → b{x} ∈ ⟦∗⟧ₖ)
    _       ∈ ⟦mty⟧ₖ     = ⊥
    f       ∈ ⟦Π a j b⟧ₖ = ∀ x → x ∈ ⟦a⟧ⱼ → f x ∈ ⟦b{x}⟧ₖ
    x       ∈ ⟦a⟧ₖ       = ∃ b → a ≈ b ∧ x ∈ ⟦b⟧ₖ
----------------------------------------------------------}

data U' k (U< : ∀ {j} → j < k → Term → Set)
          (el< : ∀ {j} (j<k : j < k) → Term → ∀ {T} → U< j<k T → Set)
        : Term → Set where
  Û : U' k U< el< ∗
  ⊥̂ : U' k U< el< mty
  Π̂ : ∀ j → (j<k : j < k) →
      ∀ a → (A : U< j<k a) →
      ∀ b → (∀ x → el< j<k x A → U' k U< el< (subst (x +: var) b)) →
      U' k U< el< (Π a j b)
  ⇒̂  : ∀ a b → a ⇒ b → U' k U< el< b → U' k U< el< a

el' : ∀ k (U< : ∀ {j} → j < k → Term → Set)
          (el< : ∀ {j} (j<k : j < k) → Term → ∀ {T} → U< j<k T → Set) →
      Term → ∀ {T} → U' k U< el< T → Set
el' k U< el< T Û = U' k U< el< T
el' k U< el< _ ⊥̂  = ⊥
el' k U< el< f (Π̂ j j<k _ A _ B) = ∀ x → (a : el< j<k x A) → el' k U< el< ($ᵈ f x) (B x a)
el' k U< el< x (⇒̂  a b a⇒b A) = el' k U< el< x A

-- U' k and el' k are parametrized by U< j and el< j, where j < k;
-- we instantiate the parameters by induction on accessibility of levels

U<  : ∀ {k} → Acc k → ∀ {j} → j < k → Term → Set
el< : ∀ {k} (p : Acc k) {j} (j<k : j < k) → Term → ∀ {T} → U< p j<k T → Set

U<  (acc< f) {j} j<k T = U'  j (U< (f j<k)) (el< (f j<k)) T
el< (acc< f) {j} j<k t = el' j (U< (f j<k)) (el< (f j<k)) t

{-------------------------------------------
  Proofs of accessibility are irrelevant
  where applied to U', U< and el', el< are
  (to isolate direct uses of accProp)
-------------------------------------------}

accU' : ∀ {k} (acc₁ acc₂ : Acc k) {T} → U' k (U< acc₁) (el< acc₁) T → U' k (U< acc₂) (el< acc₂) T
accU' {k} acc₁ acc₂ {T} u with refl ← (let open accext in accProp acc₁ acc₂) = u

accEl' : ∀ {k} (acc₁ acc₂ : Acc k) {t T} (A : U' k (U< acc₁) (el< acc₁) T) →
         el' k (U< acc₂) (el< acc₂) t (accU' acc₁ acc₂ A) ≡ el' k (U< acc₁) (el< acc₁) t A
accEl' {k} acc₁ acc₂ {t} {T} A with refl ← (let open accext in accProp acc₁ acc₂) = refl

-- Proofs of accessibility are irrelevant across instantiated U<
accU< : ∀ {j k} (acc₁ acc₂ : Acc k) (j<k : j < k) {T} → U< acc₁ j<k T → U< acc₂ j<k T
accU< (acc< f) (acc< g) j<k = accU' (f j<k) (g j<k)

-- Proofs of accessibility are irrelevant across instantiated el<
accEl< : ∀ {j k} (acc₁ acc₂ : Acc k) (j<k : j < k) {t T} (A : U< acc₁ j<k T) →
         el< acc₂ j<k t (accU< acc₁ acc₂ j<k A) ≡ el< acc₁ j<k t A
accEl< (acc< f) (acc< g) j<k = accEl' (f j<k) (g j<k)

{------------------------------------------
  U, el, and cumulativity:
  * Given j < k, U j can be lifted to U k
  * Given j < k and u : U j,
    the interpretation of u can be lifted
    to an interpretation of the lifted u
------------------------------------------}

-- U' is cumulative
cumU' : ∀ {j k} (accj : Acc j) (acck : Acc k) → j < k → {T : Term} →
        U' j (U< accj) (el< accj) T → U' k (U< acck) (el< acck) T
cumU' _ _ _ Û = Û
cumU' _ _ _ ⊥̂  = ⊥̂
cumU' accj@(acc< f) acck@(acc< g) j<k (Π̂ i i<j a A b B) =
  Π̂ i (trans< i<j j<k)
    a (accU' (f i<j) (g (trans< i<j j<k)) A)
    b (λ x a → cumU' accj acck j<k (B x (coe (accEl' (f i<j) (g (trans< i<j j<k)) A) a)))
cumU' accj acck j<k (⇒̂  a b a⇒b B) = ⇒̂  a b a⇒b (cumU' accj acck j<k B)

-- el' is cumulative
cumEl' : ∀ {j k} (accj : Acc j) (acck : Acc k) (j<k : j < k) {t T : Term} (u : U' j (U< accj) (el< accj) T) →
         el' j (U< accj) (el< accj) t u → el' k (U< acck) (el< acck) t (cumU' accj acck j<k u)
cumEl' accj acck j<k Û = cumU' accj acck j<k
cumEl' _ _ _ ⊥̂  = λ b → b
cumEl' accj@(acc< f) acck@(acc< g) j<k (Π̂ i i<j a A b B) elB x elA =
  let a' = coe (accEl' (f i<j) (g (trans< i<j j<k)) A) elA
  in cumEl' accj acck j<k (B x a') (elB x a')
cumEl' accj acck j<k (⇒̂  a b a⇒b B) elB = cumEl' accj acck j<k B elB

{-------------------------------------------------
  We tie the knot by instantiating accessibility
  in U< and el< by well-foundedness of levels
-----------------------------------------------}

U : ∀ k → Term → Set
U k T = U' k (U< (wf k)) (el< (wf k)) T

el : ∀ k → Term → ∀ {T} → U k T → Set
el k t = el' k (U< (wf k)) (el< (wf k)) t

cumU : ∀ {j k} → j < k → ∀ {T} → U j T → U k T
cumU = cumU' (wf _) (wf _)

cumEl : ∀ {j k} → (j<k : j < k) → ∀ {t T} (u : U j T) → el j t u → el k t (cumU j<k u)
cumEl = cumEl' (wf _) (wf _)

-- Invariance across equal semantic types
-- (holds by elProp later, but this proof is independent)
el≡ : ∀ {k A A'} → (p : A ≡ A') → (u : U k A) → ∀ t → el k t u ≡ el k t (transp (U k) p u)
el≡ refl u t = refl

{-------------------
  Inversion lemmas
--------------------}

-- Universes are à la Russell
el-U : ∀ {k A} (u : U k ∗) → el k A u → U k A
el-U Û elU = elU
el-U (⇒̂  ∗ ∗ ⇒-∗ u) elU = el-U u elU

-- Nothing lives in the empty type
empty : ∀ {k t} (u : U k mty) → el k t u → ⊥
empty ⊥̂  ()
empty (⇒̂  mty mty ⇒⋆-mty u) = empty u

-- Inversion on semantic function type
invΠ-U : ∀ {a j b k} (acc : Acc k) → U' k (U< acc) (el< acc) (Π a j b) →
       Σ[ j<k ∈ j < k ] Σ[ A ∈ U< acc j<k a ]
       ∀ x → el< acc j<k x A → U' k (U< acc) (el< acc) (subst (x +: var) b)
invΠ-U acc (Π̂ j j<k a A b B) = j<k , A , B
invΠ-U acc@(acc< f) (⇒̂  (Π a j b) (Π a' j b') (⇒-Π a⇒a' b⇒b') u) =
  let j<k , A' , B' = invΠ-U acc u
  in j<k , ⇒̂  a a' a⇒a' A' , λ x elA → ⇒̂  _ _ (⇒-cong (⇒-refl x) b⇒b') (B' x elA)

-- Inversion on semantic functions
invΠ-el : ∀ {a j b k} (acc : Acc k) (u : U' k (U< acc) (el< acc) (Π a j b)) f →
          el' k (U< acc) (el< acc) f u →
          let j<k , A , B = invΠ-U acc u in
          ∀ x → (a : el< acc j<k x A) → el' k (U< acc) (el< acc) ($ᵈ f x) (B x a)
invΠ-el acc (Π̂ j j<k a A b B) f elB x elA = elB x elA
invΠ-el acc@(acc< _) (⇒̂  (Π a j b) (Π a' j b') (⇒-Π a⇒a' b⇒b') u) = invΠ-el acc u

{------------------------------------------------------------
  Backward type preservation of U and el with respect to ⇒⋆
------------------------------------------------------------}

⇒⋆-U' : ∀ {k} (acc : Acc k) {a b} → a ⇒⋆ b → U' k (U< acc) (el< acc) b → U' k (U< acc) (el< acc) a
⇒⋆-U' _ (⇒⋆-refl a) u = u
⇒⋆-U' acc (⇒⋆-trans a⇒b b⇒⋆c) u = ⇒̂ _ _ a⇒b (⇒⋆-U' acc b⇒⋆c u)

⇒⋆-elt' : ∀ {k} (acc : Acc k) {a b} (a⇒⋆b : a ⇒⋆ b) (u : U' k (U< acc) (el< acc) b) →
         ∀ t → el' k (U< acc) (el< acc) t u ≡ el' k (U< acc) (el< acc) t (⇒⋆-U' acc a⇒⋆b u)
⇒⋆-elt' acc (⇒⋆-refl a) u t = refl
⇒⋆-elt' acc (⇒⋆-trans a⇒b b⇒⋆c) u t = ⇒⋆-elt' acc b⇒⋆c u t

⇒⋆-U : ∀ {k a b} → a ⇒⋆ b → U k b → U k a
⇒⋆-U {k} with acc< f ← wf k = ⇒⋆-U' (acc< f)

⇒⋆-elt : ∀ {k a b} (a⇒⋆b : a ⇒⋆ b) (u : U k b) t → el k t u ≡ el k t (⇒⋆-U a⇒⋆b u)
⇒⋆-elt {k} with acc< f ← wf k = ⇒⋆-elt' (acc< f)

{------------------------------------------------------
  Backward term preservation of el with respect to ⇒⋆
------------------------------------------------------}

⇒-el : ∀ {k} (acc : Acc k) {a b A} (u : U' k (U< acc) (el< acc) A) → a ⇒ b →
       el' k (U< acc) (el< acc) b u → el' k (U< acc) (el< acc) a u
⇒-el acc Û a⇒b = ⇒⋆-U' acc (⇒-⇒⋆ a⇒b)
⇒-el acc (Π̂ j j<k _ A _ B) a⇒b elB x elA = ⇒-el acc (B x elA) (⇒-$ᵈ a⇒b (⇒-refl x)) (elB x elA)
⇒-el acc (⇒̂  A B A⇒B u) a⇒b = ⇒-el acc u a⇒b

⇒⋆-el' : ∀ {k} (acc : Acc k) {a b A} (u : U' k (U< acc) (el< acc) A) → a ⇒⋆ b →
         el' k (U< acc) (el< acc) b u → el' k (U< acc) (el< acc) a u
⇒⋆-el' acc u (⇒⋆-refl a) elU = elU
⇒⋆-el' acc u (⇒⋆-trans a⇒b b⇒⋆c) elU = ⇒-el acc u a⇒b (⇒⋆-el' acc u b⇒⋆c elU)

⇒⋆-el : ∀ {k a b A} (u : U k A) → a ⇒⋆ b → el k b u → el k a u
⇒⋆-el {k} with acc< f ← wf k = ⇒⋆-el' (acc< f)

{-----------------------------------
  Subject reduction of U and el:
  If a ⇒ b and U k a then U k b,
  and the interpretations of both
  contain exactly the same terms.
-----------------------------------}

SRU'  : ∀ {k} (acc : Acc k) {a b} →
       a ⇒ b → U' k (U< acc) (el< acc) a → U' k (U< acc) (el< acc) b

SRel' : ∀ {k} (acc : Acc k) {a b} →
       (a⇒b : a ⇒ b) → (u : U' k (U< acc) (el< acc) a) →
       ∀ t → el' k (U< acc) (el< acc) t u ≡ el' k (U< acc) (el< acc) t (SRU' acc a⇒b u)
-- I imagine that instead of an equality, you merely need an isomorphism,
-- i.e. (l , r) : el k t u ↔ el k t (SRU a⇒b u) s.t. l ∘ r ≡ id × r ∘ l ≡ id,
-- but because the function case requires the sym of SRel',
-- both functions and both equalities need to be defined mutually,
-- which is a mess and can lead to termination issues;
-- using function extensionality, while unnecessary, is a lot more convenient

-- This case needs to be first so it reduces in the type of SRel'!
-- Otherwise Agda will refuse since it doesn't match on a⇒b
SRU' acc@(acc< f) {b = b} a⇒b (⇒̂  a c a⇒c C) =
  let d , b⇒d , c⇒d = diamond a⇒b a⇒c
  in ⇒̂  b d b⇒d (SRU' acc c⇒d C)
SRU' (acc< _) ⇒-∗ Û = Û
SRU' (acc< _) ⇒-mty ⊥̂ = ⊥̂
SRU' acc@(acc< f) (⇒-Π {a' = a'} {b' = b'} a⇒a' b⇒b') (Π̂ i i<j a A b B) =
  Π̂ i i<j
    a' (SRU' (f i<j) a⇒a' A)
    b' (λ x elA → SRU' acc (⇒-cong (⇒-refl x) b⇒b')
         (B x (coe (sym (SRel' (f i<j) a⇒a' A x)) elA)))

SRel' (acc< _) ⇒-∗ Û _ = refl
SRel' (acc< _) ⇒-mty ⊥̂ _ = refl
SRel' acc@(acc< f) (⇒-Π a⇒a' b⇒b') (Π̂ i i<j a A b B) h =
  cong-fun refl (λ x →
    cong-fun (SRel' (f i<j) a⇒a' A x)
             (λ elA → SRel' acc (⇒-cong (⇒-refl x) b⇒b') (B x elA) ($ᵈ h x)))
  where open funext
SRel' acc@(acc< _)a⇒b (⇒̂  a c a⇒c C) x =
  let d , b⇒d , c⇒d = diamond a⇒b a⇒c
  in SRel' acc c⇒d C x

SRU : ∀ {k a b} → a ⇒ b → U k a → U k b
SRU {k} with acc< f ← wf k = SRU' (acc< f)

SRel : ∀ {k a b} (a⇒b : a ⇒ b) (u : U k a) →
       ∀ t → el k t u ≡ el k t (SRU a⇒b u)
SRel {k} with acc< f ← wf k = SRel' (acc< f)

SRU* : ∀ {k a b} → a ⇒⋆ b → U k a → U k b
SRU* (⇒⋆-refl a) u = SRU (⇒-refl a) u
SRU* (⇒⋆-trans a⇒b b⇒⋆c) u = SRU* b⇒⋆c (SRU a⇒b u)

SRel* : ∀ {k a b} (a⇒⋆b : a ⇒⋆ b) (u : U k a) →
        ∀ t → el k t u ≡ el k t (SRU* a⇒⋆b u)
SRel* (⇒⋆-refl a) = SRel (⇒-refl a)
SRel* (⇒⋆-trans a⇒b b⇒⋆c) u t = trans (SRel a⇒b u t) (SRel* b⇒⋆c (SRU a⇒b u) t)

≈-U : ∀ {k a b} → a ≈ b → U k a → U k b
≈-U (_ , a⇒⋆c , b⇒⋆c) u = ⇒⋆-U b⇒⋆c (SRU* a⇒⋆c u)

≈-el : ∀ {k a b} (a≈b : a ≈ b) (u : U k a) t → el k t u ≡ el k t (≈-U a≈b u)
≈-el (c , a⇒⋆c , b⇒⋆c) u t = trans (SRel* a⇒⋆c u t) (⇒⋆-elt b⇒⋆c (SRU* a⇒⋆c u) t)

{-----------------------------------------------------
  Propositional irrelevance across U:
  two proofs of a ∈ 〚A⟧ₖ are propositionally equal,
  even given two different sets 〚A⟧ₖ for the same A
-----------------------------------------------------}

elProp : ∀ {k a A₁ A₂} (acc₁ acc₂ : Acc k)
         (u₁ : U' k (U< acc₁) (el< acc₁) A₁)
         (u₂ : U' k (U< acc₂) (el< acc₂) A₂) → A₁ ≈ A₂ →
         el' k (U< acc₁) (el< acc₁) a u₁ → el' k (U< acc₂) (el< acc₂) a u₂
elProp acc₁ acc₂ Û Û _ = accU' acc₁ acc₂
elProp acc₁ acc₂ ⊥̂ ⊥̂ _ ()
elProp acc₁@(acc< f) acc₂@(acc< g) (Π̂ j₁ j<k₁ a₁ A₁ b₁ B₁) (Π̂ j₂ j<k₂ a₂ A₂ b₂ B₂) Πab₁≈Πab₂ =
  let a₁≈a₂ , j₁≡j₂ , b₁≈b₂ = ≈-Π-inv Πab₁≈Πab₂ in helper a₁≈a₂ j₁≡j₂ b₁≈b₂ where
    helper : a₁ ≈ a₂ → j₁ ≡ j₂ → b₁ ≈ b₂ →
      el' _ _ _ _ (Π̂ j₁ j<k₁ a₁ A₁ b₁ B₁) → el' _ _ _ _ (Π̂ j₂ j<k₂ a₂ A₂ b₂ B₂)
    helper a₁≈a₂ refl b₁≈b₂ elf x ela =
      let ela' = elProp (g j<k₂) (f j<k₁) A₂ A₁ (≈-sym a₁≈a₂) ela
      in elProp acc₁ acc₂ (B₁ x ela') (B₂ x ela) (≈-cong (≈-refl x) b₁≈b₂) (elf x ela')
elProp acc₁ acc₂ (⇒̂  a₁ a₂ a₁⇒a₂ u₁) u₂ a₁≈a₃ =
  elProp acc₁ acc₂ u₁ u₂ (≈-trans (≈-sym (⇒-≈ a₁⇒a₂)) a₁≈a₃)
elProp acc₁ acc₂ u₁ (⇒̂  a₂ a₃ a₂⇒a₃ u₂) a₁≈a₂ =
  elProp acc₁ acc₂ u₁ u₂ (≈-trans a₁≈a₂ (⇒-≈ a₂⇒a₃))
elProp _ _ Û ⊥̂ ∗≈mty with () ← ≉⋆-∗mty ∗≈mty
elProp _ _ Û (Π̂ _ _ _ _ _ _) ∗≈Π with () ← ≉⋆-∗Π ∗≈Π
elProp _ _ ⊥̂ (Π̂ _ _ _ _ _ _) mty≈Π with () ← ≉⋆-mtyΠ mty≈Π
elProp _ _ ⊥̂ Û mty≈∗ with () ← ≉⋆-∗mty (≈-sym mty≈∗)
elProp _ _ (Π̂ _ _ _ _ _ _) Û Π≈∗ with () ← ≉⋆-∗Π (≈-sym Π≈∗)
elProp _ _ (Π̂ _ _ _ _ _ _) ⊥̂ Π≈mty with () ← ≉⋆-mtyΠ (≈-sym Π≈mty)

elProp' : ∀ {k a A} (acc₁ acc₂ : Acc k)
         (u₁ : U' k (U< acc₁) (el< acc₁) A) →
         (u₂ : U' k (U< acc₂) (el< acc₂) A) →
         el' k (U< acc₁) (el< acc₁) a u₁ → el' k (U< acc₂) (el< acc₂) a u₂
elProp' acc₁ acc₂ u₁ u₂ = elProp acc₁ acc₂ u₁ u₂ (≈-refl _)

{-----------------------------------------
  Semantic well-formedness:
    σ ∈ ⟦Γ⟧ = x ⦂ A # k ∈ Γ → σ x ∈ ⟦A⟧ₖ
-----------------------------------------}

data V : Ctxt → Set
em : ∀ (σ : Nat → Term) {Γ} → V Γ → Set

data V where
  ∙̂  : V ∙
  ∷̂  : ∀ {Γ A k} → (v : V Γ) → (∀ σ → em σ v → U k (subst σ A)) → V (Γ ∷ A # k)

em σ ∙̂  = ⊤
em σ (∷̂  v u) = Σ[ emV ∈ em (σ ∘ suc) v ] el _ (σ 0) (u (σ ∘ suc) emV)