{-# OPTIONS --rewriting --confluence-check #-}

open import Data.Empty
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_ ; refl ; sym ; trans)
  renaming (subst to transp)
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

-- Backward preservation with respect to ⇒⋆

⇒⋆-U' : ∀ {k} (acc : Acc k) {a b} → a ⇒⋆ b → U' k (U< acc) (el< acc) b → U' k (U< acc) (el< acc) a
⇒⋆-U' _ (⇒⋆-refl a) u = u
⇒⋆-U' acc (⇒⋆-trans a⇒b b⇒⋆c) u = ⇒̂ _ _ a⇒b (⇒⋆-U' acc b⇒⋆c u)

⇒⋆-el' : ∀ {k} (acc : Acc k) {a b} (a⇒⋆b : a ⇒⋆ b) (u : U' k (U< acc) (el< acc) b) →
         ∀ t → el' k (U< acc) (el< acc) t u ≡ el' k (U< acc) (el< acc) t (⇒⋆-U' acc a⇒⋆b u)
⇒⋆-el' acc (⇒⋆-refl a) u t = refl
⇒⋆-el' acc (⇒⋆-trans a⇒b b⇒⋆c) u t = ⇒⋆-el' acc b⇒⋆c u t

{------------------------------------------
  U, el, and cumulativity:
  * Given j < k, U j can be lifted to U k
  * Given j < k and u : U j,
    the interpretation of u can be lifted
    to an interpretation of the lifted u
------------------------------------------}

-- Proofs of accessibility are irrelevant across instantiated U'
accU' : ∀ {k} (acc₁ acc₂ : Acc k) {T} → U' k (U< acc₁) (el< acc₁) T → U' k (U< acc₂) (el< acc₂) T
accU' {k} acc₁ acc₂ {T} = transp (λ acc → U' k (U< acc) (el< acc) T) (accProp acc₁ acc₂)

-- Proofs of accessibility are irrelevant across instantiated el'
accEl' : ∀ {k} (acc₁ acc₂ : Acc k) {t T : Term} (A : U' k (U< acc₁) (el< acc₁) T) →
  el' k (U< acc₂) (el< acc₂) t (accU' acc₁ acc₂ A) → el' k (U< acc₁) (el< acc₁) t A
accEl' {k} acc₁ acc₂ {t} {T} A =
  transp (λ x → el' k (U< x) (el< x) t
                    (transp (λ x → U' k (U< x) (el< x) T)
                            (accProp acc₁ x) A))
         (accProp acc₂ acc₁)

-- U' is cumulative
cumU' : ∀ {j k} (accj : Acc j) (acck : Acc k) → j < k → {T : Term} →
        U' j (U< accj) (el< accj) T → U' k (U< acck) (el< acck) T
cumU' _ _ _ Û = Û
cumU' _ _ _ ⊥̂  = ⊥̂
cumU' accj@(acc< f) acck@(acc< g) j<k (Π̂ i i<j a A b B) =
  Π̂ i (trans< i<j j<k)
    a (accU' (f i<j) (g (trans< i<j j<k)) A)
    b (λ x a → cumU' accj acck j<k (B x (accEl' (f i<j) (g (trans< i<j j<k)) A a)))
cumU' accj acck j<k (⇒̂  a b a⇒b B) = ⇒̂  a b a⇒b (cumU' accj acck j<k B)

-- el' is cumulative
cumEl' : ∀ {j k} (accj : Acc j) (acck : Acc k) (j<k : j < k) {t T : Term} (u : U' j (U< accj) (el< accj) T) →
         el' j (U< accj) (el< accj) t u → el' k (U< acck) (el< acck) t (cumU' accj acck j<k u)
cumEl' accj acck j<k Û = cumU' accj acck j<k
cumEl' _ _ _ ⊥̂  = λ b → b
cumEl' accj@(acc< f) acck@(acc< g) j<k (Π̂ i i<j a A b B) elB x elA =
  let a' = accEl' (f i<j) (g (trans< i<j j<k)) A elA
  in cumEl' accj acck j<k (B x a') (elB x a')
cumEl' accj acck j<k (⇒̂  a b a⇒b B) elB = cumEl' accj acck j<k B elB

-- We tie the knot by instantiating the accessibility proof
-- in U< and el< by well-foundedness of levels

U : ∀ k → Term → Set
U k T = U' k (U< (wf k)) (el< (wf k)) T

el : ∀ k → Term → ∀ {T} → U k T → Set
el k t = el' k (U< (wf k)) (el< (wf k)) t

cumU : ∀ {j k} → j < k → ∀ {T} → U j T → U k T
cumU = cumU' (wf _) (wf _)

cumEl : ∀ {j k} → (j<k : j < k) → ∀ {t T} (u : U j T) → el j t u → el k t (cumU j<k u)
cumEl = cumEl' (wf _) (wf _)

-- Backward preservation with respect to ⇒⋆

⇒⋆-U : ∀ {k a b} → a ⇒⋆ b → U k b → U k a
⇒⋆-U {k} with acc< f ← wf k = ⇒⋆-U' (acc< f)

⇒⋆-el : ∀ {k a b} (a⇒⋆b : a ⇒⋆ b) (u : U k b) t → el k t u ≡ el k t (⇒⋆-U a⇒⋆b u)
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
         (B x (transp (λ x → x) (sym (SRel' (f i<j) a⇒a' A x)) elA)))

import funext
SRel' (acc< _) ⇒-∗ Û _ = refl
SRel' (acc< _) ⇒-mty ⊥̂ _ = refl
SRel' acc@(acc< f) (⇒-Π a⇒a' b⇒b') (Π̂ i i<j a A b B) h =
  let open funext in
  cong-fun refl (λ x →
    cong-fun (SRel' (f i<j) a⇒a' A x)
             (λ elA → SRel' acc (⇒-cong (⇒-refl x) b⇒b') (B x elA) ($ᵈ h x)))
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
≈-el (c , a⇒⋆c , b⇒⋆c) u t = trans (SRel* a⇒⋆c u t) (⇒⋆-el b⇒⋆c (SRU* a⇒⋆c u) t)

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