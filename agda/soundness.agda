{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Nat
open import Data.Fin.Base
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym)
  renaming (subst to transp)
import accessibility
import syntactics
import reduction
import typing
import semantics

module soundness
  (Level : Set)
  (_<_ : Level → Level → Set)
  (_≤_ : Level → Level → Set)
  (trans< : ∀ {i j k} → i < j → j < k → i < k)
  (wf : accessibility.WF Level _<_) where
open accessibility Level _<_
open syntactics Level
open reduction Level
open typing Level _<_ _≤_
open semantics Level _<_ trans< wf

{-
el≡ : ∀ {k A A'} → (p : A ≡ A') → (u : U k A) → ∀ t → el k t u ≡ el k t (transp (U k) p u)
el≡ refl u t = refl

{---------------------------------------------------------
  Semantic well-formedness
    σ ∈ ⟦Γ⟧ = ∀ i → let A , k = get Γ i in σ i ∈ ⟦A{σ}⟧ₖ
---------------------------------------------------------}

infix 5 _⊩_
_⊩_ : (Nat → Term) → Ctxt → Set
σ ⊩ Γ = ∀ i → let A , k = get Γ i in (u : U k (subst σ A)) → el k (σ (toℕ i)) u

⊩∙ : ∀ σ → σ ⊩ ∙
⊩∙ σ ()

⊩∷ : ∀ a A k σ Γ → ((u : U k (subst σ A)) → el k a u) → σ ⊩ Γ → a +: σ ⊩ Γ ∷ A # k
⊩∷ a A k σ Γ h σ⊩Γ zero u =
  let p = substRename suc (a +: σ) _ (λ _ → refl) A
  in transp (λ x → x) (sym (el≡ p u a)) (h (transp (U k) p u))
⊩∷ a A k σ Γ _ σ⊩Γ (suc i) u =
  let A' , k' = get Γ i
      p = substRename suc (a +: σ) _ (λ _ → refl) A'
  in transp (λ x → x) (sym (el≡ p u (σ (toℕ i)))) (σ⊩Γ i (transp (U k') p u))

infix 5 _⊩_
_⊩_ : (Nat → Term) → Ctxt → Set
σ ⊩ Γ = ∀ i → let A , k = get Γ i in Σ[ u ∈ U k (subst σ A) ] el k (σ (toℕ i)) u

⊩∙ : ∀ σ → σ ⊩ ∙
⊩∙ σ ()

⊩∷ : ∀ a A k σ Γ → (u : U k (subst σ A)) → el k a u → σ ⊩ Γ → a +: σ ⊩ Γ ∷ A # k
⊩∷ a A k σ Γ u elA σ⊩Γ zero =
  let p = sym (substRename suc (a +: σ) _ (λ _ → refl) A)
  in transp (U k) p u , transp (λ x → x) (el≡ p u a) elA
⊩∷ a A k σ Γ _ _ σ⊩Γ (suc i) =
  let A' , k' = get Γ i
      p = sym (substRename suc (a +: σ) _ (λ _ → refl) A')
      u' , elA' = σ⊩Γ i
  in transp (U k') p u' , transp (λ x → x) (el≡ p u' (σ (toℕ i))) elA'
-}

soundwf   : ∀ {σ Γ} → ⊢ Γ → Σ[ v ∈ V Γ ] em σ v
soundness : ∀ {Γ a A k} → Γ ⊢ a ⦂ A # k → Σ[ u ∈ U k A ] el k a u