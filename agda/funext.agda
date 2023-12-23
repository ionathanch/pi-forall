{-# OPTIONS --rewriting --confluence-check --with-K #-}

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_ ; refl ; subst ; cong ; sym)

{-# BUILTIN REWRITE _≡_ #-}

postulate
  funext' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} →
    {f g : ∀ {x} → B x} → (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
  funext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} →
    {f g : ∀ x → B x} → (∀ x → f x ≡ g x) → f ≡ g

funextRefl' : ∀ {ℓ₁ ℓ₂ A B} (f : ∀ {x} → B x) h → funext' {ℓ₁} {ℓ₂} {A} {B} {f} {f} h ≡ refl
funextRefl' f h with refl ← funext' h = refl

funextRefl : ∀ {ℓ₁ ℓ₂ A B} (f : ∀ x → B x) h → funext {ℓ₁} {ℓ₂} {A} {B} {f} {f} h ≡ refl
funextRefl f h with refl ← funext h = refl

funeq : ∀ {A₁ A₂ : Set} {B : A₂ → Set} (p : A₁ ≡ A₂) →
  ((a : A₂) → B a) ≡ ((a : A₁) → B (subst _ p a))
funeq refl = refl

{-# REWRITE funextRefl' funextRefl #-}

cong-fun : ∀ {A A' : Set} {B B' : A → Set} →
  (p : A ≡ A') → (∀ x → B x ≡ B' x) →
  (∀ x → B x) ≡ (∀ x → B' (subst (λ x → x) (sym p) x))
cong-fun refl h = cong (λ B → ∀ x → B x) (funext (λ x → h x))