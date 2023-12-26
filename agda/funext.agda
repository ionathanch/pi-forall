open import Relation.Binary.PropositionalEquality.Core
  using (_≡_ ; refl ; subst ; cong ; sym)

postulate
  funext' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} →
    {f g : ∀ {x} → B x} → (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
  funext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} →
    {f g : ∀ x → B x} → (∀ x → f x ≡ g x) → f ≡ g

cong-fun : ∀ {A A' : Set} {B B' : A → Set} →
  (p : A ≡ A') → (∀ x → B x ≡ B' x) →
  (∀ x → B x) ≡ (∀ x → B' (subst (λ x → x) (sym p) x))
cong-fun refl h = cong (λ B → ∀ x → B x) (funext h)

cong-fun' : ∀ {A A' : Set} {B : A → Set} {B' : A' → Set} →
  (p : A ≡ A') → (∀ x → B x ≡ B' (subst (λ x → x) p x)) →
  (∀ x → B x) ≡ (∀ x → B' x)
cong-fun' refl h = cong (λ B → ∀ x → B x) (funext h)