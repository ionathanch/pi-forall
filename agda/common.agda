open import Agda.Builtin.Unit using (⊤ ; tt) public
open import Agda.Builtin.Nat using (Nat ; zero ; suc) public
open import Function.Base using (_∘_) public
open import Data.Empty using (⊥) public
open import Data.Product.Base using (Σ-syntax ; ∃-syntax ; _×_ ; _,_) public
open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; refl ; sym ; trans ; cong ; module ≡-Reasoning)
  renaming (subst to transp)
open ≡-Reasoning public

coe : ∀ {A B : Set} → A ≡ B → A → B
coe refl x = x

module funext where
  postulate
    funext' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} →
      {f g : ∀ {x} → B x} → (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
    funext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} →
      {f g : ∀ x → B x} → (∀ x → f x ≡ g x) → f ≡ g

  cong-fun : ∀ {A A' : Set} {B B' : A → Set} →
    (p : A ≡ A') → (∀ x → B x ≡ B' x) →
    (∀ x → B x) ≡ (∀ x → B' (coe (sym p) x))
  cong-fun refl h = cong (λ B → ∀ x → B x) (funext h)