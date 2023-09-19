{-# OPTIONS --rewriting --with-K #-}

open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_ ; refl ; subst ; cong)

{-------------------------------------------------------------
  This module parametrizes the accessibility predicate
  over some strict preorder of Levels.
  We also postulate function extensionality to show that
  accessibility predicates are mere propositions,
  and for convenience mere propness computes to refl
  on definitionally equal proofs of accessibility
  (which requires --with-K).
-------------------------------------------------------------}

module Acc (Level : Set)
           (_<_ : Level → Level → Set)
           (trans< : ∀ {i j k} → i < j → j < k → i < k) where

record Acc (k : Level) : Set where
  pattern
  inductive
  constructor acc<
  field acc : ∀ {j} → j < k → Acc j
open Acc

WF : Set
WF = ∀ k → Acc k

postulate
  funext' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} →
    (f g : ∀ {x} → B x) → (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
  funext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} →
    (f g : ∀ x → B x) → (∀ x → f x ≡ g x) → f ≡ g

funeq : ∀ {A₁ A₂ : Set} {B : A₂ → Set} (p : A₁ ≡ A₂) →
  ((a : A₂) → B a) ≡ ((a : A₁) → B (subst _ p a))
funeq refl = refl

accProp : ∀ {k} (p q : Acc k) → p ≡ q
accProp (acc< f) (acc< g) = cong acc< (funext' f g (λ j → funext f g (λ j<k → accProp (f j<k) (g j<k))))

accPropRefl : ∀ {k} (p : Acc k) → accProp p p ≡ refl
accPropRefl p with accProp p p
... | refl = refl

{-# REWRITE accPropRefl #-}