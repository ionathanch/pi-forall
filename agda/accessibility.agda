{-# OPTIONS --rewriting --confluence-check --with-K #-}

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_ ; refl ; cong)

{-# BUILTIN REWRITE _≡_ #-}

{-------------------------------------------------------------
  This module parametrizes the accessibility predicate
  over some strict preorder of Levels.
  We also postulate function extensionality to show that
  accessibility predicates are mere propositions,
  and for convenience mere propness computes to refl
  on definitionally equal proofs of accessibility
  (which requires --with-K).
-------------------------------------------------------------}

module accessibility
  (Level : Set)
  (_<_ : Level → Level → Set) where

record Acc (k : Level) : Set where
  pattern
  inductive
  constructor acc<
  field acc : ∀ {j} → j < k → Acc j
open Acc

WF : Set
WF = ∀ k → Acc k

-- import funext
postulate
  accProp : ∀ {k} (p q : Acc k) → p ≡ q
  -- accProp (acc< f) (acc< g) = let open funext in cong acc< (funext' (λ j → funext (λ j<k → accProp (f j<k) (g j<k))))

accPropRefl : ∀ {k} (p : Acc k) → accProp p p ≡ refl
accPropRefl p with refl ← accProp p p = refl

{-# REWRITE accPropRefl #-}