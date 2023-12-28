open import common

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

module accext where
  accProp : ∀ {k} (p q : Acc k) → p ≡ q
  accProp (acc< f) (acc< g) = cong acc< (funext' (λ j → funext (λ j<k → accProp (f j<k) (g j<k))))
    where open funext