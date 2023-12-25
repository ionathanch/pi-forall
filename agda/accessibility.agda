open import Relation.Binary.PropositionalEquality.Core
  using (_≡_ ; refl ; cong)

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

import funext
accProp : ∀ {k} (p q : Acc k) → p ≡ q
accProp (acc< f) (acc< g) = let open funext in cong acc< (funext' (λ j → funext (λ j<k → accProp (f j<k) (g j<k))))