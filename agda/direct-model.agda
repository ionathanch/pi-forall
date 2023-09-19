{-# OPTIONS --rewriting #-}

import Acc

module direct-model (Level : Set)
                    (_<_ : Level → Level → Set)
                    (trans< : ∀ {i j k} → i < j → j < k → i < k)
                    (wf : Acc.WF Level _<_ trans<) where

data ⊥ : Set where

data U (k : Level) : Set
el : ∀ k → U k → Set

{-# NO_POSITIVITY_CHECK #-}
data U k where
  Û : U k
  ⊥̂ : U k
  Π̂ : ∀ j → j < k → (A : U j) → (el j A → U k) → U k

el k Û = U k
el k ⊥̂  = ⊥
el k (Π̂ j j<k A B) = (x : el j A) → el k (B x)

lift : ∀ {j k} → j < k → U j → U k
lift _ Û = Û
lift _ ⊥̂ = ⊥̂
lift j<k (Π̂ i i<j A B) = Π̂ i (trans< i<j j<k) A (λ a → lift j<k (B a))

el→ : ∀ {j k} → (j<k : j < k) → ∀ u → el j u → el k (lift j<k u)
el→ j<k Û = lift j<k
el→ _ ⊥̂  ()
el→ j<k (Π̂ i i<j A B) b a = el→ j<k (B a) (b a)