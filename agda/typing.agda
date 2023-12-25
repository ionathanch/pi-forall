open import Agda.Builtin.Nat
open import Data.Fin.Base hiding (_≤_)
open import Data.Product.Base
import syntactics
import reduction

module typing
  (Level : Set)
  (_<_ : Level → Level → Set)
  where
open syntactics Level
open reduction Level

data _≤_ : Level → Level → Set where
  eq : ∀ {k} → k ≤ k
  lt : ∀ {j k} → j < k → j ≤ k

infix 10 ⊢_
data ⊢_ : Ctxt → Set
data _⊢_⦂_#_ (Γ : Ctxt) : Term → Term → Level → Set

data ⊢_ where
  ⊢∙ : ⊢ ∙
  ⊢∷ : ∀ {Γ A j} →
       ⊢ Γ →
       Γ ⊢ A ⦂ ∗ # j →
       ---------------
       ⊢ Γ ∷ A # j

data _⊢_⦂_#_ Γ where
  ⊢var : ∀ {x A j k} →
         ⊢ Γ →
         j ≤ k →
         x ⦂ A # j ∈ Γ →
         -----------------
         Γ ⊢ var x ⦂ A # k
  ⊢∗   : ∀ {k} → ⊢ Γ →
         -------------
         Γ ⊢ ∗ ⦂ ∗ # k
  ⊢Π   : ∀ {A j B k} →
         j < k →
         Γ ⊢ A ⦂ ∗ # j →
         Γ ∷ A # j ⊢ B ⦂ ∗ # k →
         ---------------------
         Γ ⊢ Π A j B ⦂ ∗ # k
  ⊢λᵈ  : ∀ {A j B b k} →
         j < k →
         Γ ⊢ A ⦂ ∗ # j →
         Γ ∷ A # j ⊢ b ⦂ B # k →
         -----------------------
         Γ ⊢ λᵈ b ⦂ Π A j B # k
  ⊢$ᵈ  : ∀ {A j B b a k} →
         j < k →
         Γ ⊢ b ⦂ Π A j B # k →
         Γ ⊢ a ⦂ A # j →
         -----------------------------------
         Γ ⊢ $ᵈ b a ⦂ subst (a +: var) B # k
  ⊢mty : ∀ {k} → ⊢ Γ →
         ---------------
         Γ ⊢ mty ⦂ ∗ # k
  ⊢abs : ∀ {A b k} →
         Γ ⊢ A ⦂ ∗ # k →
         Γ ⊢ b ⦂ mty # k →
         -----------------
         Γ ⊢ abs b ⦂ A # k
  ⊢≈   : ∀ {A B a k} →
         A ≈ B →
         Γ ⊢ a ⦂ A # k →
         Γ ⊢ B ⦂ ∗ # k →
         -------------
         Γ ⊢ a ⦂ B # k