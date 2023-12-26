open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; cong)
  renaming (subst to transp)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open ≡-Reasoning

module syntactics (Level : Set) where

variable
  A B C : Set
  P : A → Set

infix 20 _∘_
_∘_ : (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

infix 10 _+:_
_+:_ : A → (ℕ → A) → ℕ → A
(x +: ξ) zero = x
(x +: ξ) (suc n) = ξ n

{-----------------------
  Terms and congruence
-----------------------}

data Term : Set where
  var : ℕ → Term
  ∗ : Term
  Π : Term → Level → Term → Term
  λᵈ : Term → Term
  $ᵈ : Term → Term → Term
  mty : Term
  abs : Term → Term

congΠ : ∀ {A A' j j' B B'} → A ≡ A' → j ≡ j' → B ≡ B' → Π A j B ≡ Π A' j' B'
congΠ refl refl refl = refl

invΠ : ∀ {A A' j j' B B'} → Π A j B ≡ Π A' j' B' → A ≡ A' × j ≡ j' × B ≡ B'
invΠ refl = refl , refl , refl

cong$ᵈ : ∀ {b b' a a'} → b ≡ b' → a ≡ a' → $ᵈ b a ≡ $ᵈ b' a'
cong$ᵈ refl refl = refl

{--------------------
  Lifting renamings
---------------------}

lift : (ℕ → ℕ) → ℕ → ℕ
lift ξ = 0 +: (suc ∘ ξ)

-- Lifting composes
lift∘ : ∀ ξ ζ ρ → (∀ x → (ξ ∘ ζ) x ≡ ρ x) → ∀ x → (lift ξ ∘ lift ζ) x ≡ lift ρ x
lift∘ ξ ζ ρ h zero = refl
lift∘ ξ ζ ρ h (suc n) = cong suc (h n)

{---------------------
  Applying renamings
---------------------}

rename : (ℕ → ℕ) → Term → Term
rename ξ (var s) = var (ξ s)
rename ξ ∗ = ∗
rename ξ (Π A j B) = Π (rename ξ A) j (rename (lift ξ) B)
rename ξ (λᵈ b) = λᵈ (rename (lift ξ) b)
rename ξ ($ᵈ b a) = $ᵈ (rename ξ b) (rename ξ a)
rename ξ mty = mty
rename ξ (abs b) = abs (rename ξ b)

-- Renamings compose
rename∘ : ∀ ξ ζ ς → (∀ x → (ξ ∘ ζ) x ≡ ς x) → ∀ s → (rename ξ ∘ rename ζ) s ≡ rename ς s
rename∘ ξ ζ ς h (var s) = cong var (h s)
rename∘ ξ ζ ς h ∗ = refl
rename∘ ξ ζ ς h (Π A j B) = congΠ (rename∘ ξ ζ ς h A) refl (rename∘ (lift ξ) (lift ζ) (lift ς) (lift∘ ξ ζ ς h) B)
rename∘ ξ ζ ς h (λᵈ b) = cong λᵈ (rename∘ (lift ξ) (lift ζ) (lift ς) (lift∘ ξ ζ ς h) b)
rename∘ ξ ζ ς h ($ᵈ b a) = cong$ᵈ (rename∘ ξ ζ ς h b) (rename∘ ξ ζ ς h a)
rename∘ ξ ζ ς h mty = refl
rename∘ ξ ζ ς h (abs b) = cong abs (rename∘ ξ ζ ς h b)

-- Push renaming into single substitution
renameLift : ∀ ξ a s → (rename ξ ∘ (a +: var)) s ≡ ((rename ξ a +: var) ∘ lift ξ) s
renameLift ξ a zero = refl
renameLift ξ a (suc n) = refl

{------------------------
  Lifting substitutions
------------------------}

infix 30 ↑_
↑_ : (ℕ → Term) → ℕ → Term
↑ σ = var 0 +: (rename suc ∘ σ)

-- Lifting var "substitution" does nothing
↑id : ∀ σ → (∀ x → σ x ≡ var x) → ∀ x → (↑ σ) x ≡ var x
↑id σ h zero = refl
↑id σ h (suc n) = cong (rename suc) (h n)

-- Lifting respects substitution extensionality
↑ext : ∀ σ τ → (∀ x → σ x ≡ τ x) → ∀ x → (↑ σ) x ≡ (↑ τ) x
↑ext σ τ h zero = refl
↑ext σ τ h (suc n) = cong (rename suc) (h n)

-- Lifting commutes with var
↑var : ∀ ξ σ → (∀ x → (var ∘ ξ) x ≡ σ x) → ∀ x → (var ∘ lift ξ) x ≡ (↑ σ) x
↑var ξ σ h zero = refl
↑var ξ σ h (suc n) = cong (rename suc) (h n)

-- Lifting commutes with composition
↑lift : ∀ ξ σ τ → (∀ x → (σ ∘ ξ) x ≡ τ x) → ∀ x → (↑ σ ∘ lift ξ) x ≡ (↑ τ) x
↑lift ξ σ τ h zero = refl
↑lift ξ σ τ h (suc n) = cong (rename suc) (h n)

-- Lifting commutes with renaming
↑rename : ∀ ξ σ τ → (∀ x → (rename ξ ∘ σ) x ≡ τ x) → ∀ x → (rename (lift ξ) ∘ ↑ σ) x ≡ (↑ τ) x
↑rename ξ σ τ h zero = refl
↑rename ξ σ τ h (suc n) = begin
  (rename (lift ξ) ∘ rename suc) (σ n) ≡⟨ rename∘ (lift ξ) suc (lift ξ ∘ suc) (λ _ → refl) (σ n) ⟩
  rename (lift ξ ∘ suc) (σ n)          ≡⟨⟩
  (rename (suc ∘ ξ)) (σ n)             ≡⟨ sym (rename∘ suc ξ (suc ∘ ξ) (λ _ → refl) (σ n)) ⟩
  (rename suc ∘ rename ξ) (σ n)        ≡⟨⟩
  rename suc ((rename ξ ∘ σ) n)        ≡⟨ cong (rename suc) (h n) ⟩
  rename suc (τ n) ∎

{-------------------------
  Applying substitutions
-------------------------}

subst : (ℕ → Term) → Term → Term
subst σ (var s) = σ s
subst σ ∗ = ∗
subst σ (Π A j B) = Π (subst σ A) j (subst (↑ σ) B)
subst σ (λᵈ b) = λᵈ (subst (↑ σ) b)
subst σ ($ᵈ b a) = $ᵈ (subst σ b) (subst σ a)
subst σ mty = mty
subst σ (abs b) = abs (subst σ b)

-- Applying var "substitution" does nothing
private -- use substId'
  substId : ∀ σ → (∀ x → σ x ≡ var x) → ∀ s → subst σ s ≡ s
  substId σ h (var s) = h s
  substId σ h ∗ = refl
  substId σ h (Π A j B) = congΠ (substId σ h A) refl (substId (↑ σ) (↑id σ h) B)
  substId σ h (λᵈ b) = cong λᵈ (substId (↑ σ) (↑id σ h) b)
  substId σ h ($ᵈ b a) = cong$ᵈ (substId σ h b) (substId σ h a)
  substId σ h mty = refl
  substId σ h (abs b) = cong abs (substId σ h b)

-- Substitution extensionality
substExt : ∀ σ τ → (∀ x → σ x ≡ τ x) → ∀ s → subst σ s ≡ subst τ s
substExt σ τ h (var s) = h s
substExt σ τ h ∗ = refl
substExt σ τ h (Π A j B) = congΠ (substExt σ τ h A) refl (substExt (↑ σ) (↑ τ) (↑ext σ τ h) B)
substExt σ τ h (λᵈ b) = cong λᵈ (substExt (↑ σ) (↑ τ) (↑ext σ τ h) b)
substExt σ τ h ($ᵈ b a) = cong$ᵈ (substExt σ τ h b) (substExt σ τ h a)
substExt σ τ h mty = refl
substExt σ τ h (abs b) = cong abs (substExt σ τ h b)

-- Renaming is a substitution
private -- use substVar'
  substVar : ∀ ξ σ → (∀ x → (var ∘ ξ) x ≡ σ x) → ∀ s → rename ξ s ≡ subst σ s
  substVar ξ σ h (var s) = h s
  substVar ξ σ h ∗ = refl
  substVar ξ σ h (Π A j B) = congΠ (substVar ξ σ h A) refl (substVar (lift ξ) (↑ σ) (↑var ξ σ h) B)
  substVar ξ σ h (λᵈ b) = cong λᵈ (substVar (lift ξ) (↑ σ) (↑var ξ σ h) b)
  substVar ξ σ h ($ᵈ b a) = cong$ᵈ (substVar ξ σ h b) (substVar ξ σ h a)
  substVar ξ σ h mty = refl
  substVar ξ σ h (abs b) = cong abs (substVar ξ σ h b)

-- Substitution/renaming compositionality
private -- use substRename'
  substRename : ∀ ξ (σ τ : ℕ → Term) → (∀ x → (σ ∘ ξ) x ≡ τ x) → ∀ s → subst σ (rename ξ s) ≡ subst τ s
  substRename ξ σ τ h (var s) = h s
  substRename ξ σ τ h ∗ = refl
  substRename ξ σ τ h (Π A j B) = congΠ (substRename ξ σ τ h A) refl (substRename (lift ξ) (↑ σ) (↑ τ) (↑lift ξ σ τ h) B)
  substRename ξ σ τ h (λᵈ b) = cong λᵈ (substRename (lift ξ) (↑ σ) (↑ τ) (↑lift ξ σ τ h) b)
  substRename ξ σ τ h ($ᵈ b a) = cong$ᵈ (substRename ξ σ τ h b) (substRename ξ σ τ h a)
  substRename ξ σ τ h mty = refl
  substRename ξ σ τ h (abs b) = cong abs (substRename ξ σ τ h b)

-- Renaming/substitution compositionality
private -- use renameSubst'
  renameSubst : ∀ ξ σ τ → (∀ x → (rename ξ ∘ σ) x ≡ τ x) → ∀ s → rename ξ (subst σ s) ≡ subst τ s
  renameSubst ξ σ τ h (var s) = h s
  renameSubst ξ σ τ h ∗ = refl
  renameSubst ξ σ τ h (Π A j B) = congΠ (renameSubst ξ σ τ h A) refl (renameSubst (lift ξ) (↑ σ) (↑ τ) (↑rename ξ σ τ h) B)
  renameSubst ξ σ τ h (λᵈ b) = cong λᵈ (renameSubst (lift ξ) (↑ σ) (↑ τ) (↑rename ξ σ τ h) b)
  renameSubst ξ σ τ h ($ᵈ b a) = cong$ᵈ (renameSubst ξ σ τ h b) (renameSubst ξ σ τ h a)
  renameSubst ξ σ τ h mty = refl
  renameSubst ξ σ τ h (abs b) = cong abs (renameSubst ξ σ τ h b)

-- Lifting commutes with substitution
↑subst : ∀ ρ σ τ → (∀ x → (subst ρ ∘ σ) x ≡ τ x) → ∀ x → (subst (↑ ρ) ∘ (↑ σ)) x ≡ (↑ τ) x
↑subst ρ σ τ h zero = refl
↑subst ρ σ τ h (suc n) = begin
  (subst (↑ ρ) ∘ rename suc) (σ n) ≡⟨ substRename suc (↑ ρ) (↑ ρ ∘ suc) (λ _ → refl) (σ n) ⟩
  subst (↑ ρ ∘ suc) (σ n)          ≡⟨⟩
  subst (rename suc ∘ ρ) (σ n)     ≡⟨ sym (renameSubst suc ρ (rename suc ∘ ρ) (λ _ → refl) (σ n)) ⟩
  (rename suc ∘ subst ρ) (σ n)     ≡⟨⟩
  rename suc (subst ρ (σ n))       ≡⟨ cong (rename suc) (h n) ⟩
  rename suc (τ n) ∎

-- Substitution compositionality
private -- use subst∘'
  subst∘ : ∀ ρ σ τ → (∀ x → (subst ρ ∘ σ) x ≡ τ x) → ∀ s → (subst ρ ∘ subst σ) s ≡ subst τ s
  subst∘ ρ σ τ h (var s) = h s
  subst∘ ρ σ τ h ∗ = refl
  subst∘ ρ σ τ h (Π A j B) = congΠ (subst∘ ρ σ τ h A) refl (subst∘ (↑ ρ) (↑ σ) (↑ τ) (↑subst ρ σ τ h) B)
  subst∘ ρ σ τ h (λᵈ b) = cong λᵈ (subst∘ (↑ ρ) (↑ σ) (↑ τ) (↑subst ρ σ τ h) b)
  subst∘ ρ σ τ h ($ᵈ b a) = cong$ᵈ (subst∘ ρ σ τ h b) (subst∘ ρ σ τ h a)
  subst∘ ρ σ τ h mty = refl
  subst∘ ρ σ τ h (abs b) = cong abs (subst∘ ρ σ τ h b)

{------------------------------------------------
  Substitution & renaming lemmas, extensionally
  TODO: Maybe the primed and unprimed should swap names
------------------------------------------------}

substId' : ∀ s → subst var s ≡ s
substId' = substId var (λ _ → refl)

substVar' : ∀ ξ s → rename ξ s ≡ subst (var ∘ ξ) s
substVar' ξ = substVar ξ (var ∘ ξ) (λ _ → refl)

substRename' : ∀ ξ σ s → (subst σ ∘ rename ξ) s ≡ subst (σ ∘ ξ) s
substRename' ξ σ = substRename ξ σ (σ ∘ ξ) (λ _ → refl)

renameSubst' : ∀ ξ σ s → (rename ξ ∘ subst σ) s ≡ subst (rename ξ ∘ σ) s
renameSubst' ξ σ = renameSubst ξ σ (rename ξ ∘ σ) (λ _ → refl)

subst∘' : ∀ σ τ s → (subst σ ∘ subst τ) s ≡ subst (subst σ ∘ τ) s
subst∘' σ τ = subst∘ σ τ (subst σ ∘ τ) (λ _ → refl)

{------------------------------------------
  Handy dandy derived substitution lemmas
------------------------------------------}

substRenameVar : ∀ (σ : ℕ → Term) a n → σ n ≡ subst (a +: var) (rename suc (σ n))
substRenameVar σ a n = begin
  σ n ≡⟨ sym (substId var (λ _ → refl) (σ n)) ⟩
  subst var (σ n) ≡⟨ sym (substRename suc (a +: var) ((a +: var) ∘ suc) (λ _ → refl) (σ n)) ⟩
  subst (a +: var) (rename suc (σ n)) ∎

substSubstRename : ∀ σ a s → subst (a +: σ) s ≡ subst (a +: var) (subst (var 0 +: rename suc ∘ σ) s)
substSubstRename σ a s = begin
  subst (a +: σ) s                                       ≡⟨ substExt _ _ (λ {zero → refl ; (suc n) → substRenameVar σ a n}) s ⟩
  subst (subst (a +: var) ∘ (var 0 +: rename suc ∘ σ)) s ≡⟨ sym (subst∘ (a +: var) (var 0 +: rename suc ∘ σ) _ (λ _ → refl) s) ⟩
  (subst (a +: var) ∘ subst (var 0 +: rename suc ∘ σ)) s ∎

substSubstCons : ∀ σ a s → subst (subst σ a +: σ) s ≡ (subst σ ∘ subst (a +: var)) s
substSubstCons σ a s = begin
  subst (subst σ a +: σ) s       ≡⟨ substExt _ _ (λ { zero → refl ; (suc n) → refl }) s ⟩
  subst (subst σ ∘ (a +: var)) s ≡⟨ sym (subst∘ σ (a +: var) _ (λ _ → refl) s) ⟩
  (subst σ ∘ subst (a +: var)) s ∎

{--------------------------
  Contexts and membership
--------------------------}
infix 30 _∷_#_
data Ctxt : Set where
  ∙ : Ctxt
  _∷_#_ : Ctxt → Term → Level → Ctxt

infix 40 _⦂_#_∈_
data _⦂_#_∈_ : ℕ → Term → Level → Ctxt → Set where
  here  : ∀ {Γ A k} → 0 ⦂ (rename suc A) # k ∈ (Γ ∷ A # k)
  there : ∀ {Γ x A B k j} → x ⦂ A # k ∈ Γ → suc x ⦂ (rename suc A) # k ∈ (Γ ∷ B # j) 