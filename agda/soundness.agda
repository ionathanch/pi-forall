{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Data.Empty
open import Data.Fin.Base
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym)
  renaming (subst to transp)
import accessibility
import syntactics
import reduction
import typing
import semantics

module soundness
  (Level : Set)
  (_<_ : Level → Level → Set)
  (trans< : ∀ {i j k} → i < j → j < k → i < k)
  (wf : accessibility.WF Level _<_) where
open accessibility Level _<_
open syntactics Level
open reduction Level
open typing Level _<_
open semantics Level _<_ trans< wf

soundVar : ∀ {σ Γ x A k} (v : V Γ) → em σ v → x ⦂ A # k ∈ Γ → Σ[ u ∈ U k (subst σ A) ] el k (subst σ (var x)) u
soundVar {σ} (∷̂  v u) (emV , elU) (here {A = A}) =
  let p : subst σ (rename suc A) ≡ subst (σ ∘ suc) A
      p = substRename suc σ _ (λ _ → refl) A
  in transp (U _) (sym p) (u (σ ∘ suc) emV) ,
     transp (λ x → x) (el≡ (sym p) (u (σ ∘ suc) emV) (σ 0)) elU
soundVar {σ} (∷̂  v _) (emV , _) (there {x = x} {A = A} where?) =
  let u , elU = soundVar v emV where?
      p : subst σ (rename suc A) ≡ subst (σ ∘ suc) A
      p = substRename suc σ _ (λ _ → refl) A
  in transp (U _) (sym p) u ,
     transp (λ x → x) (el≡ (sym p) u (subst σ (var (suc x)))) elU

soundness : ∀ {σ Γ a A k} (v : V Γ) → em σ v → Γ ⊢ a ⦂ A # k → Σ[ u ∈ U k (subst σ A) ] el k (subst σ a) u
soundness v emV (⊢var ⊢Γ eq where?) = soundVar v emV where?
soundness v emV (⊢var ⊢Γ (lt j<k) where?) =
  let u , elU = soundVar v emV where?
  in cumU j<k u , cumEl j<k u elU
soundness v emV (⊢∗ ⊢Γ) = Û , Û
soundness {σ} v emV (⊢Π {B = b} {k = k} j<k tA tB) with acc< f ← wf k =
  let u , elU = soundness v emV tA
  in Û , Π̂ _ j<k _ (accU' (wf _) (f j<k) (el-U u elU)) _
     (λ x elA →
      let u , elU = soundness {σ = x +: σ}
            (∷̂  v (λ σ emV → let u , elU = soundness v emV tA in el-U u elU))
            (emV , accEl' (wf _) (f j<k) (el-U u elU) elA) tB
      in accU' (wf _) (acc< f) (transp (U _) (substSubstRename σ x b) (el-U u elU)))
soundness {σ} v emV (⊢λᵈ {B = b} {k = k} j<k tA tb) with acc< f ← wf k =
  let u , elU = soundness v emV tA
  in Π̂ _ j<k _ (accU' (wf _) (f j<k) (el-U u elU)) _
     (λ x elA →
      let B , elB = soundness {σ = x +: σ}
            (∷̂  v (λ σ emV → let u , elU = soundness v emV tA in el-U u elU))
            (emV , accEl' (wf _) (f j<k) (el-U u elU) elA) tb
      in accU' (wf _) (acc< f) (transp (U _) (substSubstRename σ x b) B)) ,
     (λ x elA → {!   !})
soundness {σ} v emV (⊢$ᵈ {B = B} {a = a} j<k tb ta) =
  let Ub , elb = soundness v emV tb
      Ua , ela = soundness v emV ta
  in transp (U _) (substSubstCons σ a B) {!   !} , {!   !}
soundness {σ} v emV (⊢abs {A = A} {b = b} tA tb)
  with () ← (let b , elb = soundness v emV tb in empty b elb)
soundness v emV (⊢mty ⊢Γ) = Û , ⊥̂
soundness {σ} v emV (⊢≈ {a = a} A≈B ta _) =
  let u , elU = soundness v emV ta
      Aσ≈Bσ = ≈-subst σ A≈B
  in ≈-U Aσ≈Bσ u , transp (λ x → x) (≈-el Aσ≈Bσ u (subst σ a)) elU

consistency : ∀ {b k} → ∙ ⊢ b ⦂ mty # k → ⊥
consistency tb with b , elb ← soundness {σ = var} ∙̂  tt tb = empty b elb