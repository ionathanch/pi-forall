open import common
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
      p = substRename suc σ A
  in transp (U _) (sym p) (u (σ ∘ suc) emV) ,
     ≡-el (u (σ ∘ suc) emV) (sym p) elU
soundVar {σ} (∷̂  v _) (emV , _) (there {x = x} {A = A} where?) =
  let u , elU = soundVar v emV where?
      p : subst σ (rename suc A) ≡ subst (σ ∘ suc) A
      p = substRename suc σ A
  in transp (U _) (sym p) u ,
     ≡-el u (sym p) elU

soundness : ∀ {σ Γ a A k} (v : V Γ) → em σ v → Γ ⊢ a ⦂ A # k → Σ[ u ∈ U k (subst σ A) ] el k (subst σ a) u
soundness v emV (⊢var ⊢Γ eq where?) = soundVar v emV where?
soundness v emV (⊢var ⊢Γ (lt j<k) where?) =
  let u , elU = soundVar v emV where?
  in cumU j<k u , cumEl j<k u elU
soundness v emV (⊢∗ ⊢Γ) = Û , Û
soundness {σ} v emV (⊢Π {B = B} {k = k} j<k tA tB) with acc< f ← wf k =
  let u , elU = soundness v emV tA
  in Û , Π̂ _ j<k _ (accU' (wf _) (f j<k) (el-U u elU)) _
     (λ x elA →
      let u , elU = soundness {σ = x +: σ}
            (∷̂  v (λ σ emV → let u , elU = soundness v emV tA in el-U u elU))
            (emV , accEl' (f j<k) (wf _) (accU' (wf _) (f j<k) _) (el-U u elU) elA) tB
      in accU' (wf k) (acc< f) (transp (U k) (substUnion σ x B) (el-U u elU)))
soundness {σ} v emV (⊢λᵈ {B = B} {b = b} {k = k} j<k tA tb) with acc< f ← wf k =
  let u , elU = soundness v emV tA
  in Π̂ _ j<k _ (accU' (wf _) (f j<k) (el-U u elU)) _
     (λ x elA →
      let uB , elB = soundness {σ = x +: σ}
            (∷̂  v (λ σ emV → let u , elU = soundness v emV tA in el-U u elU))
            (emV , accEl' (f j<k) (wf _) (accU' (wf _) (f j<k) _) (el-U u elU) elA) tb
      in accU' (wf k) (acc< f) (transp (U k) (substUnion σ x B) uB)) ,
     (λ x elA →
      let uB , elB = soundness {σ = x +: σ}
            (∷̂  v (λ σ emV → let u , elU = soundness v emV tA in el-U u elU))
            (emV , accEl' (f j<k) (wf _) (accU' (wf _) (f j<k) _) (el-U u elU) elA) tb
          uB' = transp (U k) (substUnion σ x B) uB
          elB' = ≡-el uB (substUnion σ x B) elB
          elB'' = ⇒⋆-el uB' (⇒⋆-β σ b x) elB'
      in accEl' (wf k) (acc< f) uB' (accU' (wf k) (acc< f) _) elB'')
soundness {σ} v emV (⊢$ᵈ {j = j} {B = B} {b = b} {a = a} {k = k} j<k tb ta)
  with acc< f ← wf k | acc< g ← wf j =
  let ub , elb = soundness v emV tb
      ua , ela = soundness v emV ta
      j<k , uA , uB = invΠ-U (wf k) ub
      uA' = accU< (wf k) (acc< f) j<k uA
      ela' = accEl' (wf j) (f j<k) ua uA' ela
      ela'' = accEl< (acc< f) (wf k) j<k uA' uA ela'
      uB' = uB (subst σ a) ela''
      elb' = invΠ-el (wf k) ub (subst σ b) elb (subst σ a) ela''
      uB'' = transp (U k) (substDist σ a B) uB'
      elb'' = ≡-el uB' (substDist σ a B) elb'
  in accU' (wf k) (acc< f) uB'' ,
     accEl' (wf k) (acc< f) uB'' (accU' (wf k) (acc< f) _) elb''
soundness v emV (⊢mty ⊢Γ) = Û , ⊥̂
soundness {σ} v emV (⊢abs {A = A} {b = b} tA tb)
  with () ← (let b , elb = soundness v emV tb in empty b elb)
soundness {σ} v emV (⊢≈ {a = a} A≈B ta _) =
  let u , elU = soundness v emV ta
      Aσ≈Bσ = ≈-subst σ A≈B
  in ≈-U Aσ≈Bσ u , ≈-el u (≈-U Aσ≈Bσ u) Aσ≈Bσ elU

consistency : ∀ {b k} → ∙ ⊢ b ⦂ mty # k → ⊥
consistency tb with b , elb ← soundness {σ = var} ∙̂  tt tb = empty b elb