module FStream.Bisimulation-alt where

open import Library
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import FStream.Core
open import CTL.Modalities


mutual 
  record _~ₛ_ {ℓ₁ ℓ₂} {X : Set ℓ₁} {C : Container ℓ₂} (s₁ s₂ : FStream C X) : Set (ℓ₁ ⊔ ℓ₂) where
    field 
      sameInitShapes : proj₁ (inF s₁) ≡ proj₁ (inF s₂)
      bisim : ∀ pos → proj₂ (inF s₁) pos ∼ₛ' proj₂ (inF s₂) (subst (Position C) sameInitShapes pos)
  record _∼ₛ'_ {i} {ℓ₁ ℓ₂} {X : Set ℓ₁} {C : Container ℓ₂} (s₁ s₂ : FStream' {i} C X) : Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      hd∼ : head s₁ ≡ head s₂
      sameShapes : ∀ {j : Size< i} → proj₁ (inF (tail s₁)) ≡ proj₁ (inF (tail s₂))
      tl∼ : ∀ {j : Size< i} → ∀ pos → (proj₂ (inF (tail s₁ {j})) pos ∼ₛ' proj₂ (inF (tail s₂ {j})) (subst (Position C) sameShapes pos))

-- BisimIsEquivalence : IsEquivalence _~ₛ_
-- refl, sym, trans 
