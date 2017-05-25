module FStream.Bisimulation-alt where

open import Library
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import FStream.Core
open import CTL.Modalities


mutual
  record _~_ {i} {ℓ₁ ℓ₂} {X : Set ℓ₁} {C : Container ℓ₂} (s₁ s₂ : FStream {i} C X) : Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      sameInitShapes : ∀ {j : Size< i} → proj₁ (inF s₁) ≡ proj₁ (inF s₂)
      bisim : ∀ {j : Size< i} → ∀ pos → proj₂ (inF s₁) pos ~' proj₂ (inF s₂) (subst (Position C) sameInitShapes pos)
  record _~'_ {i} {ℓ₁ ℓ₂} {X : Set ℓ₁} {C : Container ℓ₂} (s₁ s₂ : FStream' {i} C X) : Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      hd∼ : head s₁ ≡ head s₂
      tl∼ : ∀ {j : Size< i} → tail s₁ ~ tail s₂

-- BisimIsEquivalence : IsEquivalence _~_
-- refl, sym, trans
