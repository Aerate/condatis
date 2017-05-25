module FStream.Bisimulation-alt where

open import Library
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Core as Core 

open import FStream.Core
open import CTL.Modalities


mutual
  record _~_ {i} {ℓ₁ ℓ₂} {X : Set ℓ₁} {C : Container ℓ₂} (s₁ s₂ : FStream {i} C X) : Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      sameInitShapes : proj₁ (inF s₁) ≡ proj₁ (inF s₂)
      bisim : ∀ {j : Size< i} → ∀ pos → proj₂ (inF s₁) pos ~' proj₂ (inF s₂) (subst (Position C) sameInitShapes pos)
  record _~'_ {i} {ℓ₁ ℓ₂} {X : Set ℓ₁} {C : Container ℓ₂} (s₁ s₂ : FStream' {i} C X) : Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      hd∼ : head s₁ ≡ head s₂
      tl∼ : ∀ {j : Size< i} → tail s₁ ~ tail s₂
open _~_ public
open _~'_ public

mutual
  BisimEquiv  : IsEquivalence _~_
  sameInitShapes (IsEquivalence.refl BisimEquiv {x = x}) = refl
  hd∼ (bisim (IsEquivalence.refl BisimEquiv {x}) pos) = refl
  tl∼ (bisim (IsEquivalence.refl BisimEquiv {x}) pos) with {!!} 
  ...                                              | y = {!!}
  IsEquivalence.sym BisimEquiv = {!!}
  IsEquivalence.trans BisimEquiv = {!!}



  BisimEquiv' : IsEquivalence _~'_
  hd∼ (IsEquivalence.refl BisimEquiv' {x}) = refl
  tl∼ (IsEquivalence.refl BisimEquiv' {x}) = {!!}
  IsEquivalence.sym BisimEquiv' = {!!}
  IsEquivalence.trans BisimEquiv' = {!!}


