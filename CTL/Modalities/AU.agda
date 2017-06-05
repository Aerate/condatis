module CTL.Modalities.AU where

open import CTL.Modalities.AN
open import FStream.Core
open import Library


data _AU'_ {ℓ₁ ℓ₂} {C : Container ℓ₁}
     (props₁ props₂ : FStream' C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  finallyA : head props₁ → props₁ AU' props₂
  _untilA_ : head props₂ → AN'ₛ props₁ AU' AN'ₛ props₂ → props₁ AU' props₂

-- TODO Implement with Applicative
AU : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream C (Set ℓ₂)
   → FStream C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AU s₁ s₂ = {!   !}

mutual
  AUₛ' : ∀ {i : Size} {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' C (Set ℓ₂)
       → FStream' C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
  AUₛ' = {!   !}

  AUₛ : ∀ {i : Size} {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream C (Set ℓ₂)
      → FStream C (Set ℓ₂) → FStream {i} C (Set (ℓ₁ ⊔ ℓ₂))
  AUₛ = {!   !}
