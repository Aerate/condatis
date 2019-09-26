module CTL.Modalities.AU where

open import CTL.Modalities.AN
open import FStream.Core
open import Library


data _AU'_ {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
     (props₁ props₂ : FStream' C (Set ℓ₃)) : Set (ℓ₂ ⊔ ℓ₃) where
  finallyA : head props₁ → props₁ AU' props₂
  _untilA_ : head props₂ → AN'ₛ props₁ AU' AN'ₛ props₂ → props₁ AU' props₂ -- FIXME Problem here is that props1 & props2 should be in the same Kripke worlds in the future. What if their shapes differ? Do I need Applicative?
  -- Think about example programs. Do we want to execute both? For how long? Is this about exceptions?

-- TODO Implement with Applicative
AU : ∀ {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂} → FStream C (Set ℓ₃)
   → FStream C (Set ℓ₃) → Set (ℓ₂ ⊔ ℓ₃)
AU s₁ s₂ = {!   !}

mutual
  AUₛ' : ∀ {i : Size} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂} → FStream' C (Set ℓ₃)
       → FStream' C (Set ℓ₃) → FStream' {i} C (Set (ℓ₂ ⊔ ℓ₃))
  AUₛ' = {!   !}

  AUₛ : ∀ {i : Size} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂} → FStream C (Set ℓ₃)
      → FStream C (Set ℓ₃) → FStream {i} C (Set (ℓ₂ ⊔ ℓ₃))
  AUₛ = {!   !}
