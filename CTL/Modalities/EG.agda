module CTL.Modalities.EG where

open import FStream.Core
open import Library

-- Possibly forever : s₀ ⊧ φ ⇔ ∃ s₀ R s₁ R ... ∀ i . sᵢ ⊧ φ
{-# NO_POSITIVITY_CHECK #-} -- Not necessary from EGda 2.6 upwards
record EG' {i : Size} {ℓ₁ ℓ₂} {C : Container ℓ₁}
  (props : FStream' C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    nowE   : head props
    laterE : {j : Size< i} → E (fmap EG' (inF (tail props)))
open EG' public

EG : ∀ {i : Size} {ℓ₁ ℓ₂} {C : Container ℓ₁}
   → FStream C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
EG props = EPred EG' (inF props)

mutual
  EGₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁}
       → FStream' C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
  head (EGₛ' props) = EG' props
  tail (EGₛ' props) = EGₛ (tail props)

  EGₛ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁}
      → FStream C (Set ℓ₂) → FStream {i} C (Set (ℓ₁ ⊔ ℓ₂))
  inF (EGₛ props) = fmap EGₛ' (inF props)
