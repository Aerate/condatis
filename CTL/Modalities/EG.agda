module CTL.Modalities.EG where

open import FStream.Core
open import Library

-- Possibly forever : s₀ ⊧ φ ⇔ ∃ s₀ R s₁ R ... ∀ i . sᵢ ⊧ φ
record EG' {i : Size} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
  (props : FStream' C (Set ℓ₃)) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  coinductive
  field
    nowE   : head props
    laterE : {j : Size< i} → E (fmap EG' (inF (tail props)))
open EG' public

EG : ∀ {i : Size} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
   → FStream C (Set ℓ₃) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
EG {_} {_} {_} {_} {C} props = ◇ C EG' (inF props)

mutual
  EGₛ' : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
       → FStream' C (Set ℓ₃) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃))
  head (EGₛ' props) = EG' props
  tail (EGₛ' props) = EGₛ (tail props)

  EGₛ : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
      → FStream C (Set ℓ₃) → FStream {i} C (Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃))
  inF (EGₛ props) = fmap EGₛ' (inF props)
