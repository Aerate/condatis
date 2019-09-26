module CTL.Modalities.AF where

open import FStream.Core
open import Library

-- Certainly sometimes : s₀ ⊧ φ ⇔ ∀ s₀ R s₁ R ... ∃ i . sᵢ ⊧ φ
-- TODO Unclear whether this needs sizes
data AF' {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
     (props : FStream' C (Set ℓ₃)) : Set (ℓ₂ ⊔ ℓ₃) where
  alreadyA : head props → AF' props
  notYetA  : A (fmap AF' (inF (tail props))) → AF' props
open AF' public

AF : ∀ {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
     → FStream C (Set ℓ₃) → Set (ℓ₂ ⊔ ℓ₃)
AF {ℓ₁} {ℓ₂} {ℓ₃} {C} props = □ C AF' (inF props)

mutual
  AFₛ' : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
       → FStream' C (Set ℓ₃) → FStream' {i} C (Set (ℓ₂ ⊔ ℓ₃))
  head (AFₛ' props) = AF' props
  tail (AFₛ' props) = AFₛ (tail props)

  AFₛ : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
       → FStream C (Set ℓ₃) → FStream {i} C (Set (ℓ₂ ⊔ ℓ₃))
  inF (AFₛ props) = fmap AFₛ' (inF props)
