module CTL.Modalities.AF where

open import FStream.Core
open import Library

-- Certainly sometime : s₀ ⊧ φ ⇔ ∀ s₀ R s₁ R ... ∃ i . sᵢ ⊧ φ
-- TODO Unclear whether this needs sizes
data AF' {ℓ₁ ℓ₂} {C : Container ℓ₁}
     (props : FStream' C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyA : head props → AF' props
  notYetA  : A (fmap AF' (inF (tail props))) → AF' props
open AF' public

AF : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁}
     → FStream C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AF props = APred AF' (inF props)

mutual
  AFₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁}
       → FStream' C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
  head (AFₛ' props) = AF' props
  tail (AFₛ' props) = AFₛ (tail props)

  AFₛ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁}
      → FStream C (Set ℓ₂) → FStream {i} C (Set (ℓ₁ ⊔ ℓ₂))
  inF (AFₛ props) = fmap AFₛ' (inF props)
