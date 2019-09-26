module CTL.Modalities.AG where

open import FStream.Core
open import Library

-- Certainly forever : s₀ ⊧ φ ⇔ ∀ s₀ R s₁ R ... ∀ i . sᵢ ⊧ φ
record AG' {i : Size} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
  (props : FStream' C (Set ℓ₃)) : Set (ℓ₂ ⊔ ℓ₃) where
  coinductive
  field
    nowA   : head props
    laterA : {j : Size< i} → A (fmap AG' (inF (tail props)))
open AG' public

AG : ∀ {i : Size} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
   → FStream C (Set ℓ₃) → Set (ℓ₂ ⊔ ℓ₃)
AG {_} {_} {_} {_} {C} props = □ C AG' (inF props)

mutual
  AGₛ' : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
       → FStream' C (Set ℓ₃) → FStream' {i} C (Set (ℓ₂ ⊔ ℓ₃))
  head (AGₛ' props) = AG' props
  tail (AGₛ' props) = AGₛ (tail props)

  AGₛ : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
      → FStream C (Set ℓ₃) → FStream {i} C (Set (ℓ₂ ⊔ ℓ₃))
  inF (AGₛ props) = fmap AGₛ' (inF props)
