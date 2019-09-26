module CTL.Modalities.EF where

open import FStream.Core
open import Library

-- Possibly sometime : s₀ ⊧ φ ⇔ ∃ s₀ R s₁ R ... ∃ i . sᵢ ⊧ φ
data EF' {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
     (props : FStream' C (Set ℓ₃)) : Set (ℓ₂ ⊔ ℓ₃) where
  alreadyE : head props → EF' props
  notYetE  : E (fmap EF' (inF (tail props))) → EF' props
open EF'

EF : ∀ {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
     → FStream C (Set ℓ₃) → Set (ℓ₂ ⊔ ℓ₃)
EF {_} {_} {_} {C} props = □ C EF' (inF props)

mutual
  EFₛ' : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
       → FStream' C (Set ℓ₃) → FStream' {i} C (Set (ℓ₂ ⊔ ℓ₃))
  head (EFₛ' props) = EF' props
  tail (EFₛ' props) = EFₛ (tail props)

  EFₛ : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
      → FStream C (Set ℓ₃) → FStream {i} C (Set (ℓ₂ ⊔ ℓ₃))
  inF (EFₛ props) = fmap EFₛ' (inF props)
