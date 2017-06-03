module CTL.Modalities.EF where

open import FStream.Core
open import Library

-- Possibly sometime : s₀ ⊧ φ ⇔ ∃ s₀ R s₁ R ... ∃ i . sᵢ ⊧ φ
data EF' {ℓ₁ ℓ₂} {C : Container ℓ₁}
     (props : FStream' C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyE : head props → EF' props
  notYetE  : E (fmap EF' (inF (tail props))) → EF' props
open EF'

EF : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁}
     → FStream C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
EF props = APred EF' (inF props)

mutual
  EFₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁}
       → FStream' C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
  head (EFₛ' props) = EF' props
  tail (EFₛ' props) = EFₛ (tail props)

  EFₛ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁}
      → FStream C (Set ℓ₂) → FStream {i} C (Set (ℓ₁ ⊔ ℓ₂))
  inF (EFₛ props) = fmap EFₛ' (inF props)
