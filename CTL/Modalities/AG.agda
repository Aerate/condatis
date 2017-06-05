module CTL.Modalities.AG where

open import FStream.Core
open import Library

-- Certainly forever : s₀ ⊧ φ ⇔ ∀ s₀ R s₁ R ... ∀ i . sᵢ ⊧ φ
{-# NO_POSITIVITY_CHECK #-} -- Not necessary from Agda 2.6 upwards
record AG' {i : Size} {ℓ₁ ℓ₂} {C : Container ℓ₁}
  (props : FStream' C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    nowA   : head props
    laterA : {j : Size< i} → A (fmap AG' (inF (tail props)))
open AG' public

AG : ∀ {i : Size} {ℓ₁ ℓ₂} {C : Container ℓ₁}
   → FStream C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AG props = APred AG' (inF props)

mutual
  AGₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁}
       → FStream' C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
  head (AGₛ' props) = AG' props
  tail (AGₛ' props) = AGₛ (tail props)

  AGₛ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁}
      → FStream C (Set ℓ₂) → FStream {i} C (Set (ℓ₁ ⊔ ℓ₂))
  inF (AGₛ props) = fmap AGₛ' (inF props)
