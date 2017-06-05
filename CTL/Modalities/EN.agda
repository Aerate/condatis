module CTL.Modalities.EN where

open import FStream.Core
open import Library

-- Eventually (in) Next : p ⊧ φ ⇔ ∃ p[1] ⊧ φ
EN' : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
EN' s = EPred head (inF (tail s))

EN : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
EN s = EPred EN' (inF s)

mutual
  EN'ₛ : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁}
       → FStream' C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
  head (EN'ₛ props) = EN' props
  tail (EN'ₛ props) = ENₛ (tail props)

  ENₛ : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁}
      → FStream C (Set ℓ₂) → FStream {i} C (Set (ℓ₁ ⊔ ℓ₂))
  inF (ENₛ props) = fmap EN'ₛ (inF props)
