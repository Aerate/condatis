module CTL.Modalities.AN where

open import FStream.Core
open import Library

-- Always (in) Next : p ⊧ φ ⇔ p[1] ⊧ φ
AN' : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁}
    → FStream' C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AN' props = APred head (inF (tail props))

AN : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁}
   → FStream C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AN props = APred AN' (inF props)

mutual
  AN'ₛ : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁}
       → FStream' C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
  head (AN'ₛ props) = AN' props
  tail (AN'ₛ props) = ANₛ (tail props)

  ANₛ : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁}
      → FStream C (Set ℓ₂) → FStream {i} C (Set (ℓ₁ ⊔ ℓ₂))
  inF (ANₛ props) = fmap AN'ₛ (inF props)
