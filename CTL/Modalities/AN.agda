module CTL.Modalities.AN where

open import FStream.Core
open import Library

-- Always (in) Next : p ⊧ φ ⇔ p[1] ⊧ φ
AN' : ∀ {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
    → FStream' C (Set ℓ₃) → Set (ℓ₂ ⊔ ℓ₃)
AN' {_} {_} {_} {C} props = □ C head (inF (tail props))

AN : ∀ {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
   → FStream C (Set ℓ₃) → Set (ℓ₂ ⊔ ℓ₃)
AN {_} {_} {_} {C} props = □ C AN' (inF props)

mutual
  AN'ₛ : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
       → FStream' C (Set ℓ₃) → FStream' {i} C (Set (ℓ₂ ⊔ ℓ₃))
  head (AN'ₛ props) = AN' props
  tail (AN'ₛ props) = ANₛ (tail props)

  ANₛ : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
      → FStream C (Set ℓ₃) → FStream {i} C (Set (ℓ₂ ⊔ ℓ₃))
  inF (ANₛ props) = fmap AN'ₛ (inF props)
