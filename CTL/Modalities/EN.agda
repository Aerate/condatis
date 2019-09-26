module CTL.Modalities.EN where

open import FStream.Core
open import Library

-- Eventually (in) Next : p ⊧ φ ⇔ ∃ p[1] ⊧ φ
EN' : ∀ {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂} → FStream' C (Set ℓ₃) → Set (ℓ₂ ⊔ ℓ₃)
EN' {_} {_} {_} {C} s = ◇ C head (inF (tail s))

EN : ∀ {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂} → FStream C (Set ℓ₃) → Set (ℓ₂ ⊔ ℓ₃)
EN {_} {_} {_} {C} s = ◇ C EN' (inF s)

mutual
  EN'ₛ : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
       → FStream' C (Set ℓ₃) → FStream' {i} C (Set (ℓ₂ ⊔ ℓ₃))
  head (EN'ₛ props) = EN' props
  tail (EN'ₛ props) = ENₛ (tail props)

  ENₛ : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
      → FStream C (Set ℓ₃) → FStream {i} C (Set (ℓ₂ ⊔ ℓ₃))
  inF (ENₛ props) = fmap EN'ₛ (inF props)
