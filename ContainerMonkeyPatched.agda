-- Only A & E remain

module ContainerMonkeyPatched where

open import Data.Container
open import Data.Product
open import Level

-- TODO Why doesn't this work with box?
A : ∀ {c₁ c₂ ℓ} {C : Container c₁ c₂} → ⟦ C ⟧ (Set ℓ) → Set (c₂ ⊔ ℓ)
--A {c₁} {c₂} {ℓ} {C} x = □ {c₁} {c₂} C {suc ℓ} {ℓ} {Set ℓ} (λ s -> s) x
A (s , f) = ∀ p → f p

E : ∀ {c₁ c₂ ℓ} {C : Container c₁ c₂} → ⟦ C ⟧ (Set ℓ) → Set (c₂ ⊔ ℓ)
E (s , f) = ∃ λ p → f p
