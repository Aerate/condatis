------------------------------------------------------------------------
-- Modalities that quantify over all paths (A)
------------------------------------------------------------------------

module CTL.A where

open import FStream.Core
open import Library

-- Always Certain : s ⊧ φ ⇔ ∀ p ∀ s ∈ p ⊧ φ
{-# NO_POSITIVITY_CHECK #-}
record AG' {i : Size} {ℓ₁ ℓ₂} {C : Container ℓ₁}
  (props : FStream' {i} C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    nowA' : head props
    laterA' : {j : Size< i} → A (fmap AG' (inF (tail props)))
open AG' public

AG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AG props = APred AG' (inF props)


-- Always Possible : s ⊧ φ ⇔ ∀ p ∃ s ∈ p ⊧ φ
data AF {ℓ₁ ℓ₂} {C : Container ℓ₁}
     (cas : FStream C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyA : A (fmap head (inF cas)) → AF cas
  notYetA : APred AF (fmap (λ x → tail x) (inF cas)) → AF cas
open AF

data AF' {i} {ℓ₁ ℓ₂} {C : Container ℓ₁}
     (cas : FStream' {i} C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyA' : head cas → AF' cas
  notYetA' :  {j : Size< i} →  A (fmap AF' (inF (tail cas))) → AF' cas
open AF'


-- Always (in) Next : p ⊧ φ ⇔ p[1] ⊧ φ
AN' : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} →
      FStream' C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AN' s = APred head (inF (tail s))

AN : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} →
     FStream C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AN s = APred AN' (inF s)


-- TODO AN' won't work with sizes
{-# NON_TERMINATING #-}
AN'ₛ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} →
       FStream' C (Set ℓ₂) → FStream' C (Set (ℓ₁ ⊔ ℓ₂))
head (AN'ₛ s) = AN' s
inF (tail (AN'ₛ s)) = fmap AN'ₛ (inF (tail s))


-- TODO check semantics
data _AU'_ {ℓ₁ ℓ₂} {C : Container ℓ₁}
     (props₁ props₂ : FStream' C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  finallyA : head props₁ → props₁ AU' props₂
  _untilA_ : head props₂ → AN'ₛ props₁ AU' AN'ₛ props₂ → props₁ AU' props₂

AU : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream C (Set ℓ₂) →
     FStream C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AU s₁ s₂ =  APred (λ x → APred (λ y → x AU' y) (inF s₁)) (inF s₂)
