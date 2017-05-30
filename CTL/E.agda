------------------------------------------------------------------------
-- Modalities that quantify over some paths (E)
------------------------------------------------------------------------

module CTL.E where

open import FStream.Core
open import Library

-- 'Eventually Certain' : s ⊧ φ ⇔ ∃ p ∀ s ∈ p ⊧ φ
{-# NO_POSITIVITY_CHECK #-}
record EG' {i : Size} {ℓ₁ ℓ₂} {C : Container ℓ₁}
  (props : FStream' {i} C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    nowE' : head props
    laterE' : {j : Size< i} → E (fmap EG' (inF (tail props)))
open EG' public

EG : ∀ {i : Size} {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
EG props = EPred EG' (inF props)


-- Eventually Possible : s ⊧ φ ⇔ ∃ p ∃ s ∈ p ⊧ φ
data EF' {ℓ₁ ℓ₂} {i : Size} {C : Container ℓ₁}
     (cas : FStream' {i} C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyE : head cas → EF' cas
  notYetE :  {j : Size< i} → E (fmap EF' (inF (tail cas))) → EF' cas
open EF'

data EF {ℓ₁ ℓ₂} {C : Container ℓ₁}
     (cas : FStream C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyE : E (fmap head (inF cas)) → EF cas
  notYetE : EPred EF (fmap (λ x → tail x) (inF cas)) → EF cas
open EF


-- Eventually (in) Next : p ⊧ φ ⇔ ∃ p[1] ⊧ φ
EN' : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
EN' s = EPred head (inF (tail s))

EN : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
EN s = EPred EN' (inF s)

{-# NON_TERMINATING #-} -- TODO EN' won't work with sizes
EN'ₛ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' C (Set ℓ₂) → FStream' C (Set (ℓ₁ ⊔ ℓ₂))
head (EN'ₛ s) = EN' s
inF (tail (EN'ₛ s)) = fmap EN'ₛ (inF (tail s))

ENₛ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream C (Set ℓ₂) → FStream C (Set (ℓ₁ ⊔ ℓ₂))
inF (ENₛ s) = fmap EN'ₛ (inF s)
