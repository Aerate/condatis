module CTL.Modalities where

open import FStream.Core
open import Library

------------------------------------------------------------------------
-- Modalities of CTL
------------------------------------------------------------------------

-- ∀ p ∈ paths, ∀ s ∈ states/p
{-# NO_POSITIVITY_CHECK #-}
record AG' {i : Size} {ℓ₁ ℓ₂} {C : Container ℓ₁}
  (props : FStream' {i} C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    nowA' : head props
    laterA' : {j : Size< i} → A (fmap AG' (inF (tail props)))
open AG' public

AG : ∀ {i : Size} {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AG props = APred AG' (inF props)


-- ∃ p ∈ path, ∀ s ∈ states/p
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


-- ∀ p ∈ paths, ∃ s ∈ states/p
data AF {ℓ₁ ℓ₂} {C : Container ℓ₁} (cas : FStream C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyA : A (fmap head (inF cas)) → AF cas
  notYetA : APred AF (fmap (λ x → tail x) (inF cas)) → AF cas
open AF

data AF' {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} (cas : FStream' {i} C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyA' : head cas → AF' cas
  notYetA' :  {j : Size< i} →  A (fmap AF' (inF (tail cas))) → AF' cas
open AF'


-- ∃ p ∈ paths, ∃ s ∈ states/p
data EF' {ℓ₁ ℓ₂} {i : Size} {C : Container ℓ₁} (cas : FStream' {i} C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyE : head cas → EF' cas
  notYetE :  {j : Size< i} →  E (fmap EF' (inF (tail cas))) → EF' cas
open EF'

data EF {ℓ₁ ℓ₂} {C : Container ℓ₁} (cas : FStream C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyE : E (fmap head (inF cas)) → EF cas
  notYetE : EPred EF (fmap (λ x → tail x) (inF cas)) → EF cas
open EF


initA : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (initA {i} {ℓ₁} {ℓ₂} {C} cas) = A {ℓ₁} {ℓ₂} (fmap head (inF {i} cas))
inF (tail (initA cas)) = fmap (initA ∘ (λ as → tail as)) (inF cas)
