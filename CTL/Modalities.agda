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

AG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
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


AN' : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AN' s = APred head (inF (tail s))

AN : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AN s = APred AN' (inF s)


{-# NON_TERMINATING #-} -- TODO AN' won't work with sizes
AN'ₛ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' C (Set ℓ₂) → FStream' C (Set (ℓ₁ ⊔ ℓ₂))
head (AN'ₛ s) = AN' s
inF (tail (AN'ₛ s)) = fmap AN'ₛ (inF (tail s))

-- TODO EN

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

data _AU'_ {ℓ₁ ℓ₂} {C : Container ℓ₁} (props₁ props₂ : FStream' C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  finallyA : head props₁ → props₁ AU' props₂
  _untilA_ : head props₂ → AN'ₛ props₁ AU' AN'ₛ props₂ → props₁ AU' props₂

AU : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream C (Set ℓ₂) → FStream C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AU s₁ s₂ =  APred (λ x → APred (λ y → x AU' y) (inF s₁)) (inF s₂)

-- TODO AU, EU', EU


initA : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (initA {i} {ℓ₁} {ℓ₂} {C} cas) = A {ℓ₁} {ℓ₂} (fmap head (inF {i} cas))
inF (tail (initA cas)) = fmap (initA ∘ (λ as → tail as)) (inF cas)
