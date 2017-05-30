module CTL.ModalitiesIdeas where

open import Library
open import FStream.Core
open import CTL.A
open import CTL.E


-- GAₛ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream {i} C (Set (ℓ₁ ⊔ ℓ₂))
-- TODO Implement with fmap

{-
GAₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (GAₛ' cas) = GA cas
inF (tail (GAₛ' cas)) = fmap (GAₛ' ∘ (λ as → tail as)) (inF cas)
-}

AGₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' {∞} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (AGₛ' props) = AG' props
inF (tail (AGₛ' props)) = fmap AGₛ' (inF (tail props))

AGₛ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {∞} C (Set ℓ₂) → FStream {i} C (Set (ℓ₁ ⊔ ℓ₂))
inF (AGₛ props) = fmap AGₛ' (inF props)

AFₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (AFₛ' x) =  AF' x
inF (tail (AFₛ' x)) = fmap AFₛ' (inF (tail x))

AFₛ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream {i} C (Set (ℓ₁ ⊔ ℓ₂))
inF (AFₛ props) = fmap AFₛ' (inF props)

EFₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (EFₛ' x) =  EF' x
inF (tail (EFₛ' x)) = fmap EFₛ' (inF (tail x))

-- GAₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
-- head (GAₛ' cas) = GA cas
-- inF (tail (GAₛ' cas)) = fmap (GAₛ' ∘ (λ as → tail as)) (inF cas)

{-
mutual
  FAₛ' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
  head (FAₛ' props) = FA {!   !} -- props
  inF (tail (FAₛ' props)) = fmap FAₛ' (fmap (λ x → tail x) (inF props))
  FAₛ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream  C (Set ℓ₂) → FStream C (Set (ℓ₁ ⊔ ℓ₂))
  FAₛ = {!   !}
FAₛ'' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (FAₛ'' {i} props) = FA' {! props  !} -- props
inF (tail (FAₛ'' props)) = fmap FAₛ'' (inF (tail props))
GAₛ'' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
GAₛ'' props = {!   !}
-}

--TODO Try GAₛ maybe?
--TODO Think about the semantics and implement it from there

-- Strategie für CTL*: Die temporalen Operatoren sammeln die F an, und die Effektoperatoren fressen sie alle auf
-- Brauchen wir freie Monaden dafür?
{-
Quasi so:
collect : FStream F A -> (Free F) (Stream A)
Dann A oder E anwenden
Wie dann in den F-Kontext zurückkehren?
Oder A & E sind nur Dekorationen per newtype die später ausgewertet werden
-}

Eₛ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (Eₛ {i} {ℓ₁} {ℓ₂} {C} cas) = E {ℓ₁} {ℓ₂} (fmap head (inF {i} cas))
inF (tail (Eₛ cas)) = fmap (Eₛ ∘ (λ as → tail as)) (inF cas)
