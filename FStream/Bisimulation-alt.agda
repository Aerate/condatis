module FStream.Bisimulation-alt where

open import Library
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Core as Core
open ≡-Reasoning

open import FStream.Core
open import CTL.Modalities


mutual
  record _~_ {i} {ℓ₁ ℓ₂} {X : Set ℓ₁} {C : Container ℓ₂} (s₁ s₂ : FStream {i} C X) : Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      sameInitShapes : ∀ {j : Size< i} → proj₁ (inF s₁) ≡ proj₁ (inF s₂)
      bisim : ∀ {j : Size< i} → ∀ pos → proj₂ (inF s₁) pos ~' proj₂ (inF s₂) (subst (Position C) sameInitShapes pos)
  record _~'_ {i} {ℓ₁ ℓ₂} {X : Set ℓ₁} {C : Container ℓ₂} (s₁ s₂ : FStream' {i} C X) : Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      hd∼ : head s₁ ≡ head s₂
      tl∼ : ∀ {j : Size< i} → tail s₁ ~ tail s₂
open _~_ public
open _~'_ public


{-
mutual
  BisimEquiv  : ∀ {i : Size} → IsEquivalence (_~_ {i})
  sameInitShapes (IsEquivalence.refl BisimEquiv {x = x}) = refl
  bisim (IsEquivalence.refl (BisimEquiv {i}) {x}) {j} pos = IsEquivalence.refl (BisimEquiv' {i})
  sameInitShapes (IsEquivalence.sym BisimEquiv x) = sym (sameInitShapes x)
  bisim (IsEquivalence.sym (BisimEquiv {i}) {i = s1} {j = s2} x) pos with bisim x pos
  ... | bla = IsEquivalence.sym BisimEquiv' (subst (λ x₁ → {!   !}) lemma x)
    where
      lemma = begin {!   !}
  sameInitShapes (IsEquivalence.trans BisimEquiv bisim1 bisim2) = trans (sameInitShapes bisim1) (sameInitShapes bisim2)
  bisim (IsEquivalence.trans BisimEquiv bisim1 bisim2) pos = IsEquivalence.trans BisimEquiv' {!   !} {!   !}


  BisimEquiv' : ∀ {i : Size} → IsEquivalence (_~'_ {i})
  hd∼ (IsEquivalence.refl BisimEquiv' {x}) = refl
  tl∼ (IsEquivalence.refl BisimEquiv' {x}) {j} = IsEquivalence.refl (BisimEquiv {j})
  hd∼ (IsEquivalence.sym BisimEquiv' x) = sym (hd∼ x)
  tl∼ (IsEquivalence.sym BisimEquiv' x) {j} = IsEquivalence.sym BisimEquiv (tl∼ x)
  hd∼ (IsEquivalence.trans BisimEquiv' bisim1 bisim2) = trans (hd∼ bisim1) (hd∼ bisim2)
  tl∼ (IsEquivalence.trans BisimEquiv' bisim1 bisim2) {j} = IsEquivalence.trans BisimEquiv (tl∼ bisim1) (tl∼ bisim2)

-}
