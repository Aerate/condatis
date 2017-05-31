module FStream.Core where

------------------------------------------------------------------------
-- Core module of effectful streams
------------------------------------------------------------------------

open import Library

mutual
  record FStream {i : Size} {ℓ₁ ℓ₂} (C : Container ℓ₁) (A : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    inductive
    field
      inF : ⟦ C ⟧ (FStream' {i} C A)
  record FStream' {i : Size} {ℓ₁ ℓ₂} (C : Container ℓ₁) (A : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    constructor _≺_
    coinductive
    field
      head : A
      tail : {j : Size< i} → FStream {j} C A
open FStream public
open FStream' public

postulate
  _►_ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} →
    ⟦ C ⟧ A → FStream C A → FStream C A
--inF (a ► as) = fmap (λ x → x ≺ as) a


-- Caution, this one pushes the side effects down one tick
mutual
  _►'_ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} →
    A → FStream {i} C A → FStream {i} C A
  inF (a ►' as) = fmap (aux a) (inF as)

  aux  : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} →
    A → FStream' {i} C A → FStream' {i} C A
  head (aux a as) = a
  tail (aux a as) = head as ►' tail as


-- TODO Write without the direct recursion
{-# TERMINATING #-}
_►⋯' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} → A → FStream {i} C A
a ►⋯' = a ►' (a ►⋯')


mutual
  map : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃} →
    (A → B) → FStream {i} C A → FStream {i} C B
  inF (map f as) = fmap (map' f) (inF as)

  map' : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃} →
    (A → B) → FStream' {i} C A → FStream' {i} C B
  head (map' f as) = f (head as)
  tail (map' f as) = map f (tail as)


mutual
  constantly : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} →
    ⟦ C ⟧ A → FStream {i} C A
  inF (constantly ca) = fmap (constantly' ca) ca

  constantly' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} →
    ⟦ C ⟧ A → A → FStream' {i} C A
  head (constantly' ca a) = a
  tail (constantly' ca a) = constantly ca


repeat : {A : Set} → {C : Container ℓ₀} → ⟦ C ⟧ A -> FStream C A
proj₁ (inF (repeat (proj₁ , proj₂))) = proj₁
head (proj₂ (inF (repeat (proj₁ , proj₂))) x) = proj₂ x
tail (proj₂ (inF (repeat (proj₁ , proj₂))) x) = repeat (proj₁ , proj₂)


mutual
  corec : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {X : Set ℓ₃} →
    (X → A × ⟦ C ⟧ X) → ⟦ C ⟧ X → FStream {i} C A
  inF (corec f x) = fmap (corec' f) x

  corec' : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {X : Set ℓ₃} →
    (X → A × ⟦ C ⟧ X) → X → FStream' {i} C A
  head (corec' f x) = proj₁ (f x)
  tail (corec' f x) = corec f (proj₂ (f x))


{-
Stuff that doesn't obviously work:
* drop, _at_ (Since side effects would have to be thrown away)
  (One could at most delay the side effects somehow?)
* _▸⋯  (Only if the given value is effectful or the functor is pointed, i.e. has a null effect (like Applicative or Monad), or by delaying the side effects)
-}
