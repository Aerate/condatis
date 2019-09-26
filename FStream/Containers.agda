module FStream.Containers where

------------------------------------------------------------------------
-- Containers & their extension
------------------------------------------------------------------------

open import Data.Fin
open import Data.Maybe
open import Data.Unit

open import Library

ListC : Container ℓ₀ ℓ₀
Shape    ListC   = ℕ
Position ListC n = Fin n

StateC : ∀ {ℓ} → Set ℓ → Container ℓ ℓ
Shape (StateC S) = S → S
Position (StateC S) _ = S

StreamC : Container ℓ₀ ℓ₀
Shape StreamC = ⊤
Position StreamC = const ℕ

ReaderC : Set → Container ℓ₀ ℓ₀
Shape (ReaderC R) = ⊤
Position (ReaderC R) _ = R

runReader : {R A : Set} → ⟦ ReaderC R ⟧ A → R → A
runReader (proj₁ , proj₂) r = proj₂ r

ask : ∀ {R} → ⟦ ReaderC R ⟧ R
proj₁ ask = tt
proj₂ ask x = x

returnReader : ∀ {ℓ} {A : Set ℓ} {R : Set} → A → ⟦ ReaderC R ⟧ A
returnReader a = tt , (λ _ → a)

ExceptC : Set → Container ℓ₀ ℓ₀
Shape (ExceptC E) = Maybe E
Position (ExceptC E₁) (just x) = ⊥
Position (ExceptC E₁) nothing = ⊤

-- TODO Use stdlib
IdC : Container ℓ₀ ℓ₀
Shape IdC = ⊤
Position IdC tt = ⊤
