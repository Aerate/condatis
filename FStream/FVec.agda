module FStream.FVec where

------------------------------------------------------------------------
-- Dissecting effectful streams
------------------------------------------------------------------------

open import Library
open import FStream.Core
open import Data.Fin

infixr 5 _▻_
infix 6 ⟨_▻⋯
infix 7 _⟩

data FVec {ℓ₁ ℓ₂} (C : Container ℓ₁) (A : Set ℓ₂) : (n : ℕ) → Set (ℓ₁ ⊔ ℓ₂) where
  FNil : FVec C A 0
  FCons : ∀ {n} → ⟦ C ⟧ (A × FVec C A n) → FVec C A (suc n)

-- TODO Syntactic sugar for these as well
data FVec' {ℓ₁ ℓ₂} (C : Container ℓ₁) (A : Set ℓ₂) : (n : ℕ) → Set (ℓ₁ ⊔ ℓ₂) where
  FNil' : FVec' C A 0
  FCons' : ∀ {n} → A → ⟦ C ⟧ (FVec' C A n) → FVec' C A (suc n)

_▻'_ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n} →
  A → ⟦ C ⟧ (FVec' C A n) → FVec' C A (suc n)
_▻'_ = FCons'

fVec'ToFVec : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n} →
  FVec' C A n → FVec C A n
fVec'ToFVec FNil' = FNil
fVec'ToFVec (FCons' a v) = FCons (fmap (λ x → a , fVec'ToFVec x) v)

nest : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n} →
  Vec (⟦ C ⟧ A) n → FVec C A n
nest [] = FNil
nest (a ∷ as) = FCons (fmap (_, nest as) a)

_▻_ :  ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n} →
  ⟦ C ⟧ A → (FVec C A n) → FVec C A (suc n)
a ▻ v = FCons (fmap (λ x → x , v) a)

_⟩ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} → ⟦ C ⟧ A → FVec C A 1
a ⟩ = a ▻ FNil

mutual
  vmap : ∀ {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃} {n} →
    (f : A → B) → FVec C A n → FVec C B n
  vmap _ FNil = FNil
  vmap f (FCons x) = FCons (fmap (vmap' f) x)

  vmap' : ∀ {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃} {n} →
    (f : A → B) → A × FVec C A n → B × FVec C B n
  vmap' f (a , v) = f a , vmap f v

mutual
  take : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} →
    (n : ℕ) → FStream C A → FVec C A n
  take ℕ.zero as = FNil
  take (ℕ.suc n) as = FCons (fmap (take' n) (inF as))

  take' : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} →
    (n : ℕ) → FStream' C A → A × FVec C A n
  proj₁ (take' n as) = head as
  proj₂ (take' n as) = take n (tail as)

take'' : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} →
  (n : ℕ) → FStream' C A → FVec' C A n
take'' zero as = FNil'
take'' (suc n) as = FCons' (head as) (fmap (take'' n) (inF (tail as)))

_pre⟨_▻⋯' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {m n}
     → FVec' C A m → FVec' C A (suc n) → FStream' {i} C A
head (FNil' pre⟨ FCons' a _ ▻⋯') = a
inF (tail (FNil' pre⟨ FCons' a v ▻⋯')) = fmap (_pre⟨ (FCons' a v) ▻⋯') v
head (FCons' x _ pre⟨ v' ▻⋯') = x
inF (tail (FCons' _ v pre⟨ v' ▻⋯')) = fmap (_pre⟨ v' ▻⋯') v

⟨_▻⋯' : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n : ℕ}
     → FVec' C A (suc n) → FStream' {i} C A
⟨ v ▻⋯' = FNil' pre⟨ v ▻⋯'

mutual
  _pre⟨_▻⋯ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {m n}
       → FVec C A m → FVec C A (suc n) → FStream {i} C A
  inF (FCons x pre⟨ keep ▻⋯) = fmap (_aux keep) x
  inF (FNil pre⟨ FCons x ▻⋯) = fmap (_aux (FCons x)) x
  _aux_ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n m : ℕ}
    → A × FVec C A m → FVec C A (suc n) → FStream' {i} C A
  head ((a , _ ) aux v) = a
  tail ((_ , v') aux v) = v' pre⟨ v ▻⋯

⟨_▻⋯ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {A : Set ℓ₂} {n : ℕ}
     → FVec C A (suc n) → FStream {i} C A
⟨ as ▻⋯ = FNil pre⟨ as ▻⋯

data _[_]=_ {a} {A : Set a} {ℓ} {C : Container ℓ} : {n : ℕ} → FVec C A n → Fin n → ⟦ C ⟧ A → Set (a ⊔ ℓ) where
  here : ∀ {n} {x : ⟦ C ⟧ A} {xs : FVec C A n} → (x ▻ xs) [ zero ]= x
  there : ∀ {n} {k} {x y} {xs : FVec C A n} → xs [ k ]= x → (y ▻ xs) [ suc k ]= x
