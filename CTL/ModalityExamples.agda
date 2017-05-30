------------------------------------------------------------------------
-- Examples for modalities
------------------------------------------------------------------------

module CTL.ModalityExamples where

open import Library
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Unit

open import FStream.Containers
open import FStream.Core
open import CTL.A 
open import CTL.E

readDouble : ⟦ ReaderC ℕ ⟧ ℕ
readDouble = fmap (_* 2) ask

readSuc : ⟦ ReaderC ℕ ⟧ ℕ
readSuc = fmap (suc) ask

alwaysPos : (n : ℕ) → runReader readSuc n > 0
alwaysPos n = s≤s z≤n

alwaysPosC : □ (_> 0) readSuc
alwaysPosC = λ p → s≤s z≤n

sometimes3 : ◇ (_≡ 3) readSuc
sometimes3 = suc (suc zero) , refl

sometimes5 : ◇ (_≡ 5) readSuc
sometimes5 = suc (suc (suc (suc zero))) , refl

-- It is always the case that constantly readSuc outputs ℕ > 0, 
-- regardless of the environment
always>0 : AG (map (_> 0) (constantly readSuc))
nowA' (always>0 p) = alwaysPos p
laterA' (always>0 p) = {!!}

{-nowA always>0 = λ p → s≤s z≤n
laterA always>0 = λ p → always>0
-}

{-
nowA always>0 p = s≤s z≤n
laterA always>0 p = always>0
-}

-- Sums all values in the reader-environment
sumFrom : ℕ → FStream (ReaderC ℕ) ℕ
proj₁ (inF (sumFrom n0)) = tt
head (proj₂ (inF (sumFrom n0)) n) = n0 + n
tail (proj₂ (inF (sumFrom n0)) n) = sumFrom (n0 + n)

sum : FStream (ReaderC ℕ) ℕ
sum = sumFrom 0

-- Eventually the sum is greater than 2
eventuallysometimes>2 : EF (map (_> 2) sum)
-- ... having 3 as input, this is of course the case after 1 step
eventuallysometimes>2 = alreadyE (suc (suc (suc zero)) , s≤s (s≤s (s≤s z≤n)))

-- Always somehow the sum is greater than 2
alwaysSomehow>2 : ∀ {i} → EG {i} (map (_> 2) sum)
alwaysSomehow>2 = {!!}

{-proj₁ alwaysSomehow>2 = suc (suc (suc zero))
nowE' (proj₂ alwaysSomehow>2) = s≤s (s≤s (s≤s z≤n))
proj₁ (laterE' (proj₂ alwaysSomehow>2)) = zero
proj₂ (laterE' (proj₂ alwaysSomehow>2)) = {!   !}
-}

{-
nowE alwaysSomehow>2 = (ℕ.suc (ℕ.suc (ℕ.suc ℕ.zero)) , s≤s (s≤s (s≤s z≤n)))
laterE alwaysSomehow>2 = ℕ.zero , alwaysSomehow>2
-}





--
