module Examples.TrafficLight where

open import Data.Bool
open import Data.Empty
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Library
open import FStream.Core
open import FStream.FVec
open import FStream.Containers

open import CTL.A
open import CTL.E
open import CTL.ModalitiesIdeas

data Colour : Set where
  red   : Colour
  green : Colour

_<$>_ = fmap

boolToColour : Bool → Colour
boolToColour false = green
boolToColour true = red

trafficLight : FStream (ReaderC Bool) Colour
trafficLight = ⟨ returnReader green ▻ (boolToColour <$> ask) ▻ returnReader green ▻ returnReader red ⟩ ▻⋯
-- TODO Consider replacing Colour by Bool for simplification

boolLight : FStream (ReaderC Bool) Bool
boolLight = ⟨ returnReader true ▻ returnReader true ▻ returnReader false ⟩ ▻⋯

-- TODO This only proves that right now (in the first tick), liveness is satisfied, but not in the later ticks!
isLive : AF (map (_≡ green) trafficLight)
isLive = alreadyA (λ p → refl)


trafficLight₂ : FStream (ReaderC Bool) Colour
trafficLight₂ = ⟨ returnReader red ▻ (boolToColour <$> ask) ▻ returnReader red ▻ returnReader green ⟩ ▻⋯
boolLight₂ : FStream (ReaderC Bool) Bool
boolLight₂ = ⟨ returnReader false ▻ returnReader false ▻ returnReader true ⟩ ▻⋯

-- FIND-OUT how to call this / what this actually means
isLive₂ : EF (map (_≡ true) boolLight₂)
isLive₂ = notYetE (true , (notYetE (true , (alreadyE (false , refl)))))


trafficLight₃ : ∀ {i} → FStream {i} (ReaderC Bool) Colour
trafficLight₃ = ⟨ returnReader green ▻ (boolToColour <$> ask) ▻ returnReader red ▻ returnReader green ⟩ ▻⋯
boolLight₃ : FStream (ReaderC Bool) Bool
boolLight₃ = ⟨ returnReader true ▻ returnReader false ▻ returnReader true ⟩ ▻⋯

-- TODO: Check FAₛ implementation since only the 'AlreadyA'-Constructor seems to work
isLive₃ : ∀ {i} → head (AGₛ' {i} (AFₛ' (initA (map (_≡ green) (trafficLight₃)))))
nowA' isLive₃ = alreadyA' (λ p → refl)
nowA' (laterA' (isLive₃ {i}) {j} p) = {! notYetA' ?   !}
nowA' (laterA' (laterA' isLive₃ p₁) p₂) = {!   !}
nowA' (laterA' (laterA' (laterA' isLive₃ p₁) p₂) p) = {!   !}
laterA' (laterA' (laterA' (laterA' isLive₃ p₁) p₂) p) {j} p₃ = isLive₃

isLive₄ : ∀ {i} → AG {i} (AFₛ (map (_≡ green) (trafficLight₃)))
nowA' (isLive₄ p) = alreadyA' refl
nowA' (laterA' (isLive₄ p) false) = alreadyA' refl
nowA' (laterA' (isLive₄ p) true) = notYetA' (const (notYetA' (const (alreadyA' refl))))
nowA' (laterA' (laterA' (isLive₄ p) p₁) p₂) = notYetA' (λ p₃ → alreadyA' refl)
nowA' (laterA' (laterA' (laterA' (isLive₄ p) p₁) p₂) p₃) = alreadyA' refl
laterA' (laterA' (laterA' (laterA' (isLive₄ p) p₁) p₂) p₃) p₄ = isLive₄ true

mutual
  -- This fellow switches between false and true every time a "true" is entered as input
  trueEgde : ∀ {i} → FStream {i} (ReaderC Bool) Bool
  proj₁ (inF trueEgde) = tt
  head (proj₂ (inF trueEgde) true) = false
  tail (proj₂ (inF trueEgde) true) = falseEgde
  head (proj₂ (inF trueEgde) false) = true
  tail (proj₂ (inF trueEgde) false) = trueEgde
  falseEgde : ∀ {i} → FStream {i} (ReaderC Bool) Bool
  proj₁ (inF falseEgde) = tt
  head (proj₂ (inF falseEgde) true) = true
  tail (proj₂ (inF falseEgde) true) = trueEgde
  head (proj₂ (inF falseEgde) false) = false
  tail (proj₂ (inF falseEgde) false) = falseEgde

-- At every point in time, it is possible (by correct input) to output true
-- TODO Not sure whether initA is called for here
mutual
  edgeResponsive : ∀ {i} → head (AGₛ' {i} (EFₛ' (Eₛ (map (_≡ true) trueEgde ))))
  nowA' edgeResponsive = alreadyE (false , refl)
  laterA' edgeResponsive false = edgeResponsive
  laterA' edgeResponsive true = edgeResponsive'
  edgeResponsive' : ∀ {i} → head (AGₛ' {i} (EFₛ' (Eₛ (map (_≡ true) falseEgde))))
  nowA' edgeResponsive' = alreadyE (true , refl)
  laterA' edgeResponsive' false = edgeResponsive'
  laterA' edgeResponsive' true = edgeResponsive

-- Prove that a series of ⊤ is always true, under any circumstance
tautology : AG' ⟨ ⊤ ▻' returnReader FNil' ▻⋯'
-- We create a cyclical stream of proofs
tautology = cycleAG' (tt ▻AG' (λ p → []AG'))

tautology₂ : ∀ {i} → AG {i} ⟨ returnReader ⊤ ⟩ ▻⋯
nowA' (tautology₂ p) = tt
laterA' (tautology₂ p) p₁ = tautology₂ p
-- p is the position of the first side effect
{-
nowA' tautology₂ p = tt
laterA' tautology₂ p = tautology₂
-}
tautology₃ : AG ⟨ returnReader ⊤ ⟩ ▻⋯
tautology₃ = ⟨ ConsAG (λ p → tt , []AG) ▻AG


-- TODO Find something that this satisfies
identity : ∀ {A} → FStream (ReaderC A) A
identity = ⟨ ask ⟩ ▻⋯

alwaysGreen : ∀ {i} → FStream {i} (ReaderC Bool) Colour
alwaysGreen = ⟨ (returnReader green) ▻ returnReader green ⟩ ▻⋯

isAlwaysGreen : ∀ {i} → AG {i} (map (_≡ green) alwaysGreen)
nowA' (isAlwaysGreen p) = refl
nowA' (laterA' (isAlwaysGreen p) p₁) = refl
laterA' (laterA' (isAlwaysGreen p) p₁) p₂ = isAlwaysGreen p
{-
nowA' isAlwaysGreen _ = refl
nowA' (laterA' isAlwaysGreen _) _ = refl
laterA' (laterA' isAlwaysGreen _) _ = isAlwaysGreen
-}

isAlwaysGreen' : ∀ {i} → AG {i} (map (_≡ green) alwaysGreen)
isAlwaysGreen' = mapAG ⟨ (λ p → tt) ▻AG (λ p → refl) ⟩AG ▻AG
-- TODO Impossible

isGreenOrRed : ∀ {i} → AG {i} (map (λ x → (x ≡ green) ⊎ (x ≡ red)) ⟨ returnReader green ▻ returnReader red ⟩ ▻⋯)
nowA' (isGreenOrRed p) = inj₁ refl
nowA' (laterA' (isGreenOrRed p) p₁) = inj₂ refl
laterA' (laterA' (isGreenOrRed p) p₁) p₂ = isGreenOrRed p

isGreenOrRed₁ : ∀ {i} → AG {i} (map (λ x → (x ≡ green) ⊎ (x ≡ red)) ⟨ returnReader green ▻ returnReader red ⟩ ▻⋯)
isGreenOrRed₁ = mapAG ⟨ ((λ p → refl) ▻AG ((λ p → inj₁) ⟩AG)) ▻AG

trafficLight₄ : ∀ {i} → FStream {i} (ReaderC Bool) Bool
trafficLight₄ = ⟨ returnReader true ▻ ask ⟩ ▻⋯

responsivity : ∀ {i} → EG {i} (map (true ≡_) trafficLight₄)
proj₁ responsivity = false
nowE' (proj₂ responsivity) = refl
proj₁ (laterE' (proj₂ responsivity)) = true
nowE' (proj₂ (laterE' (proj₂ responsivity))) = refl
laterE' (proj₂ (laterE' (proj₂ responsivity))) = responsivity

responsivity₁ : ∀ {i} → EG {i} (map (true ≡_) trafficLight₄)
responsivity₁ = mapEG ⟨ refl ⟩EGᵢ ▻EG

responsivity₁' : ∀ {i} → EG {i} (map (true ≡_) trafficLight₄)
responsivity₁' = mapEG ⟨ refl ▻EGᵢ 5675875 ⟩EGᵢ ▻EG
-- TODO Fubar

responsivity₁₁ : ∀ {i} → EG {i} (map (true ≡_) trafficLight₄)
responsivity₁₁ = mapEG ⟨ ((true , refl) ▻EG (false , 23) ⟩EG) ▻EG
-- TODO Fubar

responsivity₁₂ : ∀ {i} → EG {i} (map (true ≡_) trafficLight₄)
responsivity₁₂ = mapEGᵢ FNil (returnReader true ▻ ask ⟩) ⟨ ((true , refl) ▻EG ((true , refl) ⟩EG)) ▻EG

responsivity∼ : ∀ {i} → EG {i} (map (true ≡_) trafficLight₄)
responsivity∼ = bisimEG map∼ ⟨ ((true , refl) ▻EG []EG) ▻EG

responsivity₂ : ∀ {i} → EG {i} (⟨ vmap (true ≡_) (returnReader true ▻ ask ⟩) ▻⋯)
proj₁ responsivity₂ = false
nowE' (proj₂ responsivity₂) = refl
proj₁ (laterE' (proj₂ responsivity₂)) = true
nowE' (proj₂ (laterE' (proj₂ responsivity₂))) = refl
laterE' (proj₂ (laterE' (proj₂ responsivity₂))) = responsivity₂

test : ∀ {i} → AG {i} ⟨ ((returnReader ⊤) ▻ ((fmap (_≡_ true) ask) ⟩)) ▻⋯
test = ⟨ ((λ p → tt) ▻AG ((λ p → {!   !}) ⟩AG)) ▻AG

example : ∀ {i} → FStream {i} (ReaderC ℕ) Set
example = ⟨ (returnReader ⊤) ▻ (fmap (_≡_ 23) ask) ⟩ ▻⋯

property : ∀ {i} → EG {i} example
--property = ⟨ ({! 42 , tt  !} _▻EG_ {!   !}) ▻EG
property = ⟨ (42 , tt) ▻EG (23 , refl) ⟩EG ▻EG

testE : ∀ {i} → EG {i} ⟨ (returnReader ⊤) ▻ (fmap (_≡_ true) ask) ⟩ ▻⋯
testE = ⟨ (true , tt) ▻EG (true , refl) ⟩EG ▻EG

responsoSmall : EN (⟨ vmap (true ≡_) (returnReader true ▻ ask ⟩) ▻⋯)
proj₁ responsoSmall = true
proj₁ (proj₂ responsoSmall) = true
proj₂ (proj₂ responsoSmall) = refl

responso : AG (ENₛ (⟨ vmap (true ≡_) (returnReader true ▻ ask ⟩) ▻⋯))
nowA' (responso p) with fmap EN'ₛ (inF ⟨ FCons (fmap (vmap' (λ section → true ≡ section)) (fmap (λ x → x , ask ⟩) (returnReader true))) ▻⋯)
nowA' (responso p) | proj₃ , proj₄ with EN' (_aux_ ((true ≡ true) , FCons (tt , (λ x → (true ≡ x) , FNil))) (FCons (tt , (λ x → (true ≡ true) , FCons (tt , (λ x₁ → (true ≡ x₁) , FNil))))))
...   | bla = {!   !}
nowA' (laterA' (responso p) p₁) = {!   !}
laterA' (laterA' (responso p) p₁) p₂ = {!   !}

{-
head
      (EN'ₛ
       (((true ≡ true) , FCons (tt , (λ x → (true ≡ x) , FNil))) aux
        FCons
        (tt ,
         (λ x → (true ≡ true) , FCons (tt , (λ x₁ → (true ≡ x₁) , FNil))))))
EN'
 (((true ≡ true) , FCons (tt , (λ x → (true ≡ x) , FNil))) aux
  FCons
  (tt ,
   (λ x → (true ≡ true) , FCons (tt , (λ x₁ → (true ≡ x₁) , FNil)))))
EPred head (inF (tail
 (((true ≡ true) , FCons (tt , (λ x → (true ≡ x) , FNil))) aux
  FCons
  (tt ,
   (λ x → (true ≡ true) , FCons (tt , (λ x₁ → (true ≡ x₁) , FNil)))))))
EPred head (inF
 (( FCons (tt , (λ x → (true ≡ x) , FNil))) pre⟨
  FCons
  (tt ,
   (λ x → (true ≡ true) , FCons (tt , (λ x₁ → (true ≡ x₁) , FNil))) ▻⋯ )))
EPred head (fmap (_aux
  (FCons
  (tt ,
   (λ x → (true ≡ true) , FCons (tt , (λ x₁ → (true ≡ x₁) , FNil))) ▻⋯ ))) (tt , (λ x → (true ≡ x) , FNil)) )
EPred head (tt , (λ x → (true ≡ x) , FNil) aux
  FCons
  (tt ,
   (λ x → (true ≡ true) , FCons (tt , (λ x₁ → (true ≡ x₁) , FNil))) ▻⋯ ) )
∃ p → head ((λ x → (true ≡ x) , FNil) aux
  FCons
  (tt ,
   (λ x → (true ≡ true) , FCons (tt , (λ x₁ → (true ≡ x₁) , FNil))) ▻⋯ ) )
-}

tautology₄ : EG ⟨ returnReader ⊤ ⟩ ▻⋯
tautology₄ = ⟨ ConsEG (23 , tt , []EG) ▻EG

tautology₅ : EG ⟨ returnReader ⊤ ⟩ ▻⋯
tautology₅ = ⟨ (23 , tt) ⟩EG ▻EG

tautology₆ : EG ⟨ returnReader ⊤ ▻ returnReader ⊤ ⟩ ▻⋯
tautology₆ = ⟨ (23 , tt) ▻EG (42 , tt) ⟩EG ▻EG

-- In lots of cases, Agda can infer the input that will validate the proof
easy : EG ⟨ (true ≡_) <$> ask ▻ returnReader ⊤ ⟩ ▻⋯
easy = ⟨ refl ▻EGᵢ tt ⟩EGᵢ ▻EG


timesTwo : ∀ {i} → FStream {i} (ReaderC ℕ) ℕ
timesTwo = map (_* 2) ⟨ ask ⟩ ▻⋯

even : ℕ → Set
even n = ∃ λ m → n ≡ m * 2

alwaysEven : ∀ {i} → AG {i} (map even timesTwo)
nowA' (alwaysEven p) = p , refl
laterA' (alwaysEven p) = alwaysEven

alwaysEven₁ : ∀ {i} → AG {i} (map even timesTwo)
-- alwaysEven₁ = mapAG ([]AG pre⟨ {!   !} ▻AG) -- TODO Report internal error on refining
alwaysEven₁ = mapAG ⟨ (λ p → p) ⟩AG ▻AG

someMoreEven : ∀ {i} → AG {i} (map even ⟨ fmap (_* 2) ask ▻ returnReader 2 ⟩ ▻⋯)
nowA' (someMoreEven p) = p , refl
nowA' (laterA' (someMoreEven p) p₁) = 1 , refl
laterA' (laterA' (someMoreEven p) p₁) = someMoreEven

someMoreEven₁ : ∀ {i} → AG {i} (map even ⟨ fmap (_* 2) ask ▻ returnReader 2 ⟩ ▻⋯)
-- someMoreEven₁ = mapAG ⟨ ((λ p → refl) ▻AG []AG) ▻AG -- TODO Even this works
someMoreEven₁ = mapAG ⟨ ((λ p → refl) ▻AG ((λ p → refl) ⟩AG)) ▻AG






--
