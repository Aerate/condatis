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

open import CTL.Modalities
open import CTL.Proof

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
isLive p = alreadyA refl


trafficLight₂ : FStream (ReaderC Bool) Colour
trafficLight₂ = ⟨ returnReader red ▻ (boolToColour <$> ask) ▻ returnReader red ▻ returnReader green ⟩ ▻⋯
boolLight₂ : FStream (ReaderC Bool) Bool
boolLight₂ = ⟨ returnReader false ▻ returnReader false ▻ returnReader true ⟩ ▻⋯

-- FIND-OUT how to call this / what this actually means
isLive₂ : EF (map (_≡ true) boolLight₂)
isLive₂ p = notYetE (true , (notYetE (true , (alreadyE refl))))
-- notYetE (true , (notYetE (true , (alreadyE (false , refl)))))


trafficLight₃ : ∀ {i} → FStream {i} (ReaderC Bool) Colour
trafficLight₃ = ⟨ returnReader green ▻ (boolToColour <$> ask) ▻ returnReader red ▻ returnReader green ⟩ ▻⋯
boolLight₃ : FStream (ReaderC Bool) Bool
boolLight₃ = ⟨ returnReader true ▻ returnReader false ▻ returnReader true ⟩ ▻⋯


isLive₄ : ∀ {i} → AG {i} (AFₛ (map (_≡ green) (trafficLight₃)))
nowA (isLive₄ p) = alreadyA refl
nowA (laterA (isLive₄ p) false) = alreadyA refl
nowA (laterA (isLive₄ p) true) = notYetA (const (notYetA (const (alreadyA refl))))
nowA (laterA (laterA (isLive₄ p) p₁) p₂) = notYetA (λ p₃ → alreadyA refl)
nowA (laterA (laterA (laterA (isLive₄ p) p₁) p₂) p₃) = alreadyA refl
laterA (laterA (laterA (laterA (isLive₄ p) p₁) p₂) p₃) p₄ = isLive₄ true

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
mutual
  edgeResponsive : ∀ {i} → AG {i} (EFₛ (map (_≡ true) trueEgde ))
  nowA (edgeResponsive false) = alreadyE refl
  nowA (edgeResponsive true) = notYetE (true , alreadyE refl)
  laterA (edgeResponsive false) = edgeResponsive
  laterA (edgeResponsive true) = edgeResponsive'
  edgeResponsive' : ∀ {i} → AG {i} (EFₛ (map (_≡ true) falseEgde))
  edgeResponsive' = {!   !}
  -- Exercise for you, dear reader!

frob : ∀ {i} → Bool → FStream {i} (ReaderC Bool) Bool
proj₁ (inF (frob b)) = tt
head (proj₂ (inF (frob b)) false) = b
tail (proj₂ (inF (frob b)) false) = frob b
head (proj₂ (inF (frob b)) true) = not b
tail (proj₂ (inF (frob b)) true) = frob (not b)

frobResponsive : ∀ {i} → (b : Bool) → AG {i} (EFₛ (map (_≡ true) (frob b) ))
nowA (frobResponsive false false) = notYetE (true , alreadyE refl)
nowA (frobResponsive false true) = alreadyE refl
nowA (frobResponsive true false) = alreadyE refl
nowA (frobResponsive true true) = notYetE (true , (alreadyE refl))
laterA (frobResponsive b false) = frobResponsive b
laterA (frobResponsive b true) = frobResponsive (not b)

-- Prove that a series of ⊤ is always true, under any circumstance
tautology : AG ⟨ returnReader ⊤ ⟩ ▻⋯
-- We create a cyclical stream of proofs
tautology = ⟨ const tt ⟩AG ▻AG

tautology₂ : ∀ {i} → AG {i} ⟨ returnReader ⊤ ⟩ ▻⋯
nowA (tautology₂ p) = tt
laterA (tautology₂ p) = tautology₂
-- p is the position of the first side effect


-- TODO Find something that this satisfies
identity : ∀ {A} → FStream (ReaderC A) A
identity = ⟨ ask ⟩ ▻⋯

alwaysGreen : ∀ {i} → FStream {i} (ReaderC Bool) Colour
alwaysGreen = ⟨ (returnReader green) ▻ returnReader green ⟩ ▻⋯

isAlwaysGreen : ∀ {i} → AG {i} (map (_≡ green) alwaysGreen)
nowA (isAlwaysGreen p) = refl
nowA (laterA (isAlwaysGreen p) p₁) = refl
laterA (laterA (isAlwaysGreen p) p₁) p₂ = isAlwaysGreen p
{-
nowA isAlwaysGreen _ = refl
nowA (laterA isAlwaysGreen _) _ = refl
laterA (laterA isAlwaysGreen _) _ = isAlwaysGreen
-}

isAlwaysGreen' : ∀ {i} → AG {i} (map (_≡ green) alwaysGreen)
isAlwaysGreen' = {!   !} -- TODO Would like to use bisimulation


isGreenOrRed : ∀ {i} → AG {i} (map (λ x → (x ≡ green) ⊎ (x ≡ red)) ⟨ returnReader green ▻ returnReader red ⟩ ▻⋯)
nowA (isGreenOrRed p) = inj₁ refl
nowA (laterA (isGreenOrRed p) p₁) = inj₂ refl
laterA (laterA (isGreenOrRed p) p₁) p₂ = isGreenOrRed p


trafficLight₄ : ∀ {i} → FStream {i} (ReaderC Bool) Bool
trafficLight₄ = ⟨ returnReader true ▻ ask ⟩ ▻⋯

liveness₄ : ∀ {i} → AG {i} (AFₛ (map (true ≡_) trafficLight₄))
nowA (liveness₄ p) = alreadyA refl
nowA (laterA (liveness₄ p) p₁) = notYetA (λ p₂ → alreadyA refl)
laterA (laterA (liveness₄ p) p₁) = liveness₄

responsivity : ∀ {i} → EG {i} (map (true ≡_) trafficLight₄)
proj₁ responsivity = false
nowE (proj₂ responsivity) = refl
proj₁ (laterE (proj₂ responsivity)) = true
nowE (proj₂ (laterE (proj₂ responsivity))) = refl
laterE (proj₂ (laterE (proj₂ responsivity))) = responsivity

responsivity₁ : ∀ {i} → EG {i} (map (true ≡_) trafficLight₄)
responsivity₁ = mapEG ⟨ refl ⟩EGᵢ ▻EG

responsivity₁' : ∀ {i} → EG {i} (map (true ≡_) trafficLight₄)
responsivity₁' = mapEG ⟨ refl ▻EGᵢ refl ⟩EGᵢ ▻EG

responsivity₂ : ∀ {i} → EG {i} (⟨ vmap (true ≡_) (returnReader true ▻ ask ⟩) ▻⋯)
proj₁ responsivity₂ = false
nowE (proj₂ responsivity₂) = refl
proj₁ (laterE (proj₂ responsivity₂)) = true
nowE (proj₂ (laterE (proj₂ responsivity₂))) = refl
laterE (proj₂ (laterE (proj₂ responsivity₂))) = responsivity₂


responsoSmall : EN (⟨ vmap (true ≡_) (returnReader true ▻ ask ⟩) ▻⋯)
proj₁ responsoSmall = true
proj₁ (proj₂ responsoSmall) = true
proj₂ (proj₂ responsoSmall) = refl

responso : AG (ENₛ (⟨ vmap (true ≡_) (returnReader true ▻ ask ⟩) ▻⋯))
nowA (responso p) with fmap EN'ₛ (inF ⟨ FCons (fmap (vmap' (λ section → true ≡ section)) (fmap (λ x → x , ask ⟩) (returnReader true))) ▻⋯)
nowA (responso p) | proj₃ , proj₄ with EN' (_aux_ ((true ≡ true) , FCons (tt , (λ x → (true ≡ x) , FNil))) (FCons (tt , (λ x → (true ≡ true) , FCons (tt , (λ x₁ → (true ≡ x₁) , FNil))))))
...   | bla = {!   !}
nowA (laterA (responso p) p₁) = {!   !}
laterA (laterA (responso p) p₁) p₂ = {!   !}

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
◇ C head (inF (tail
 (((true ≡ true) , FCons (tt , (λ x → (true ≡ x) , FNil))) aux
  FCons
  (tt ,
   (λ x → (true ≡ true) , FCons (tt , (λ x₁ → (true ≡ x₁) , FNil)))))))
◇ C head (inF
 (( FCons (tt , (λ x → (true ≡ x) , FNil))) pre⟨
  FCons
  (tt ,
   (λ x → (true ≡ true) , FCons (tt , (λ x₁ → (true ≡ x₁) , FNil))) ▻⋯ )))
◇ C head (fmap (_aux
  (FCons
  (tt ,
   (λ x → (true ≡ true) , FCons (tt , (λ x₁ → (true ≡ x₁) , FNil))) ▻⋯ ))) (tt , (λ x → (true ≡ x) , FNil)) )
◇ C head (tt , (λ x → (true ≡ x) , FNil) aux
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
nowA (alwaysEven p) = p , refl
laterA (alwaysEven p) = alwaysEven

alwaysEven₁ : ∀ {i} → AG {i} (map even timesTwo)
-- alwaysEven₁ = mapAG ([]AG pre⟨ {!   !} ▻AG) -- TODO Report internal error on refining
alwaysEven₁ = mapAG ⟨ (λ p → p) ⟩AG ▻AG
