module CTL.Semantics where


open import Library
open import CTL.Modalities
open import CTL.ModalitiesIdeas
open import FStream.Core

record _⇔_ (A B : Set) : Set where -- Equivalence without setoids
  field
    l : A → B
    r : B → A
    right-inverse : ∀ x → r (l x) ≡ x
    left-inverse  : ∀ y → l (r y) ≡ y


record Positions (C : Container ℓ₀) : Set where
  field
    shape : Shape C
    position : Position C shape

data PositionVec {i} {ℓ} {C : Container ℓ} (fx : FStream {∞} C ⊤) : ℕ → Set ℓ where
  here : PositionVec fx zero
  there : ∀ {j : Size< i} {n} → (p : Position C (proj₁ (inF fx))) → PositionVec (tail (proj₂ (inF fx) p)) n → PositionVec fx (suc n)

lengthPV : ∀ {ℓ} {C : Container ℓ} {fx : FStream C ⊤} {n} → PositionVec fx n → ℕ
lengthPV {n = n} _ = n

record PosStream {ℓ} {C : Container ℓ} (fx : FStream C ⊤) : Set ℓ where
  coinductive
  field
    headPos : Position C (proj₁ (inF fx))
    tailPos : PosStream (tail (proj₂ (inF fx) headPos))
open PosStream

takePos : ∀ {ℓ} {C : Container ℓ} {fx : FStream C ⊤} → (n : ℕ) → PosStream fx → PositionVec fx n
takePos zero ps = here
takePos (suc n) ps = there (headPos ps) (takePos n (tailPos ps))

FStreamC : ∀ {ℓ} → Container ℓ → Container ℓ
Shape (FStreamC C) = FStream C ⊤
Position (FStreamC C) fx = Σ[ n ∈ ℕ ] PositionVec fx (suc n)

FStreamC' : ∀ {ℓ} → Container ℓ → Container ℓ
Shape (FStreamC' C) = FStream C ⊤
Position (FStreamC' C) fx = Σ[ n ∈ ℕ ] PositionVec fx n


onlyShapes : ∀ {i} {ℓ a} {A : Set a} {C : Container ℓ} → FStream {i} C A → FStream {i} C ⊤
onlyShapes as = map (const tt) as

onlyShapes' : ∀ {i} {ℓ a} {A : Set a} {C : Container ℓ} → FStream' {↑ i} C A → FStream {i} C ⊤
onlyShapes' as = onlyShapes (tail as)

posFun : ∀ {i} {ℓ a} {A : Set a} {C : Container ℓ} {n} → (s : FStream C A) → PositionVec {i} (onlyShapes s) (suc n) → A
posFun = {!   !}

posFun' : ∀ {i} {ℓ a} {A : Set a} {C : Container ℓ} {n} → (s : FStream' C A) → PositionVec {i} (onlyShapes' s) n → A
posFun' s here = head s
posFun' s (there p x) = posFun' (proj₂ (inF (tail s)) p) x

{-
containerize : ∀ {ℓ a} {A : Set a} {C : Container ℓ} → FStream C A → ⟦ FStreamC C ⟧ A
proj₁ (containerize as) = map(const tt) as
proj₂ (containerize as) (zero , there p here) = head (proj₂ (inF as) p)
proj₂ (containerize as) (suc n , there p v) = proj₂ (containerize (tail (proj₂ (inF as) p))) (n , v)
-}
{-proj₁ (containerize as) = map (const tt) as
proj₂ (containerize as) (here p) = head (proj₂ (inF as) p)
proj₂ (containerize as) (there p pc) = proj₂ (containerize (tail (proj₂ (inF as) p))) pc
-}
{-
containerize' : ∀ {ℓ a} {A : Set a} {C : Container ℓ} → FStream' C A → ⟦ FStreamC' C ⟧ A
proj₁ (containerize' as) = proj₁ (containerize (tail as))
proj₂ (containerize' as) (zero , here) = head as
proj₂ (containerize' as) (suc n , there p v) = proj₂ (containerize' (proj₂ (inF (tail as)) p)) (n , v)
-- TODO Can't we implement this by ping pong to containerize?
-}
{-
proj₁ (containerize' as) = proj₁ (containerize (tail as))
proj₂ (containerize' as) (inj₁ tt) = head as
proj₂ (containerize' as) (inj₂ y) = proj₂ (containerize (tail as)) y
-}

embed : Bool → Set
embed true  = ⊤
embed false = ⊥

-- TODO Add sufficient universe polymorphism
_,_⊨_ : ∀ {C : Container ℓ₀} {n} → (fx : FStream C ⊤) → (pos : PositionVec fx (suc n)) → (s : ∀ {m} → PositionVec fx (suc m) → Set) → Set
fx , pos ⊨ s = s pos

_,_⊨'_ : ∀ {i} {C : Container ℓ₀} {n} → (fx : FStream C ⊤) → (pos : PositionVec {i} fx n) → (s : ∀ {m} → PositionVec {i} fx m → Set) → Set
fx , pos ⊨' s = s pos


_at_ : ∀ {i} {C : Container ℓ₀} {n} → (s : FStream C Set) → (pos : PositionVec {i} (onlyShapes s) (suc n)) → Set
_at_ {i = i} s pos = {!   !} -- (onlyShapes {i} s) , pos ⊨ posFun s
--(λ x → proj₂ (containerize s) ({! suc  !} , x)) --(λ x → proj₂ (containerize s) (n , x))
-- (proj₁ (containerize s)) , pos ⊨ (proj₂ (containerize s))

_at'_ : ∀ {i} {C : Container ℓ₀} {n} → (s : FStream' C Set) → (pos : PositionVec {i} (onlyShapes' s) n) → Set
_at'_ {i = i} {n = n} s pos = (onlyShapes' s) , pos ⊨' posFun' s --(λ x → proj₂ (containerize' s) ((lengthPV x) , x)) --(λ x → proj₂ (containerize' s) (n , x))
-- (proj₁ (containerize' s)) , {!   !} ⊨ (proj₂ {! containerize' s  !})


⊨now : ∀ {C : Container ℓ₀} → (s : FStream C Set) → Set
⊨now s = ∀ p → s at (there p here) -- ∀ p → s at (here p)
-- TODO Rewrite with modalities?
⊨now' : ∀ {C : Container ℓ₀} → (s : FStream' C Set) → Set
⊨now' {i} s =  _at'_ s here

semAG' : ∀ {i} {C : Container ℓ₀} → (s : FStream' C Set) → Set
semAG' {i} s = ∀ {n} → (pVec : PositionVec {i} (onlyShapes' s) n) → s at' pVec


semAG'tail : ∀ {i} {C : Container ℓ₀} → {s : FStream' C Set} → semAG' {i} s → APred (semAG' {i}) (inF (tail s))
semAG'tail proof p here = {!   !}
semAG'tail proof p (there p₁ pVec) = {!   !}


semAG : ∀ {C : Container ℓ₀} → (s : FStream C Set) → Set
semAG s = ∀ {n} → (pVec : PositionVec (onlyShapes s) (suc n)) → s at pVec

semAG'correct : ∀ {i} {C : Container ℓ₀} {s : FStream' C Set} → (⊨now' (AGₛ' s)) ⇔ semAG' {i} s
_⇔_.l semAG'correct agProof here = nowA' agProof
_⇔_.l semAG'correct agProof (there p v) = _⇔_.l semAG'correct (laterA' agProof p) v
nowA' (_⇔_.r semAG'correct semProof) = semProof here
laterA' (_⇔_.r (semAG'correct {i}) semProof) {j} p = _⇔_.r semAG'correct (semAG'tail {! semProof  !} {!   !})
_⇔_.right-inverse semAG'correct = {!   !}
_⇔_.left-inverse semAG'correct = {!   !}

semAGcorrect : ∀ {i} {C : Container ℓ₀} {s : FStream C Set} → (⊨now (AGₛ s)) ⇔ semAG s
_⇔_.l semAGcorrect agProof (there p here) = nowA' (agProof p)
_⇔_.l semAGcorrect agProof (there p (there p₁ pVec)) = _⇔_.l semAGcorrect (laterA' (agProof {!   !})) {! pVec  !}
_⇔_.r semAGcorrect semProof p = {!   !}
_⇔_.right-inverse semAGcorrect = {!   !}
_⇔_.left-inverse semAGcorrect = {!   !}
{-
_⇔_.l semAG agProof (here p) = {!   !}
_⇔_.l semAG agProof (there p pVec) = {!   !}
_⇔_.r semAG semProof p = r semProof p
  where
    r : ∀ {C : Container ℓ₀} {s : FStream C Set} {pos : PositionVec (proj₁ (containerize s))} → (∀ pVec → s at pVec) → (p : Position C (proj₁ (inF s))) → (AGₛ s) at here p
    -- Position .C (proj₁ (fmap (map' (const tt)) (fmap AGₛ' (inF .s))))
    -- Position .C (proj₁ (fmap (map' (const tt)) (AGₛ s)))
    nowA' (r semProof pos₁) = semProof (here pos₁)
    laterA' (r semProof pos₁) pos₂ = {! r  !}
_⇔_.right-inverse semAG = {!   !}
_⇔_.left-inverse semAG = {!   !}
-}
{-
cont : Container ℓ₀ → Set → Set₁
cont C B = (B → FStream' C Set) → FStream' C Set

_,_⊨_ : ∀ {B : Set} → (C : Container ℓ₀) → (B → FStream' C Bool) → cont C B → Set
C , valuation ⊨ expr = head (expr (map' embed ∘ valuation))


atom : ∀ {C} {B : Set} → B → cont C B
atom b g = g b

op : ∀ {C : Container ℓ₀} {B : Set} → (FStream' C Set → FStream' C Set) → cont C B → cont C B
op f c = f ∘ c

ag : ∀ {C} {valuation} {expr} → (C , valuation ⊨ op AGₛ' expr) ⇔ ({!   !} ,{!   !} ⊨ {!   !})
ag = {!   !}
-}









--
