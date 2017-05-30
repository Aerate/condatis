------------------------------------------------------------------------
-- Modalities that quantify over all paths (A)
------------------------------------------------------------------------

module CTL.A where

open import FStream.Core
open import Library

-- Always Certain : s ⊧ φ ⇔ ∀ p ∀ s ∈ p ⊧ φ
{-# NO_POSITIVITY_CHECK #-}
record AG' {i : Size} {ℓ₁ ℓ₂} {C : Container ℓ₁}
  (props : FStream' {∞} C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    nowA' : head props
    laterA' : {j : Size< i} → A (fmap AG' (inF (tail props)))
open AG' public

AG : ∀ {i : Size} {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {∞} C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AG props = APred AG' (inF props)


-- Always Possible : s ⊧ φ ⇔ ∀ p ∃ s ∈ p ⊧ φ
data AF {ℓ₁ ℓ₂} {C : Container ℓ₁}
     (cas : FStream C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyA : A (fmap head (inF cas)) → AF cas
  notYetA : APred AF (fmap (λ x → tail x) (inF cas)) → AF cas
open AF public

data AF' {i} {ℓ₁ ℓ₂} {C : Container ℓ₁}
     (cas : FStream' {i} C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyA' : head cas → AF' cas
  notYetA' :  {j : Size< i} →  A (fmap AF' (inF (tail cas))) → AF' cas
open AF' public


-- Always (in) Next : p ⊧ φ ⇔ p[1] ⊧ φ
AN' : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} →
      FStream' C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AN' s = APred head (inF (tail s))

AN : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} →
     FStream C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AN s = APred AN' (inF s)


-- TODO AN' won't work with sizes
{-# NON_TERMINATING #-}
AN'ₛ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} →
       FStream' C (Set ℓ₂) → FStream' C (Set (ℓ₁ ⊔ ℓ₂))
head (AN'ₛ s) = AN' s
inF (tail (AN'ₛ s)) = fmap AN'ₛ (inF (tail s))


-- TODO check semantics
data _AU'_ {ℓ₁ ℓ₂} {C : Container ℓ₁}
     (props₁ props₂ : FStream' C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  finallyA : head props₁ → props₁ AU' props₂
  _untilA_ : head props₂ → AN'ₛ props₁ AU' AN'ₛ props₂ → props₁ AU' props₂

AU : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream C (Set ℓ₂) →
     FStream C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
AU s₁ s₂ =  APred (λ x → APred (λ y → x AU' y) (inF s₁)) (inF s₂)


-- TODO Unnecessary?
initA : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} →
        FStream {i} C (Set ℓ₂) →
        FStream' {i} C (Set (ℓ₁ ⊔ ℓ₂))
head (initA {i} {ℓ₁} {ℓ₂} {C} cas) = A {ℓ₁} {ℓ₂} (fmap head (inF {i} cas))
inF (tail (initA cas)) = fmap (initA ∘ (λ as → tail as)) (inF cas)


-- TODO In separate file?
module ProofA where

open import FStream.FVec

data proofAG' {ℓ₁ ℓ₂} {C : Container ℓ₁} : {n : ℕ} →
     (props : FVec' C (Set ℓ₂) n) → Set (ℓ₁ ⊔ ℓ₂) where
  []AG'  : proofAG' FNil'
  _▻AG'_ : ∀ {prop : Set ℓ₂} {n} {props : ⟦ C ⟧ (FVec' C (Set ℓ₂) n)} →
           prop → A (fmap proofAG' props) → proofAG' (FCons' prop props)


-- TODO Unify syntax with other examples
_preCycleAG'_ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {m n}
                {props : FVec' C (Set ℓ₂) m}
                {props' : FVec' C (Set ℓ₂) (suc n)} →
                proofAG' props →
                proofAG' props' →
                AG' {i} (props pre⟨ props' ▻⋯')
nowA' ([]AG' preCycleAG' (proof ▻AG' _)) = proof
laterA' ([]AG' preCycleAG' (proof ▻AG' proofs)) p =
  (proofs p) preCycleAG' (proof ▻AG' proofs)
nowA' ((proof ▻AG' _) preCycleAG' _) = proof
laterA' ((_ ▻AG' proofs) preCycleAG' proofs') p =
  (proofs p) preCycleAG' proofs'


cycleAG' : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {n}
           {props : FVec' C (Set ℓ₂) (suc n)} →
           proofAG' props →
           AG' {i} (FNil' pre⟨ props ▻⋯')
cycleAG' proofs = []AG' preCycleAG' proofs


data proofAG {ℓ₁ ℓ₂} {C : Container ℓ₁} : {n : ℕ} →
     (props : FVec C (Set ℓ₂) n) → Set (ℓ₁ ⊔ ℓ₂) where
  []AG : proofAG FNil
  ConsAG : ∀ {n} {props : ⟦ C ⟧ (Set ℓ₂ × FVec C (Set ℓ₂) n)} →
    A (fmap (λ x → (proj₁ x) × (proofAG (proj₂ x))) props) → proofAG (FCons props)
  -- TODO This constructor type signature is an abomination and should be somehow rewritten with proofAG, but how??
  -- TODO props should be of type FVec C (Set ℓ₂) (suc n) maybe? Or is it easier this way?


mapAGlemma : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁}
             {A : Set ℓ₂} {f : A → Set ℓ₃} {m n} →
             (v : FVec C A m) →
             (v' : FVec C A (suc n)) →
             AG {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) →
             AG {i} (map f (v pre⟨ v' ▻⋯))
nowA' (mapAGlemma FNil (FCons x) proofs p) = nowA' (proofs p)
nowA' (mapAGlemma (FCons x) v proofs p) = nowA' (proofs p)
laterA' (mapAGlemma FNil (FCons (shape , vals)) proofs p) p₁ =
  mapAGlemma (proj₂ (vals p)) (FCons (shape , vals)) (laterA' (proofs p)) p₁
laterA' (mapAGlemma (FCons (shape , vals)) v' proofs p) p₁ =
  mapAGlemma (proj₂ (vals p)) v' (laterA' (proofs p)) p₁

mapAG : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁}
        {A : Set ℓ₂} {f : A → Set ℓ₃} {m n} →
        {v : FVec C A m} →
        {v' : FVec C A (suc n)} →
        AG {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) →
        AG {i} (map f (v pre⟨ v' ▻⋯))
mapAG {v = v} {v' = v'} = mapAGlemma v v'

{-
mapAG : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set (lsuc ℓ₃)} {f : A → Set ℓ₃} {m n} → {v : FVec C A m} → {v' : FVec C A (suc n)} → AG {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) → AG {i} (map f (v pre⟨ v' ▻⋯))
nowA' (mapAG proof pos) = nowA' (proof pos)
laterA' (mapAG x p) = {!   !}
-}

_pre⟨_▻AG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {m n}
            {props : FVec C (Set ℓ₂) m} →
            {props' : FVec C (Set ℓ₂) (suc n)} →
            proofAG props →
            proofAG props' →
            AG {i} (props pre⟨ props' ▻⋯)
nowA' ( ([]AG pre⟨ (ConsAG proofs) ▻AG) p) = proj₁ (proofs p)
laterA' ( ([]AG pre⟨ (ConsAG proofs) ▻AG) p) p₁ =
  (proj₂ (proofs p) pre⟨ ConsAG proofs ▻AG) p₁
nowA' ( ((ConsAG proofs) pre⟨ _ ▻AG) p) = proj₁ (proofs p)
laterA' ( ((ConsAG proofs) pre⟨ proofs' ▻AG) p) p₁ =
  (proj₂ (proofs p) pre⟨ proofs' ▻AG) p₁
-- The p are the inputs (positions) from the side effects.

mapPreCycle : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁}
              {A : Set ℓ₂} {f : A → Set ℓ₃} {m n}
              (v : FVec C A m) →
              (v' : FVec C A (suc n)) →
              proofAG (vmap f v) →
              proofAG (vmap f v') →
              AG {i} (map f (v pre⟨ v' ▻⋯))
nowA' (mapPreCycle FNil (FCons x) []AG (ConsAG proofs) p)
      with proofs p
...   | proof , proofs' = proof
laterA' (mapPreCycle FNil (FCons (shape , vals)) []AG (ConsAG proofs) p) p'
      with proofs p
...   | proof , proofs'
      with vals p
...   | a , v = mapPreCycle v (FCons (shape , vals)) proofs' (ConsAG proofs) p'
nowA' (mapPreCycle (FCons x) v' (ConsAG proofs) proofs' p) = proj₁ (proofs p)
laterA' (mapPreCycle (FCons (shape , vals)) (FCons x) (ConsAG proofs) proofs' p) p₁
      with proofs p
...   | proof , proofs''
      with vals p
...   | a , v = mapPreCycle v (FCons x) proofs'' proofs' p₁


infixr 5 _▻AG_
infix 6 ⟨_▻AG
infix 7 _⟩AG


⟨_▻AG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {n}
        {props : FVec C (Set ℓ₂) (suc n)} →
        proofAG props →
        AG {i} (FNil pre⟨ props ▻⋯)
⟨_▻AG = []AG pre⟨_▻AG


_⟩AG : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁}
       {prop : ⟦ C ⟧ (Set ℓ₂)} →
       A prop →
       proofAG (FCons (fmap (_, FNil) prop))
x ⟩AG = ConsAG (λ p → x p , []AG)


_▻AG_ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁}
        {prop : ⟦ C ⟧ (Set ℓ₂)} {n}
        {props : FVec C (Set ℓ₂) n} →
        A prop → proofAG props →
        proofAG (FCons (fmap (_, props) prop))
x ▻AG v = ConsAG (λ p → (x p) , v)

open ProofA public
