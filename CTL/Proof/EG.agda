module CTL.Proof.EG where

open import CTL.Modalities.EG
open import FStream.Bisimulation
open import FStream.Core
open import FStream.FVec
open import Library

infixr 5 _▻EG_
infix 6 ⟨_▻EG
infix 7 _⟩EG

infixr 5 _▻EGᵢ_
infix 7 _⟩EGᵢ


data proofEG {ℓ₁ ℓ₂} {C : Container ℓ₁} : {n : ℕ} →
     (props : FVec C (Set ℓ₂) n) → Set (ℓ₁ ⊔ ℓ₂) where
  []EG : proofEG FNil
  ConsEG : ∀ {n} {props : ⟦ C ⟧ (Set ℓ₂ × FVec C (Set ℓ₂) n)} →
    E (fmap (λ x → (proj₁ x) × (proofEG (proj₂ x))) props) →
      proofEG (FCons props)


_pre⟨_▻EG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {m n}
              {props : FVec C (Set ℓ₂) m} {props' : FVec C (Set ℓ₂) (suc n)}
          → proofEG props
          → proofEG props'
          → EG {i} (props pre⟨ props' ▻⋯)
proj₁ ([]EG pre⟨ ConsEG (pos , _) ▻EG) = pos
nowE (proj₂ ([]EG pre⟨ ConsEG (_ , proof , _) ▻EG)) = proof
laterE (proj₂ ([]EG pre⟨ ConsEG (pos , proof , proofs) ▻EG)) =
  proofs pre⟨ ConsEG (pos , proof , proofs) ▻EG
proj₁ (ConsEG (pos , _) pre⟨ _ ▻EG) = pos
nowE   (proj₂ (ConsEG (pos , proof , proofs) pre⟨ _ ▻EG)) = proof
laterE (proj₂ (ConsEG (_   , _     , proofs) pre⟨ v ▻EG)) = proofs pre⟨ v ▻EG

-- TODO It's worth a thought whether we want to roll our own Sigma types
-- in order to have more meaningful projector names than projᵢ


⟨_▻EG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {n} {props : FVec C (Set ℓ₂) (suc n)}
      → proofEG props → EG {i} (FNil pre⟨ props ▻⋯)
⟨_▻EG = []EG pre⟨_▻EG

_⟩EG : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)}
     → E prop
     → proofEG (FCons (fmap (_, FNil) prop))
(pos , proof) ⟩EG = ConsEG (pos , (proof , []EG))

_⟩EGᵢ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)}
          {pos : Position C (proj₁ prop)}
      → proj₂ prop pos
      → proofEG (FCons (fmap (_, FNil) prop))
_⟩EGᵢ {pos = pos} proof = ConsEG (pos , (proof , []EG))


_▻EG_ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁}
        {prop : ⟦ C ⟧ (Set ℓ₂)} {n} {props : FVec C (Set ℓ₂) n}
      → E prop
      → proofEG props
      → proofEG (FCons (fmap (_, props) prop))
(pos , proof) ▻EG proofs = ConsEG (pos , (proof , proofs))


_▻EGᵢ_ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)} {n}
           {props : FVec C (Set ℓ₂) n} {pos : Position C (proj₁ prop)}
       → proj₂ prop pos
       → proofEG props
       → proofEG (FCons (fmap (_, props) prop))
_▻EGᵢ_ {pos = pos} proof proofs = ConsEG (pos , (proof , proofs))


mapEGlemma : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂}
               {f : A → Set ℓ₃} {m n}
           → (v : FVec C A m)
           → (v' : FVec C A (suc n))
           → EG {i} (vmap f v pre⟨ vmap f v' ▻⋯)
           → EG {i} (map f (v pre⟨ v' ▻⋯))
proj₁ (mapEGlemma FNil (FCons x) (pos , proof)) = pos
nowE (proj₂ (mapEGlemma FNil (FCons x) (pos , proofs))) = nowE proofs
laterE (proj₂ (mapEGlemma {f = f} FNil (FCons (shape , vals)) (pos , proof)))
  with vals pos
... | a , v = mapEGlemma v (FCons (shape , vals)) (laterE proof)
proj₁ (mapEGlemma (FCons (proj₃ , proj₄)) v' (pos , proofs)) = pos
nowE (proj₂ (mapEGlemma (FCons x) v' (pos , proofs))) = nowE proofs
laterE (proj₂ (mapEGlemma (FCons (shape , vals)) v' (pos , proofs)))
  with vals pos
... | a , v = mapEGlemma v v' (laterE proofs)


mapEG : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {f : A → Set ℓ₃}
          {m n} {v : FVec C A m} {v' : FVec C A (suc n)}
      → EG {i} ((vmap f v pre⟨ vmap f v' ▻⋯))
      → EG {i} (map f (v pre⟨ v' ▻⋯))
mapEG {v = v} {v' = v'} proofs = mapEGlemma v v' proofs


mutual
  -- TODO Rename to ∼EG?
  bisimEG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {s₁ s₂ : FStream C (Set ℓ₂)}
          → s₁ ~ s₂ → EG {i} s₁ → EG {i} s₂
  proj₁ (bisimEG {C = C} bs (pos , proofs)) =
    subst (Position C) (sameInitShapes bs) pos
  proj₂ (bisimEG bs (pos , proofs)) = bisimEG' (bisim bs pos) proofs

  bisimEG' : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {s₁ s₂ : FStream' C (Set ℓ₂)}
           → s₁ ~' s₂ → EG' {i} s₁ → EG' {i} s₂
  -- TODO This subst trick must already exist in stdlib somewhere
  nowE (bisimEG' bs proof) = subst (λ x → x) (hd∼ bs) (nowE proof)
  laterE (bisimEG' {C = C} bs proof) = bisimEG (tl∼ bs) (laterE proof)
