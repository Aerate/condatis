module CTL.Proof.AG where

open import CTL.Modalities.AG
open import FStream.Core
open import FStream.FVec
open import Library

-- TODO Maybe beautify syntax here and elsewhere
data proofAG' {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂} : {n : ℕ} →
     (props : FVec' C (Set ℓ₃) n) → Set (ℓ₂ ⊔ ℓ₃) where
  []AG'  : proofAG' FNil'
  _▻AG'_ : ∀ {prop : Set ℓ₃} {n} {props : ⟦ C ⟧ (FVec' C (Set ℓ₃) n)} →
           prop → A (fmap proofAG' props) → proofAG' (FCons' prop props)


_pre⟨_▻AG' : ∀ {i ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂} {m n}
               {props : FVec' C (Set ℓ₃) m} {props' : FVec' C (Set ℓ₃) (suc n)}
            → proofAG' props → proofAG' props'
            → AG' {i} (props pre⟨ props' ▻⋯')
nowA ([]AG' pre⟨ (proof ▻AG' _) ▻AG') = proof
laterA ([]AG' pre⟨ (proof ▻AG' proofs) ▻AG') p =
  (proofs p) pre⟨ (proof ▻AG' proofs) ▻AG'
nowA ((proof ▻AG' _) pre⟨ _ ▻AG') = proof
laterA ((_ ▻AG' proofs) pre⟨ proofs' ▻AG') p =
  (proofs p) pre⟨ proofs' ▻AG'


⟨_▻AG' : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂} {n}
           {props : FVec' C (Set ℓ₃) (suc n)}
       → proofAG' props → AG' {i} (FNil' pre⟨ props ▻⋯')
⟨ proofs ▻AG' = []AG' pre⟨ proofs ▻AG'


data proofAG {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂} : {n : ℕ} →
     (props : FVec C (Set ℓ₃) n) → Set (ℓ₂ ⊔ ℓ₃) where
  []AG : proofAG FNil
  ConsAG : ∀ {n} {props : ⟦ C ⟧ (Set ℓ₃ × FVec C (Set ℓ₃) n)} →
    A (fmap (λ x → (proj₁ x) × (proofAG (proj₂ x))) props) → proofAG (FCons props)
  -- TODO This constructor type signature is an abomination and should be somehow rewritten with proofAG, but how??
  -- TODO props should be of type FVec C (Set ℓ₃) (suc n) maybe? Or is it easier this way?


mapAGlemma : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
             {A : Set ℓ₃} {f : A → Set ℓ₃} {m n} →
             (v : FVec C A m) →
             (v' : FVec C A (suc n)) →
             AG {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) →
             AG {i} (map f (v pre⟨ v' ▻⋯))
nowA (mapAGlemma FNil (FCons x) proofs p) = nowA (proofs p) -- TODO Why can't I join this with the next line?
nowA (mapAGlemma (FCons x) v proofs p) = nowA (proofs p)
laterA (mapAGlemma FNil (FCons (shape , vals)) proofs p) p₁ =
  mapAGlemma (proj₂ (vals p)) (FCons (shape , vals)) (laterA (proofs p)) p₁
laterA (mapAGlemma (FCons (shape , vals)) v' proofs p) p₁ =
  mapAGlemma (proj₂ (vals p)) v' (laterA (proofs p)) p₁

mapAG : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
          {A : Set ℓ₃} {f : A → Set ℓ₃} {m n} →
        {v : FVec C A m} →
        {v' : FVec C A (suc n)} →
        AG {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) →
        AG {i} (map f (v pre⟨ v' ▻⋯))
mapAG {v = v} {v' = v'} = mapAGlemma v v'


_pre⟨_▻AG : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂} {m n}
              {props : FVec C (Set ℓ₃) m} {props' : FVec C (Set ℓ₃) (suc n)}
          → proofAG props
          → proofAG props'
          → AG {i} (props pre⟨ props' ▻⋯)
nowA ( ([]AG pre⟨ (ConsAG proofs) ▻AG) p) = proj₁ (proofs p)
laterA ( ([]AG pre⟨ (ConsAG proofs) ▻AG) p) p₁ =
  (proj₂ (proofs p) pre⟨ ConsAG proofs ▻AG) p₁
nowA ( ((ConsAG proofs) pre⟨ _ ▻AG) p) = proj₁ (proofs p)
laterA ( ((ConsAG proofs) pre⟨ proofs' ▻AG) p) p₁ =
  (proj₂ (proofs p) pre⟨ proofs' ▻AG) p₁
-- The p are the inputs (positions) from the side effects.

mapPreCycle : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂} {A : Set ℓ₃}
                {f : A → Set ℓ₃} {m n}
            → (v : FVec C A m) → (v' : FVec C A (suc n))
            → proofAG (vmap f v) → proofAG (vmap f v')
            → AG {i} (map f (v pre⟨ v' ▻⋯))
nowA (mapPreCycle FNil (FCons x) []AG (ConsAG proofs) p)
      with proofs p
...   | proof , proofs' = proof
laterA (mapPreCycle FNil (FCons (shape , vals)) []AG (ConsAG proofs) p) p'
      with proofs p
...   | proof , proofs'
      with vals p
...   | a , v = mapPreCycle v (FCons (shape , vals)) proofs' (ConsAG proofs) p'
nowA (mapPreCycle (FCons x) v' (ConsAG proofs) proofs' p) = proj₁ (proofs p)
laterA (mapPreCycle (FCons (shape , vals)) (FCons x) (ConsAG proofs) proofs' p) p₁
      with proofs p
...   | proof , proofs''
      with vals p
...   | a , v = mapPreCycle v (FCons x) proofs'' proofs' p₁


infixr 5 _▻AG_
infix 6 ⟨_▻AG
infix 7 _⟩AG


⟨_▻AG : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂} {n}
      → {props : FVec C (Set ℓ₃) (suc n)}
      → proofAG props
      → AG {i} (FNil pre⟨ props ▻⋯)
⟨_▻AG = []AG pre⟨_▻AG


_⟩AG : ∀ {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂} {prop : ⟦ C ⟧ (Set ℓ₃)}
     → A prop
     → proofAG (FCons (fmap (_, FNil) prop))
x ⟩AG = ConsAG (λ p → x p , []AG)


_▻AG_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁ ℓ₂}
          {prop : ⟦ C ⟧ (Set ℓ₃)} {n} {props : FVec C (Set ℓ₃) n}
      → A prop → proofAG props
      → proofAG (FCons (fmap (_, props) prop))
x ▻AG v = ConsAG (λ p → (x p) , v)
