module CTL.Proof where

open import Relation.Binary.PropositionalEquality

open import Library
open import FStream.FVec
open import FStream.Bisimulation-alt
open import FStream.Core
open import CTL.Modalities

data proofAG' {ℓ₁ ℓ₂} {C : Container ℓ₁} : {n : ℕ} → 
     (props : FVec' C (Set ℓ₂) n) → Set (ℓ₁ ⊔ ℓ₂) where
  []AG' : proofAG' FNil'
  _▻AG'_ : ∀ {prop : Set ℓ₂} {n} {props : ⟦ C ⟧ (FVec' C (Set ℓ₂) n)} → 
    prop → A (fmap proofAG' props) → proofAG' (FCons' prop props)


_preCycleAG'_ : ∀ {i ℓ₁ ℓ₂} {C : Container ℓ₁} {m n} {props : FVec' C (Set ℓ₂) m} 
                {props' : FVec' C (Set ℓ₂) (suc n)} → 
                proofAG' props → proofAG' props' → AG' {i} (props pre⟨ props' ▻⋯')
nowA' ([]AG' preCycleAG' (proof ▻AG' _)) = proof
laterA' ([]AG' preCycleAG' (proof ▻AG' proofs)) p = (proofs p) preCycleAG' (proof ▻AG' proofs)
nowA' ((proof ▻AG' _) preCycleAG' _) = proof
laterA' ((_ ▻AG' proofs) preCycleAG' proofs') p = (proofs p) preCycleAG' proofs'

cycleAG' : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {n} {props : FVec' C (Set ℓ₂) (suc n)} → 
           proofAG' props → AG' {i} (FNil' pre⟨ props ▻⋯')
cycleAG' proofs = []AG' preCycleAG' proofs

data proofAG {ℓ₁ ℓ₂} {C : Container ℓ₁} : {n : ℕ} → 
     (props : FVec C (Set ℓ₂) n) → Set (ℓ₁ ⊔ ℓ₂) where
  []AG : proofAG FNil
  ConsAG : ∀ {n} {props : ⟦ C ⟧ (Set ℓ₂ × FVec C (Set ℓ₂) n)} → 
    A (fmap (λ x → (proj₁ x) × (proofAG (proj₂ x))) props) → proofAG (FCons props)
  -- TODO This constructor type signature is an abomination and should be somehow rewritten with proofAG, but how??
  -- TODO props should be of type FVec C (Set ℓ₂) (suc n) maybe? Or is it easier this way?



{-
mapAG : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {f : A → Set ℓ₃} {m n} → (v : FVec C A m) → (v' : FVec C A (suc n)) → AG {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) → AG {i} (map f (v pre⟨ v' ▻⋯))
nowA' (mapAG FNil (FCons x) proofs p) = nowA' (proofs p)
nowA' (mapAG (FCons x) v proofs p) = nowA' (proofs p)
laterA' (mapAG FNil (FCons (shape , vals)) proofs p) p₁ with vals p
... | a , v = mapAG v (FCons (shape , vals)) (laterA' (subst (λ x → {!   !}) refl (proofs p))) p₁
-- laterA' (mapAG FNil v' proof p) p₁ = mapAG ({!   !}) (FCons {!   !}) (λ p₂ → laterA' (proof {!   !}) {!   !}) {!   !}
laterA' (mapAG (FCons x) v' proofs p) p₁ = {!   !}
-}

{-
mapAG : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set (lsuc ℓ₃)} {f : A → Set ℓ₃} {m n} → {v : FVec C A m} → {v' : FVec C A (suc n)} → AG {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) → AG {i} (map f (v pre⟨ v' ▻⋯))
nowA' (mapAG proof pos) = nowA' (proof pos)
laterA' (mapAG x p) = {!   !}
-}

_pre⟨_▻AG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {m n} {props : FVec C (Set ℓ₂) m} → 
            {props' : FVec C (Set ℓ₂) (suc n)} → 
            proofAG props → proofAG props' → AG {i} (props pre⟨ props' ▻⋯)
nowA' ( ([]AG pre⟨ (ConsAG proofs) ▻AG) p) = proj₁ (proofs p)
laterA' ( ([]AG pre⟨ (ConsAG proofs) ▻AG) p) p₁ = (proj₂ (proofs p) pre⟨ ConsAG proofs ▻AG) p₁
nowA' ( ((ConsAG proofs) pre⟨ _ ▻AG) p) = proj₁ (proofs p)
laterA' ( ((ConsAG proofs) pre⟨ proofs' ▻AG) p) p₁ = (proj₂ (proofs p) pre⟨ proofs' ▻AG) p₁
-- The p are the inputs (positions) from the side effects.

mapprecycle : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {f : A → Set ℓ₃} {m n} 
              (v : FVec C A m) → (v' : FVec C A (suc n)) → proofAG (vmap f v) → 
              proofAG (vmap f v') → AG {i} (map f (v pre⟨ v' ▻⋯))

nowA' (mapprecycle FNil (FCons x) []AG (ConsAG proofs) p) with proofs p
...                                                          | proof , proofs' = proof
laterA' (mapprecycle FNil (FCons (shape , vals)) []AG (ConsAG proofs) p) p' with proofs p
... | proof , proofs' with vals p
...                    | a , v = mapprecycle v (FCons (shape , vals)) proofs' (ConsAG proofs) p'
nowA' (mapprecycle (FCons x) v' (ConsAG proofs) proofs' p) = proj₁ (proofs p)
laterA' (mapprecycle (FCons (shape , vals)) (FCons x) (ConsAG proofs) proofs' p) p₁ with proofs p
... | proof , proofs'' with vals p
...                       | a , v = mapprecycle v (FCons x) proofs'' proofs' p₁

⟨_▻AG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {n} {props : FVec C (Set ℓ₂) (suc n)} → 
        proofAG props → AG {i} (FNil pre⟨ props ▻⋯)
⟨_▻AG = []AG pre⟨_▻AG

-- _⟩AG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁}

data proofEG {ℓ₁ ℓ₂} {C : Container ℓ₁} : {n : ℕ} → 
     (props : FVec C (Set ℓ₂) n) → Set (ℓ₁ ⊔ ℓ₂) where

  []EG : proofEG FNil

  ConsEG : ∀ {n} {props : ⟦ C ⟧ (Set ℓ₂ × FVec C (Set ℓ₂) n)} → 
    E (fmap (λ x → (proj₁ x) × (proofEG (proj₂ x))) props) → proofEG (FCons props)


_pre⟨_▻EG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {m n} {props : FVec C (Set ℓ₂) m} → 
            {props' : FVec C (Set ℓ₂) (suc n)} → 
            proofEG props → proofEG props' → EG {i} (props pre⟨ props' ▻⋯)
proj₁ ([]EG pre⟨ ConsEG (pos , _) ▻EG) = pos
nowE' (proj₂ ([]EG pre⟨ ConsEG (_ , proof , _) ▻EG)) = proof
laterE' (proj₂ ([]EG pre⟨ ConsEG (pos , proof , proofs) ▻EG)) = proofs pre⟨ ConsEG (pos , proof , proofs) ▻EG
proj₁ (ConsEG (pos , _) pre⟨ _ ▻EG) = pos
nowE'   (proj₂ (ConsEG (pos , proof , proofs) pre⟨ _ ▻EG)) = proof
laterE' (proj₂ (ConsEG (_   , _     , proofs) pre⟨ v ▻EG)) = proofs pre⟨ v ▻EG

-- TODO It's worth a thought whether we want to roll our own Sigma types
-- in order to have more meaningful projector names than projᵢ

infixr 5 _▻EG_
infix 6 ⟨_▻EG
infix 7 _⟩EG

infixr 5 _▻EG₁_
infix 7 _⟩EG₁



⟨_▻EG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {n} {props : FVec C (Set ℓ₂) (suc n)} → 
        proofEG props → EG {i} (FNil pre⟨ props ▻⋯)
⟨_▻EG = []EG pre⟨_▻EG

_⟩EG : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)} → 
       E prop → proofEG (FCons (fmap (_, FNil) prop))
(pos , proof) ⟩EG = ConsEG (pos , (proof , []EG))

_⟩EG₁ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)} → 
        {pos : Position C (proj₁ prop)} → 
        proj₂ prop pos → proofEG (FCons (fmap (_, FNil) prop))
_⟩EG₁ {pos = pos} proof = ConsEG (pos , (proof , []EG))


-- TODO
_▻EG_ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)} {n} 
        {props : FVec C (Set ℓ₂) n} → 
        E prop → proofEG props → proofEG (FCons (fmap (_, props) prop))
(pos , proof) ▻EG proofs = ConsEG (pos , (proof , proofs))

_▻EG₁_ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)} {n} 
         {props : FVec C (Set ℓ₂) n} → {pos : Position C (proj₁ prop)} → 
         proj₂ prop pos → proofEG props → proofEG (FCons (fmap (_, props) prop))
_▻EG₁_ {pos = pos} proof proofs = ConsEG (pos , (proof , proofs))

mapEG₁ : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {f : A → Set ℓ₃} {m n} → 
         (v : FVec C A m) → (v' : FVec C A (suc n)) → 
         EG {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) → EG {i} (map f (v pre⟨ v' ▻⋯))
proj₁ (mapEG₁ FNil (FCons x) (pos , proof)) = pos
nowE' (proj₂ (mapEG₁ FNil (FCons x) (pos , proofs))) = nowE' proofs
laterE' (proj₂ (mapEG₁ {f = f} FNil (FCons (shape , vals)) (pos , proof))) with vals pos
... | a , v = mapEG₁ v (FCons (shape , vals)) (laterE' proof)
proj₁ (mapEG₁ (FCons (proj₃ , proj₄)) v' (pos , proofs)) = pos
nowE' (proj₂ (mapEG₁ (FCons x) v' (pos , proofs))) = nowE' proofs
laterE' (proj₂ (mapEG₁ (FCons (shape , vals)) v' (pos , proofs))) with vals pos
... | a , v = mapEG₁ v v' (laterE' proofs)

mapEG : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {f : A → Set ℓ₃} {m n} → 
        {v : FVec C A m} → {v' : FVec C A (suc n)} → 
        EG {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) → EG {i} (map f (v pre⟨ v' ▻⋯))
mapEG {v = v} {v' = v'} proofs = mapEG₁ v v' proofs

mutual
  bisimEG  : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {s₁ s₂ : FStream {i} C (Set ℓ₂)} →
             s₁ ~ s₂ → EG {i} s₁ → EG {i} s₂
  proj₁ (bisimEG {C = C} bs (pos , proofs)) = subst (Position C) (sameInitShapes bs) pos
  proj₂ (bisimEG bs (pos , proofs)) = bisimEG' (bisim bs pos) proofs

  bisimEG' : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {s₁ s₂ : FStream' {i} C (Set ℓ₂)} →
             s₁ ~' s₂ → EG' {i} s₁ → EG' {i} s₂
  nowE' (bisimEG' bs proof) = subst id (hd∼ bs) (nowE' proof) 
  laterE' (bisimEG' {C = C} bs proof) =  bisimEG (tl∼ bs) (laterE' proof) 

lem2 : ∀ {a p} {A : Set a} {x y : A} → (P : A → Set p) → {py : P y} → (x≡y : x ≡ y) → 
       subst P x≡y (subst P (sym x≡y) py) ≡ py  
lem2 P refl = refl

mutual
  bisimAG  : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {s₁ s₂ : FStream {i} C (Set ℓ₂)} →
              s₁ ~ s₂ → AG {i} s₁ → AG {i} s₂
  bisimAG {C = C} x xs p with (subst (Position C) (sym (sameInitShapes x)) p) 
  ... | p' = bisimAG' (bisim (subst {!!} (lem2 {!!} (sameInitShapes {!x!})) x) p') (xs p')
--  ... | q = bisimAG'  (bisim {!x!} q) (xs q)  

    where 
      lem : subst (Position C) (sameInitShapes x) ((subst (Position C) (sym (sameInitShapes x)) p)) ≡ p 
      lem = lem2 (Position C) (sameInitShapes x)
    --= bisimAG' (bisim {! !}  p') (xs p') --(bisim {!x!} p) (xs p')

-- (Position C (proj₁ (inF .s₂)))
--bisimAG' (bisim {!!} (subst {!!} (sym (sameInitShapes x)) p)) (xs (subst (Position C) (sym (sameInitShapes x)) p))

  bisimAG' : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {s₁ s₂ : FStream' {i} C (Set ℓ₂)} →
             s₁ ~' s₂ → AG' {i} s₁ → AG' {i} s₂
  nowA' (bisimAG' x xs) = subst id (hd∼ x) (nowA' xs) 
  laterA' (bisimAG' {C = C} x xs) = bisimAG (tl∼ x) (laterA' xs) 

{-
-- TODO Rather write as mutual with a map∼'
map∼Lemma : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃} {f : A → B} {m n} → (v : FVec C A m) → (v' : FVec C A (suc n)) → ((vmap f v pre⟨ vmap f v' ▻⋯)) ~ (map {i} f (v pre⟨ v' ▻⋯))
sameInitShapes (map∼Lemma FNil (FCons x)) = refl
sameInitShapes (map∼Lemma (FCons x) v') = refl
hd∼ (bisim (map∼Lemma FNil (FCons x)) pos) = refl
tl∼ (bisim (map∼Lemma FNil (FCons (shape , av))) pos) {j} = map∼Lemma {j} (proj₂ (av pos)) (FCons (shape , av)) -- TODO Beautify with with
hd∼ (bisim (map∼Lemma (FCons x) (FCons x₁)) pos) = refl
tl∼ (bisim (map∼Lemma (FCons (shape , av)) v') pos) {j} = map∼Lemma {j} (proj₂ (av pos)) v'

-- TODO Eradicate the previous lemma with with on implicit arguments
map∼ : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃} {f : A → B} {m n} → {v : FVec C A m} → {v' : FVec C A (suc n)} → ((vmap f v pre⟨ vmap f v' ▻⋯)) ~ (map {i} f (v pre⟨ v' ▻⋯))
map∼ {v = v} {v' = v'} = map∼Lemma v v'


-}






--
