------------------------------------------------------------------------
-- Modalities that quantify over some paths (E)
------------------------------------------------------------------------

module CTL.E where

open import FStream.Core
open import Library

-- 'Eventually Certain' : s ⊧ φ ⇔ ∃ p ∀ s ∈ p ⊧ φ
{-# NO_POSITIVITY_CHECK #-}
record EG' {i : Size} {ℓ₁ ℓ₂} {C : Container ℓ₁}
  (props : FStream' {i} C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    nowE' : head props
    laterE' : {j : Size< i} → E (fmap EG' (inF (tail props)))
open EG' public

EG : ∀ {i : Size} {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream {i} C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
EG props = EPred EG' (inF props)


-- TODO Possibly split the different modalities into separate files still

-- TODO Rename all cas to props everywhere
-- Eventually Possible : s ⊧ φ ⇔ ∃ p ∃ s ∈ p ⊧ φ
data EF' {ℓ₁ ℓ₂} {i : Size} {C : Container ℓ₁}
     (cas : FStream' {i} C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyE : head cas → EF' cas
  notYetE :  {j : Size< i} → E (fmap EF' (inF (tail cas))) → EF' cas
open EF'

--TODO Rewrite as function like EG
data EF {ℓ₁ ℓ₂} {C : Container ℓ₁}
     (cas : FStream C (Set ℓ₂)) : Set (ℓ₁ ⊔ ℓ₂) where
  alreadyE : E (fmap head (inF cas)) → EF cas
  notYetE : EPred EF (fmap (λ x → tail x) (inF cas)) → EF cas
open EF


-- Eventually (in) Next : p ⊧ φ ⇔ ∃ p[1] ⊧ φ
EN' : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
EN' s = EPred head (inF (tail s))

EN : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream C (Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
EN s = EPred EN' (inF s)

{-# NON_TERMINATING #-} -- TODO EN' won't work with sizes
EN'ₛ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream' C (Set ℓ₂) → FStream' C (Set (ℓ₁ ⊔ ℓ₂))
head (EN'ₛ s) = EN' s
inF (tail (EN'ₛ s)) = fmap EN'ₛ (inF (tail s))

ENₛ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} → FStream C (Set ℓ₂) → FStream C (Set (ℓ₁ ⊔ ℓ₂))
inF (ENₛ s) = fmap EN'ₛ (inF s)



module ProofE where

open import FStream.FVec
open import FStream.Bisimulation-alt

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
            {props : FVec C (Set ℓ₂) m} →
            {props' : FVec C (Set ℓ₂) (suc n)} →
            proofEG props →
            proofEG props' →
            EG {i} (props pre⟨ props' ▻⋯)
proj₁ ([]EG pre⟨ ConsEG (pos , _) ▻EG) = pos
nowE' (proj₂ ([]EG pre⟨ ConsEG (_ , proof , _) ▻EG)) = proof
laterE' (proj₂ ([]EG pre⟨ ConsEG (pos , proof , proofs) ▻EG)) =
  proofs pre⟨ ConsEG (pos , proof , proofs) ▻EG
proj₁ (ConsEG (pos , _) pre⟨ _ ▻EG) = pos
nowE'   (proj₂ (ConsEG (pos , proof , proofs) pre⟨ _ ▻EG)) = proof
laterE' (proj₂ (ConsEG (_   , _     , proofs) pre⟨ v ▻EG)) = proofs pre⟨ v ▻EG

-- TODO It's worth a thought whether we want to roll our own Sigma types
-- in order to have more meaningful projector names than projᵢ



⟨_▻EG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁} {n}
        {props : FVec C (Set ℓ₂) (suc n)} →
        proofEG props → EG {i} (FNil pre⟨ props ▻⋯)
⟨_▻EG = []EG pre⟨_▻EG

_⟩EG : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)} →
       E prop → proofEG (FCons (fmap (_, FNil) prop))
(pos , proof) ⟩EG = ConsEG (pos , (proof , []EG))

_⟩EGᵢ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)} →
        {pos : Position C (proj₁ prop)} →
        proj₂ prop pos →
        proofEG (FCons (fmap (_, FNil) prop))
_⟩EGᵢ {pos = pos} proof = ConsEG (pos , (proof , []EG))


-- TODO
_▻EG_ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁}
        {prop : ⟦ C ⟧ (Set ℓ₂)} {n} {props : FVec C (Set ℓ₂) n} →
        E prop →
        proofEG props →
        proofEG (FCons (fmap (_, props) prop))
(pos , proof) ▻EG proofs = ConsEG (pos , (proof , proofs))


_▻EGᵢ_ : ∀ {ℓ₁ ℓ₂} {C : Container ℓ₁} {prop : ⟦ C ⟧ (Set ℓ₂)} {n}
         {props : FVec C (Set ℓ₂) n} →
         {pos : Position C (proj₁ prop)} →
         proj₂ prop pos →
         proofEG props →
         proofEG (FCons (fmap (_, props) prop))
_▻EGᵢ_ {pos = pos} proof proofs = ConsEG (pos , (proof , proofs))


mapEGᵢ : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂}
         {f : A → Set ℓ₃} {m n} →
         (v : FVec C A m) →
         (v' : FVec C A (suc n)) →
         EG {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) →
         EG {i} (map f (v pre⟨ v' ▻⋯))
proj₁ (mapEGᵢ FNil (FCons x) (pos , proof)) = pos
nowE' (proj₂ (mapEGᵢ FNil (FCons x) (pos , proofs))) = nowE' proofs
laterE' (proj₂ (mapEGᵢ {f = f} FNil (FCons (shape , vals)) (pos , proof)))
  with vals pos
... | a , v = mapEGᵢ v (FCons (shape , vals)) (laterE' proof)
proj₁ (mapEGᵢ (FCons (proj₃ , proj₄)) v' (pos , proofs)) = pos
nowE' (proj₂ (mapEGᵢ (FCons x) v' (pos , proofs))) = nowE' proofs
laterE' (proj₂ (mapEGᵢ (FCons (shape , vals)) v' (pos , proofs)))
  with vals pos
... | a , v = mapEGᵢ v v' (laterE' proofs)


mapEG : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂}
        {f : A → Set ℓ₃} {m n} →
        {v : FVec C A m} →
        {v' : FVec C A (suc n)} →
        EG {i} ((vmap f v pre⟨ vmap f v' ▻⋯)) →
        EG {i} (map f (v pre⟨ v' ▻⋯))
mapEG {v = v} {v' = v'} proofs = mapEGᵢ v v' proofs


mutual
  -- TODO Rename to ∼EG?
  bisimEG : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁}
            {s₁ s₂ : FStream C (Set ℓ₂)} →
            s₁ ~ s₂ → EG {i} s₁ → EG {i} s₂
  proj₁ (bisimEG {C = C} bs (pos , proofs)) =
    subst (Position C) (sameInitShapes bs) pos
  proj₂ (bisimEG bs (pos , proofs)) = bisimEG' (bisim bs pos) proofs

  bisimEG' : ∀ {i} {ℓ₁ ℓ₂} {C : Container ℓ₁}
             {s₁ s₂ : FStream' C (Set ℓ₂)} →
             s₁ ~' s₂ → EG' {i} s₁ → EG' {i} s₂
  -- TODO This thing must already exist in stdlib somewhere
  nowE' (bisimEG' bs proof) = subst (λ x → x) (hd∼ bs) (nowE' proof)
  laterE' (bisimEG' {C = C} bs proof) = bisimEG (tl∼ bs) (laterE' proof)


-- TODO Rather write as mutual with a map∼'
map∼Lemma : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁}
            {A : Set ℓ₂} {B : Set ℓ₃} {f : A → B} {m n} →
            (v : FVec C A m) →
            (v' : FVec C A (suc n)) →
            ((vmap f v pre⟨ vmap f v' ▻⋯)) ~ (map {i} f (v pre⟨ v' ▻⋯))
sameInitShapes (map∼Lemma FNil (FCons x)) = refl
sameInitShapes (map∼Lemma (FCons x) v') = refl
hd∼ (bisim (map∼Lemma FNil (FCons x)) pos) = refl
tl∼ (bisim (map∼Lemma FNil (FCons (shape , av))) pos) {j}
    with (proj₂ (av pos))
... | p = map∼Lemma {j} p (FCons (shape , av))
hd∼ (bisim (map∼Lemma (FCons x) (FCons x₁)) pos) = refl
tl∼ (bisim (map∼Lemma (FCons (shape , av)) v') pos) {j}
    with (proj₂ (av pos))
... | p = map∼Lemma {j} p v'

-- TODO Eradicate the previous lemma with with on implicit arguments
map∼ : ∀ {i} {ℓ₁ ℓ₂ ℓ₃} {C : Container ℓ₁} {A : Set ℓ₂}
       {B : Set ℓ₃} {f : A → B} {m n} →
       {v : FVec C A m} →
       {v' : FVec C A (suc n)} →
       ((vmap f v pre⟨ vmap f v' ▻⋯)) ~ (map {i} f (v pre⟨ v' ▻⋯))
map∼ {v = v} {v' = v'} = map∼Lemma v v'
