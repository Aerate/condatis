
mutual
  record ClSF {i : Size} {ℓ₁ ℓ₂} {Cl : Set ℓ₂}  (C : Container ℓ₁) (cl : FStream C Cl) (A B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    inductive
    field
      inFCl : A → ⟦ C ⟧ (ClSF' {i} C cl A B)
  record ClSF' {i : Size} {ℓ₁ ℓ₂} {Cl : Set ℓ₂}  (C : Container ℓ₁) (cl : FStream C Cl) (A B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      head : B
      tail : {j : Size< i} → ClSF {j} C cl A B
open FStream public
open FStream' public

_>>>_ : ∀ {i : Size} {ℓ₁ ℓ₂} {a b c Cl : Set ℓ₂} {C : Container ℓ₁} {cl : FStream C Cl} → ClSF {i} C cl a b → ClSF {i} C cl b c → ClSF {i} C cl a c

runClock : ∀ {i : Size} {ℓ₁ ℓ₂} {Cl B : Set ℓ₂} {C : Container ℓ₁} → (cl : FStream C Cl) → ClSF {i} C cl A B → FStream {i} C A -> FStream {i} C B 
