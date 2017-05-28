------------------------------------------------------------------------
-- Collection of most needed import from standard library
------------------------------------------------------------------------

module Library where


open import Data.Empty public
open import Data.Unit hiding (_≟_; _≤_; _≤?_; decSetoid; decTotalOrder; setoid) public
open import Data.Sum public hiding (map)
open import Data.Bool hiding (_≟_) public
open import Data.Nat hiding (_⊔_) public
open import Data.Product hiding (map) public
open import Data.Vec using ([]; _∷_; Vec) public
open import Level renaming (zero to ℓ₀; suc to ℓ⁺) public
open import Function public
open import Size public
open import Relation.Binary.PropositionalEquality hiding (decSetoid; preorder; setoid) public

open import ContainerMonkeyPatched as Container renaming (map to fmap) public
