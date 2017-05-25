------------------------------------------------------------------------
-- Collection of most needed import from standard library
------------------------------------------------------------------------

module Library where

open import Data.Nat hiding (_⊔_) public
open import Data.Product hiding (map) public
open import Data.Vec using ([]; _∷_; Vec) public
open import Level renaming (zero to ℓ₀; suc to ℓ⁺) public
open import Function public
open import Size public

open import ContainerMonkeyPatched as Container renaming (map to fmap) public
