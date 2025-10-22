open import Data.Fin using (Fin)
open import Data.Nat using (ℕ ; suc)
open import Data.Product using (Σ-syntax)

module Definitions.Common (N : ℕ) where

  Part : Set
  Part = Fin N

  Label : Set
  Label = Σ[ I ∈ ℕ ] Fin (suc I)
