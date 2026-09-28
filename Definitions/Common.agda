open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset)
open import Data.Nat using (ℕ ; suc)
open import Data.Product using (Σ-syntax)

module Definitions.Common (N : ℕ) where

  Part : Set
  Part = Fin N

  -- A set of participants (e.g. the receivers of a multicast).
  PartSet : Set
  PartSet = Subset N

  Label : Set
  Label = Σ[ I ∈ ℕ ] Fin (suc I)
