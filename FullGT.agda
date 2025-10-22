{-# OPTIONS --guardedness #-}

open import Data.Nat

module FullGT(N : ℕ) where
  open import Definitions.GlobalTypesWPar(N)
  open import Safety(GT-Properties)
