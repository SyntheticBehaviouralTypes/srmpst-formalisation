-- Named recursion binders over de Bruijn indices: a binder at depth `δ`
-- hands its body a variable usable at any depth `m > δ`, where it stands
-- for index `m ∸ suc δ`.  The bound `suc δ ≤ m` is a `True`, solved by
-- `tt` whenever both depths are known numbers.

open import Data.Nat using (ℕ; suc; _≤?_)
open import Data.Fin using (Fin; fromℕ; inject≤; opposite)
open import Relation.Nullary.Decidable using (True; toWitness)

module Utils.Binder where

  bound : ∀ δ {m} → True (suc δ ≤? m) → Fin m
  bound δ p = opposite (inject≤ (fromℕ δ) (toWitness p))
