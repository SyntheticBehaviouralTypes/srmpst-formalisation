-- Set literals of any size: `⁅ A ⁆`, `⁅ A ； B ⁆`, `⁅ A ； B ； C ⁆`,
-- …  `；` is U+FF1B (the ASCII `;` is reserved).  Replaces stdlib's `⁅_⁆`:
-- hide that one where this is opened.  Unlike `⁅_,_⁆`, this does not
-- clash with `Data.Product`'s `_,_`.

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∪_)
import Data.Fin.Subset as Subset

module Utils.SetLit where

  -- What may sit between `⁅` and `⁆`: one element, or a `；`-chain.
  record Elems (n : ℕ) (A : Set) : Set where
    field elems : A → Subset n

  open Elems {{...}}

  instance
    elems/one : ∀ {n} → Elems n (Fin n)
    elems/one = record { elems = Subset.⁅_⁆ }

    elems/many : ∀ {n} → Elems n (Subset n)
    elems/many = record { elems = λ xs → xs }

  infixr 4 _；_

  _；_ : ∀ {n A} {{_ : Elems n A}} → Fin n → A → Subset n
  x ； xs = Subset.⁅ x ⁆ ∪ elems xs

  ⁅_⁆ : ∀ {n A} {{_ : Elems n A}} → A → Subset n
  ⁅ xs ⁆ = elems xs
