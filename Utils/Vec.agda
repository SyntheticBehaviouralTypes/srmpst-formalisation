open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Properties using (+-monoˡ-<; +-monoʳ-<)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Vec using (Vec; _[_]≔_; lookup; _∷_; map; sum)

module Utils.Vec where

sum/map-update< :
  ∀ {A : Set} {n} {y : A}
  → (f : A → ℕ)
  → (xs : Vec A n)
  → (i : Fin n)
  → f y < f (lookup xs i)
  → sum (map f (xs [ i ]≔ y)) < sum (map f xs)
sum/map-update< f (_ ∷ xs) zero y<x =
  +-monoˡ-< (sum (map f xs)) y<x
sum/map-update< f (x ∷ xs) (suc i) y<x =
  +-monoʳ-< (f x) (sum/map-update< f xs i y<x)
