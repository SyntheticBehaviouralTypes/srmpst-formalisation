open import Data.Fin using (Fin; zero; suc)
open import Data.Vec renaming (lookup to lu)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Utils.Fin where

reflect-lookup : ∀{A : Set}{N}{V : Vec A N}{x : Fin N}{E} -> V [ x ]= E -> lu V x ≡ E
reflect-lookup here = refl
reflect-lookup (there prf) = reflect-lookup prf

lookup-get : ∀{A : Set}{N}{V : Vec A N}{x : Fin N}{E} -> lu V x ≡ E →  V [ x ]= E
lookup-get {V = x ∷ V} {x = zero} refl = here
lookup-get {V = x₁ ∷ V} {x = suc x} eq = there (lookup-get eq)
