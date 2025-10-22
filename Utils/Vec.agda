open import Data.Empty using (⊥-elim)
open import Data.Nat using (suc)
open import Data.Fin using (Fin ; zero ; suc ; punchOut ; punchIn)
open import Data.Vec using (Vec ; _[_]=_ ; lookup ; _∷_ ; insertAt)
-- open import Relation.Nullary using (Dec; yes; no ; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; _≢_)

module Utils.Vec where

-- Properties of vectors when looking up

cong-suc-fin : ∀ {n} -> (i j : Fin (suc n)) -> (i≢j : suc i ≢ suc j) → i ≢ j
cong-suc-fin i .i prf refl = ⊥-elim (prf refl)

lookup-not-insertAt : ∀{n}{A : Set}{V : Vec A n}{a : A} ->
  (i j : Fin (suc n)) -> (i≢j : i ≢ j) -> lookup (insertAt V i a) j ≡ lookup V (punchOut i≢j)
lookup-not-insertAt zero zero i≢j = ⊥-elim (i≢j refl)
lookup-not-insertAt zero (suc j) i≢j = refl
lookup-not-insertAt {V = _ ∷ V} (suc i) zero i≢j = refl
lookup-not-insertAt {V = _ ∷ V} (suc i) (suc j) i≢j =
  lookup-not-insertAt {V = V} i j (cong-suc-fin i j i≢j )
