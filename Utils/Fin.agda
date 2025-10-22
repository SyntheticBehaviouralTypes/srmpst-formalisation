--open import Level using (Level) renaming (suc to lsuc)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤ ; tt)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_ ; _,_)
open import Data.Bool using (T)
open import Data.Fin using (Fin ; zero ; suc ) renaming (_≟_ to _≟f_)
open import Data.Fin.Subset renaming (⊥ to ⊥f)
open import Data.Vec renaming (lookup to lu)
open import Relation.Nullary using (Dec; yes; no ; ¬_)
open import Relation.Nullary.Decidable using (False ; ⌊_⌋ ; isYes ; ¬? ; _⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

module Utils.Fin where

refl-is-equal : ∀{n}{x : Fin n} -> Data.Fin.compare x x ≡ Data.Fin.equal x
refl-is-equal {x = zero} = refl
refl-is-equal {x = suc x} rewrite refl-is-equal {x = x} = refl

_∈p_ : ∀{N} -> (P : Fin N) -> (RS : Fin N × Fin N) -> Set
P ∈p (R , S)  = (P ≡ R) ⊎ (P ≡ S)

_∈p?_ : ∀{N} -> (P : Fin N) -> (RS : Fin N × Fin N) -> Dec (P ∈p RS)
P ∈p? (R , S) = (P ≟f R) ⊎-dec (P ≟f S)

reflect-lookup : ∀{A : Set}{N}{V : Vec A N}{x : Fin N}{E} -> V [ x ]= E -> lu V x ≡ E
reflect-lookup here = refl
reflect-lookup (there prf) = reflect-lookup prf

lookup-get : ∀{A : Set}{N}{V : Vec A N}{x : Fin N}{E} -> lu V x ≡ E →  V [ x ]= E
lookup-get {V = x ∷ V} {x = zero} refl = here
lookup-get {V = x₁ ∷ V} {x = suc x} eq = there (lookup-get eq)

imnotme : ∀{N}{P : Fin N} -> False (P ≟f P) -> ⊥
imnotme {_}{P} pnp with P ≟f P
... | yes refl = pnp
... | no eq = eq refl


data SubFin : ∀ {X} → Subset X → Set where
  zero : ∀ {X}{k : Subset X} → SubFin (inside ∷ k)
  suc : ∀ {X io k} → SubFin {X = X} k → SubFin (io ∷ k)

to-fin : ∀ {X}{s : Subset X} → SubFin s → Fin X
to-fin zero = zero
to-fin (suc x) = suc (to-fin x)

to-fin/∈ : ∀ {X}{s : Subset X}(f : SubFin s) → to-fin f ∈ s
to-fin/∈ zero = here
to-fin/∈ (suc f) = there (to-fin/∈ f)
