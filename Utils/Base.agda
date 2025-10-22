open import Level using (Level) renaming (suc to lsuc)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Bool using (T)
open import Data.Nat using (ℕ ; suc ; zero) renaming (_≟_ to _≟ℕ_)
open import Data.Fin using (Fin ; zero ; suc) renaming (_≟_ to _≟f_)
open import Data.Vec hiding (_++_) renaming (lookup to lu)
open import Relation.Nullary using (Dec; yes; no ; ¬_)
open import Relation.Unary using (Pred ; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

module Utils.Base where

data Every {a} {A : Set a} (P : Pred A a) : {I : ℕ} -> (Vec A I) ->  Set a where
  [∧] : Every P []
  _:∧:_ : ∀{M I} {V : Vec A I} -> P M -> Every P V -> Every P (M ∷ V)

[∧_∧] : ∀{a A M}  {P : Pred A a} -> P M -> Every P (M ∷ [])
[∧_∧] x = x :∧: [∧]

lookup-every : ∀{a}{A : Set a}{I V}{P : Pred A a} -> Every P V -> (i : Fin I) -> P (lu V i)
lookup-every (x :∧: every) zero = x
lookup-every (x :∧: every) (suc i) = lookup-every every i

data Exists {a}{A : Set a} (I : ℕ) (P : Pred A a) : (Vec A I) -> Set a  where
  Exists/i : {V : Vec A I}  -> (i : Fin I) -> P (lu V i) -> Exists I P V

DecidableExists : {a : Level} {A : Set a} (P : Pred A a) -> (I : ℕ) -> Set a
DecidableExists P I = Decidable (Exists I P)

nothing-exists-in-the-void : ∀{a}{A : Set a} {P : Pred A a} -> Exists zero P [] -> ⊥
nothing-exists-in-the-void (Exists/i () x)

exists-deeper : {a : Level }{A : Set a}{I : ℕ} {P : Pred A a} -> (xs : Vec A I) -> (x : A) -> Exists I P xs ->
  Exists (suc I) P (x ∷ xs)
exists-deeper xs x (Exists/i i prf) = Exists/i (suc i) prf

neither-here-nor-there : {a : Level }{A : Set a}{I : ℕ}
  {P : Pred A a} -> (xs : Vec A I) -> (x : A) -> (prf1 : ¬ P x) -> (prf2 : ¬ Exists I P xs) ->
  ¬ Exists (suc I) P (x ∷ xs)
neither-here-nor-there xs x prf1 prf2 (Exists/i zero prf3) = prf1 prf3 -- not here
neither-here-nor-there xs x prf1 prf2 (Exists/i (suc i) prf3) = prf2 (Exists/i i prf3) -- not there

exists-in-vec? : {a : Level }{A : Set a} (I : ℕ) (P : Pred A a) -> (f : (x : A) -> Dec (P x)) -> DecidableExists P I
exists-in-vec? .zero P f [] = no nothing-exists-in-the-void
exists-in-vec? (suc I) P f (x ∷ xs) with f x
...| yes eq = yes (Exists/i zero eq)
...| no eq with exists-in-vec? I P f xs
... | yes eq' = yes (exists-deeper xs x eq')
... | no eq' = no (neither-here-nor-there xs x eq eq')

-- map that tracks the index of the thing
imap : ∀ {n} {A B : Set} → (Fin n -> A → B) → Vec A n → Vec B n
imap f [] = []
imap f (x ∷ xs) = f zero x ∷ imap (λ i x → f (suc i) x) xs

imap-lookup-agree : ∀{A B : Set}{N} {f : Fin N -> A -> B} {V : Vec A N} -> (n : Fin N) ->  f n (lu V n) ≡ lu (imap f V) n
imap-lookup-agree {V = x ∷ V} zero = refl
imap-lookup-agree {V = x ∷ V} (suc n) = imap-lookup-agree {V = V} n

≟f-refl : ∀ {N} (i : Fin N) → (i ≟f i) ≡ yes refl
≟f-refl {_} i with i ≟f i
... | yes refl = refl
... | no  ¬ff  = ⊥-elim (¬ff refl)

≟n-refl : ∀ (n) → (n ≟ℕ n) ≡ yes refl
≟n-refl n with n ≟ℕ n
... | yes refl = refl
... | no  ¬ff  = ⊥-elim (¬ff refl)
