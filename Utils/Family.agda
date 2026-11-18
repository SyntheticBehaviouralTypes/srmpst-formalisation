open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _,_)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- A finite family indexed by a set of labels `𝓛 ⊆ ℕ`: label `ℓ` is in `𝓛`
-- iff entry `ℓ` is `just`.  `xs ∋ ℓ ↦ x`: `ℓ ∈ 𝓛`, and its member is `x`.
module Utils.Family where

  infix 4 _∋_↦_

  data _∋_↦_ {A : Set} : ∀ {n} → Vec (Maybe A) n → ℕ → A → Set where
    here  : ∀ {n x} {xs : Vec (Maybe A) n} → (just x ∷ xs) ∋ zero ↦ x
    there : ∀ {n m ℓ y} {xs : Vec (Maybe A) n}
          → xs ∋ ℓ ↦ y → (m ∷ xs) ∋ suc ℓ ↦ y

  ∋-functional :
    ∀ {A : Set} {n} {xs : Vec (Maybe A) n} {ℓ x y}
    → xs ∋ ℓ ↦ x → xs ∋ ℓ ↦ y → x ≡ y
  ∋-functional here       here        = refl
  ∋-functional (there p) (there q) = ∋-functional p q

  ∋-unique :
    ∀ {A : Set} {n} {xs : Vec (Maybe A) n} {ℓ x}
    → (p q : xs ∋ ℓ ↦ x) → p ≡ q
  ∋-unique here      here      = refl
  ∋-unique (there p) (there q) = cong there (∋-unique p q)

  _∋?_ : ∀ {A : Set} {n} (xs : Vec (Maybe A) n) (ℓ : ℕ) → Dec (∃[ x ] xs ∋ ℓ ↦ x)
  []             ∋? ℓ     = no λ { (_ , ()) }
  (just x ∷ xs)  ∋? zero  = yes (x , here)
  (nothing ∷ xs) ∋? zero  = no λ { (_ , ()) }
  (m ∷ xs)       ∋? suc ℓ with xs ∋? ℓ
  ... | yes (y , p) = yes (y , there p)
  ... | no ¬p       = no λ { (y , there p) → ¬p (y , p) }
