{-# OPTIONS --guardedness #-}

-- Bool-vector fixpoints: iteration to a stable round, and the two
-- `Subset` facts the checker needs that stdlib lacks: a fast membership
-- decision and strict inclusion from `⊆` and `≢`.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.GeneralisedArithmetic using (iterate)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Data.Bool.Properties using () renaming (_≟_ to _≟Bool_)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∈_; _⊆_; _⊂_; inside)
open import Data.Fin.Subset.Properties using (⊆-antisym)
import Data.Fin.Properties as FinP
open import Data.Vec using (lookup)
open import Data.Vec.Properties using (lookup⇒[]=; []=⇒lookup)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _→?_)

module Utils.Bits where

iterate-suc :
  ∀ {A : Set} (f : A → A) x k → iterate f x (suc k) ≡ f (iterate f x k)
iterate-suc f x zero    = refl
iterate-suc f x (suc k) = iterate-suc f (f x) k

iterate-add :
  ∀ {A : Set} (f : A → A) x a b
  → iterate f x (a + b) ≡ iterate f (iterate f x a) b
iterate-add f x zero    b = refl
iterate-add f x (suc a) b = iterate-add f (f x) a b

iterate/stable :
  ∀ {A : Set} (f : A → A) x → f x ≡ x → ∀ k → iterate f x k ≡ x
iterate/stable f x eq zero    = refl
iterate/stable f x eq (suc k) =
  trans (cong (λ y → iterate f y k) eq) (iterate/stable f x eq k)

-- `iterate`, stopping at a stable round.  The equality test forces each
-- round, which a lazy `iterate` chain does not.  `iterateFix/iterate`
-- relates them.
iterateFix :
  ∀ {A : Set}
  → ((x y : A) → Dec (x ≡ y))
  → ℕ → (A → A) → A → A
iterateFix eq? zero f x = x
iterateFix eq? (suc fuel) f x with f x
... | fx with eq? fx x
...   | yes _ = x
...   | no  _ = iterateFix eq? fuel f fx

iterateFix/iterate :
  ∀ {A : Set}
    (eq? : (x y : A) → Dec (x ≡ y))
    fuel (f : A → A) x
  → iterateFix eq? fuel f x ≡ iterate f x fuel
iterateFix/iterate eq? zero f x = refl
iterateFix/iterate eq? (suc fuel) f x with f x in fxeq
... | fx with eq? fx x
...   | yes eq =
  sym (trans (cong (λ y → iterate f y fuel) eq)
             (iterate/stable f x (trans fxeq eq) fuel))
...   | no _ = iterateFix/iterate eq? fuel f fx

-- Stdlib's `_∈?_` wraps every recursion step in a `Dec.map′`; this reads
-- the bit once.  It is on the checker's innermost loops (`expand`, the
-- reachability rows, the `Wait` visited set), where stdlib's costs IndepW
-- 35%.
infix 4 _∈?_

_∈?_ : ∀ {n} (x : Fin n) (p : Subset n) → Dec (x ∈ p)
x ∈? p = map′ (lookup⇒[]= x p) []=⇒lookup (lookup p x ≟Bool inside)

-- A strict inclusion, from an inclusion that is not an equality.
⊆∧≢⇒⊂ : ∀ {n} {p q : Subset n} → p ⊆ q → p ≢ q → p ⊂ q
⊆∧≢⇒⊂ {n} {p} {q} p⊆q p≢q
  with FinP.¬∀⇒∃¬ n _ (λ x → (x ∈? q) →? (x ∈? p))
         (λ q⊆p → p≢q (⊆-antisym p⊆q (λ {x} → q⊆p x)))
... | x , ¬q⊆p with x ∈? q
...   | yes x∈q = p⊆q , x , x∈q , λ x∈p → ¬q⊆p λ _ → x∈p
...   | no  x∉q = ⊥-elim (¬q⊆p λ x∈q → ⊥-elim (x∉q x∈q))
