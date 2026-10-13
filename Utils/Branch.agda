-- Branching syntax, shared by protocols and processes:
--
--   ⟪ k₁ ↦ x₁
--   ∣ k₂ ↦ x₂
--   ⟫
--
-- `⟪_⟫` means whatever the `Closes` instance in scope says: a choice in
-- `Definitions.Graph.Algebra`, the branches of a receive in
-- `Definitions.Proc.Syntax`.

open import Data.Bool using (T)
open import Data.Fin using (Fin; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; [_]; _⁺++⁺_; toList)
open import Data.Maybe using (Maybe; just; nothing; is-just; _>>=_)
open import Data.Vec using (Vec; []; _∷_; tabulate)
open import Relation.Nullary using (yes; no)

module Utils.Branch where

  record Branch (K V : Set) : Set where
    constructor branch
    field
      key  : K
      body : V

  open Branch public

  Branches : Set → Set → Set
  Branches K V = List⁺ (Branch K V)

  infixr 4 _↦_
  infixr 3 _∣_

  _↦_ : ∀ {K V : Set} → K → V → Branches K V
  k ↦ x = [ branch k x ]

  _∣_ : ∀ {K V : Set} → Branches K V → Branches K V → Branches K V
  _∣_ = _⁺++⁺_

  record Closes (K V R : Set) : Set where
    field close : Branches K V → R

  open Closes {{...}} public

  ⟪_⟫ : ∀ {K V R : Set} {{_ : Closes K V R}} → Branches K V → R
  ⟪ bs ⟫ = close bs

  -- ── branches over labels, as a vector ──
  --
  -- The body of each label `0 … n-1`, in label order; `nothing` if a label
  -- has no branch.  Branches may come in any order; for a repeated label,
  -- the first one counts.
  private
    find : ∀ {n} {V : Set} → Fin n → List (Branch (Fin n) V) → Maybe V
    find i [] = nothing
    find i (branch k x ∷ bs) with i ≟ k
    ... | yes _ = just x
    ... | no  _ = find i bs

    all : ∀ {n} {V : Set} → Vec (Maybe V) n → Maybe (Vec V n)
    all [] = just []
    all (mx ∷ mxs) = mx >>= λ x → all mxs >>= λ xs → just (x ∷ xs)

  byLabel : ∀ {n} {V : Set} → Branches (Fin n) V → Maybe (Vec V n)
  byLabel bs = all (tabulate λ i → find i (toList bs))

  fromJust : ∀ {A : Set} (m : Maybe A) → T (is-just m) → A
  fromJust (just x) _ = x
