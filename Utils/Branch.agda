-- Branching syntax, shared by protocols and processes:
--
--   ⟪ k₁ ↦ x₁
--   ∣ k₂ ↦ x₂
--   ⟫
--
-- `⟪_⟫` means whatever the `Closes` instance in scope says: a choice in
-- `Definitions.Graph.Algebra`, the branches of a receive in
-- `Definitions.Proc.Syntax`.

open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; [_]; _⁺++⁺_; toList)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≟_)
open import Data.Vec using (Vec; tabulate)
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

  -- ── branches over labels, as a family ──
  --
  -- Entry `ℓ` is the body of label `ℓ`, `nothing` if it has none
  -- (`Utils.Family`); the vector runs up to the largest label.  Branches
  -- may come in any order; for a repeated label, the first one counts.
  private
    find : ∀ {V : Set} → ℕ → List (Branch ℕ V) → Maybe V
    find ℓ [] = nothing
    find ℓ (branch k x ∷ bs) with ℓ ≟ k
    ... | yes _ = just x
    ... | no  _ = find ℓ bs

    width : ∀ {V : Set} → List (Branch ℕ V) → ℕ
    width []                = zero
    width (branch k _ ∷ bs) = suc k ⊔ width bs

  family : ∀ {V : Set} (bs : Branches ℕ V) → Vec (Maybe V) (width (toList bs))
  family bs = tabulate λ i → find (toℕ i) (toList bs)
