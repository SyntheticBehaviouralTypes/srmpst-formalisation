{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Induction using (<-wellFounded)
import Data.Nat.Properties as Nat

open import Data.Fin using (Fin; zero; suc)
import Data.Fin.Properties as FinP

open import Data.Vec using (Vec; []; _∷_; lookup; tabulate; replicate)
import Data.Vec.Properties as VecP

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.Any.Properties as AnyProp

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

open import Data.Bool using (Bool; true; false; _∨_; _∧_; T)
import Data.Bool.Properties as BoolP

open import Induction.WellFounded using (Acc; acc)

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable
  using (⌊_⌋; T?; map′; _×-dec_; _→-dec_; toWitness; ¬?)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)

open import Definitions.Behav using (WellBehaved)
open import Definitions.Expr
  using (Sort; s/bool; s/nat; s/unit; Exp; Value; v/bool; v/nat; v/unit
        ; ⊢v_∶_; tv/bool; tv/nat; tv/unit; sort/value
        ; _⊢e_∶_; te/val; te/minus1; te/is-zero; te/var; ⊢e-unique
        ; val; minus1; is-zero; var
        ; s/nat≢s/bool; s/nat≢s/unit)

import Definitions.Typing as Typing

module Check.Alg (N : ℕ) where

  open import Definitions.Graph.Core N hiding (_-<_>->_; step?)
  open import Definitions.Graph.Bisimulation N
    using (Bisimilar; bisim?; bisimulationCorrect; sound; complete)
  open import Definitions.Graph.Action N using (_≟Action_; _≟Sort_)

  module AlgCheck
    (G : Graph)
    (wb : WellBehaved (graphTheory G))
    where

    open Typing.MPST wb
    open import Definitions.Typing.Alg wb

    private
      variable
        γ δ : ℕ

    Bits : Set
    Bits = Vec Bool (size G)

    ⟦_⟧ : Bits → Pred
    ⟦ bits ⟧ t = T (lookup bits t)

    alg? :
      ∀ {γ δ}
        (Γ : Vec Sort γ)
        (Δ : Vec Behav δ)
        (P : Part)
        (Pr : Proc γ δ)
        (𝒮 : Bits)
      → Dec (Γ & Δ ⊢a P ◂ Pr ∶ ⟦ 𝒮 ⟧)
    alg? = ?
