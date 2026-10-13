{-# OPTIONS --guardedness #-}

-- `A` sends a bool to `B`: once, in a loop, and in a loop unfolded once.
-- Partitions {A} {B} and {A,B}.

module Examples.SendRecv where

open import Definitions.Expr.Syntax
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Fin.Subset using (⁅_⁆)
open import Data.Vec using ([]; _∷_)
open import Data.Product using (proj₁; ∃-syntax; _×_)
open import Data.List using (length)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Sum using (_⊎_)
open import Relation.Nullary.Decidable using (from-yes)

open import Definitions.Expr using (s/bool; val; v/bool)
open import Check

open import Definitions.Graph.Algebra 2
open import Definitions.Actions 2
open import Definitions.Proc 2 hiding (rec; _⇐_？·_)
open import Definitions.Proc.Syntax 2
open import Utils.Branch using (⟪_⟫; _↦_; _∣_)

A B : Fin 2
A = 0F
B = 1F

-- The one message: a flag.
flag : Fin 1
flag = 0F

-- {A,B}: one process.
Ρ/AB : Assignment 1
Ρ/AB = byOwner λ _ → 0F

module NonRecursive where
  -- A --bool--> B, end
  sendrecv : OpenGraph 0
  sendrecv = A ⟶ ⁅ B ⁆ # flag < s/bool > ∙ end

  wbg : WBGraph {N = 2}
  wbg = buildG sendrecv

  s₀ = initial (proj₁ wbg)

  open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_; safety; module Global)

  -- {A} {B}
  module A∣B where
    Ρ = singletons
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = A ⇒ ⁅ B ⁆ ! flag < true >∙ ∅
      ∷ B ⇐ A ？· ⟪ flag ↦ ∅ ⟫
      ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = from-yes (typecheckSession wbg Ρ M)

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed

  -- {A,B}
  module AB where
    Ρ = Ρ/AB
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = ∅ ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = from-yes (typecheckSession wbg Ρ M)

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed

module Recursive where
  -- μ (A --bool--> loop)
  sendrecv : OpenGraph 0
  sendrecv = μ X · A ⟶ ⁅ B ⁆ # flag < s/bool > ∙ X

  wbg : WBGraph {N = 2}
  wbg = buildG sendrecv

  s₀ = initial (proj₁ wbg)

  open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_; safety; module Global)

  -- {A} {B}
  module A∣B where
    Ρ = singletons
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = rec X · A ⇒ ⁅ B ⁆ ! flag < true >∙ X
      ∷ rec X · B ⇐ A ？· ⟪ flag ↦ X ⟫
      ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = from-yes (typecheckSession wbg Ρ M)

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed

  -- {A,B}: an internal loop.
  module AB where
    Ρ = Ρ/AB
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = ∅ ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = from-yes (typecheckSession wbg Ρ M)

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed

module RecursiveUnfoldOnce where
  -- As `Recursive`, with `A`'s process unfolding the loop once.
  open Recursive using (sendrecv; wbg; s₀)

  open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_; safety; module Global)

  -- {A} {B}
  module A∣B where
    Ρ = singletons
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = A ⇒ ⁅ B ⁆ ! flag < true >∙
          rec X · A ⇒ ⁅ B ⁆ ! flag < true >∙ X
      ∷ rec X · B ⇐ A ？· ⟪ flag ↦ X ⟫
      ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = from-yes (typecheckSession wbg Ρ M)

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed
