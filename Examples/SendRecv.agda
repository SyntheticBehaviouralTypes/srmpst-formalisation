{-# OPTIONS --guardedness #-}

-- `A` sends a bool to `B`: once, in a loop, and in a loop unfolded once.
-- Partitions {A} {B} and {A,B}.

module Examples.SendRecv where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Subset using (⁅_⁆)
open import Data.Vec using ([]; _∷_)
open import Data.Bool using (true)
open import Data.Product using (proj₁; ∃-syntax; _×_)
open import Data.List using (length)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Sum using (_⊎_)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr using (s/bool; val; v/bool)
open import Check

open import Definitions.Graph.Algebra 2
open import Definitions.Actions 2 renaming (_<_> to mkChoice)
open import Definitions.Proc 2

A B : Fin 2
A = zero
B = suc zero

-- Pins `I = 0` for a non-branching send.
here : Fin 1
here = zero

-- {A,B}: one process.
Ρ/AB : Assignment 1
Ρ/AB = byOwner λ _ → zero

module NonRecursive where
  -- A --bool--> B, end
  sendrecv : OpenGraph 0
  sendrecv = (A ⟶ ⁅ B ⁆ # mkChoice here s/bool) ∙ end

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
    M = (A ⇒ ⁅ B ⁆ ! here < val (v/bool true) >∙ ∅) ∷ (B ⇐ A ？· (∅ ∷ [])) ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

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
    M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed

module Recursive where
  -- μ (A --bool--> loop)
  sendrecv : OpenGraph 0
  sendrecv = μ ((A ⟶ ⁅ B ⁆ # mkChoice here s/bool) ∙ var zero)

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
    M = rec (A ⇒ ⁅ B ⁆ ! here < val (v/bool true) >∙ v zero)
      ∷ rec (B ⇐ A ？· (v zero ∷ []))
      ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

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
    M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

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
    M = (A ⇒ ⁅ B ⁆ ! here < val (v/bool true) >∙
           (rec (A ⇒ ⁅ B ⁆ ! here < val (v/bool true) >∙ v zero)))
      ∷ rec (B ⇐ A ？· (v zero ∷ []))
      ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed
