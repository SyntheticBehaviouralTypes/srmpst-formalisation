{-# OPTIONS --guardedness #-}

-- `A` sends a bool to `B`, `B` replies with a nat; once, and in a loop.
-- Partitions {A} {B} and {A,B}.

module Examples.PingPong where

open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Vec using ([]; _∷_)
open import Data.Bool using (true)
open import Data.Product using (proj₁; ∃-syntax; _×_)
open import Data.List using (length)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Sum using (_⊎_)
open import Relation.Nullary.Decidable using (from-yes)

open import Definitions.Expr using (s/bool; s/nat; val; v/bool; v/nat)
open import Check

open import Definitions.Graph.Algebra 2
open import Data.Fin.Subset using (⁅_⁆)
open import Definitions.Actions 2
open import Definitions.Proc 2 hiding (rec; _⇐_？·_)
open import Definitions.Proc.Syntax 2
open import Utils.Branch using (⟪_⟫; _↦_; _∣_)

A B : Fin 2
A = 0F
B = 1F

ping pong : Fin 1
ping = 0F
pong = 0F

-- {A,B}: one process.
Ρ/AB : Assignment 1
Ρ/AB = byOwner λ _ → 0F

module NonRecursive where
  -- A --bool--> B --nat--> A, end
  ping-pong : OpenGraph 0
  ping-pong =
    A ⟶ ⁅ B ⁆ # ping < s/bool > ∙
    B ⟶ ⁅ A ⁆ # pong < s/nat > ∙ end

  wbg : WBGraph {N = 2}
  wbg = buildG ping-pong

  s₀ = initial (proj₁ wbg)

  open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_; safety; module Global)

  -- {A} {B}
  module A∣B where
    Ρ = singletons
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = (A ⇒ ⁅ B ⁆ ! ping < val (v/bool true) >∙ (A ⇐ B ？· ⟪ pong ↦ ∅ ⟫))
      ∷ (B ⇐ A ？· ⟪ ping ↦ B ⇒ ⁅ A ⁆ ! pong < val (v/nat 0) >∙ ∅ ⟫)
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
  -- μ (A --bool--> B --nat--> loop)
  ping-pong : OpenGraph 0
  ping-pong =
    μ λ X → A ⟶ ⁅ B ⁆ # ping < s/bool > ∙ B ⟶ ⁅ A ⁆ # pong < s/nat > ∙ X

  wbg : WBGraph {N = 2}
  wbg = buildG ping-pong

  s₀ = initial (proj₁ wbg)

  open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_; safety; module Global)

  -- {A} {B}
  module A∣B where
    Ρ = singletons
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = (rec λ X → A ⇒ ⁅ B ⁆ ! ping < val (v/bool true) >∙
                    (A ⇐ B ？· ⟪ pong ↦ X ⟫))
      ∷ (rec λ X → B ⇐ A ？· ⟪ ping ↦ B ⇒ ⁅ A ⁆ ! pong < val (v/nat 0) >∙ X ⟫)
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
