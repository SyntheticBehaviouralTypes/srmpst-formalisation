{-# OPTIONS --guardedness #-}

-- Type checking over rooted graphs, each process against its block's
-- local view.  `WBGraph`'s evidence is Boolean, so `buildG g` needs no
-- proof on a concrete graph.

open import Data.Bool using (T)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Fin.Properties using (all?)
open import Data.Vec using () renaming (lookup to lu)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness)

open import Definitions.Behav using (WellBehaved; Synchronous)
open import Definitions.Typing.Declarative using (module Sessions)
import Check.View

module Check.Graph (N : ℕ) where

  open Check.View N using (typecheckView)

  open import Definitions.Common N using (PartSet)
  open import Definitions.Proc N using (Proc; Assignment; module Over)
  open import Definitions.Graph.Algebra N
    using (RootedGraph; OpenGraph; compile; underlying; initial)
  open import Definitions.Graph.Core N using (graphTheory)
  open import Definitions.Graph.Decision N using (wellBehaved?; synchronous?)
  -- A graph, certified well-behaved and synchronous.
  WBGraph : Set
  WBGraph =
    Σ[ R ∈ RootedGraph ]
      T ⌊ wellBehaved? (underlying R) ⌋ × T ⌊ synchronous? (underlying R) ⌋

  wb-of : (WR : WBGraph) → WellBehaved (graphTheory (underlying (proj₁ WR)))
  wb-of WR = toWitness (proj₁ (proj₂ WR))

  sync-of : (WR : WBGraph) → Synchronous (graphTheory (underlying (proj₁ WR)))
  sync-of WR = toWitness (proj₂ (proj₂ WR))

  buildG :
    (OG : OpenGraph 0)
    → {p : T ⌊ wellBehaved? (underlying (compile OG)) ⌋}
    → {q : T ⌊ synchronous? (underlying (compile OG)) ⌋}
    → WBGraph
  buildG OG {p} {q} = compile OG , p , q

  module _ (WR : WBGraph) where

    open Sessions (graphTheory (underlying (proj₁ WR))) using (⊢ᵛ[_]_∶_; ⊢s[_]_∶_)

    -- The process of role set `Ps`, against `Ps`'s local view.
    typecheck : (Ps : PartSet) (Pr : Proc 0 0) → Dec (⊢ᵛ[ Ps ] Pr ∶ initial (proj₁ WR))
    typecheck Ps Pr =
      typecheckView (underlying (proj₁ WR)) (sync-of WR) Ps Pr (initial (proj₁ WR))

    -- Each process of the session, at its block.
    typecheckSession :
      ∀ {K} (Ρ : Assignment K) (M : Over.Session Ρ)
      → Dec (⊢s[ Ρ ] M ∶ initial (proj₁ WR))
    typecheckSession Ρ M = all? λ j → typecheck (lu (Assignment.roles Ρ) j) (lu M j)
