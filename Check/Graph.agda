{-# OPTIONS --guardedness #-}

-- The rooted-graph entry points of the decidable type checker, restored
-- (TODO.md Step 6) over `Check.Alg` with the same signatures the deleted
-- `Definitions/TypeChecker/Completeness.agda` had, so callers under
-- `Examples/` and `Tests/` only have to change which module they import.
--
-- `WBGraph` bundles a rooted graph with the *Boolean* evidence that it is
-- well behaved, so on a concrete graph `wellBehaved? …` normalises to `⊤`
-- and `buildG g` is written with no proof argument at all.

open import Data.Bool using (T)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Vec using ([])
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness)

open import Definitions.Behav using (WellBehaved)
import Check.Core as Core
import Check.Alg

module Check.Graph (N : ℕ) where

  open Core.Processes N using (ProcessTyping; SessionTyping)

  open import Definitions.Common N using (Part)
  open import Definitions.Proc N using (Proc; Session)
  open import Definitions.Graph.Algebra N
    using (RootedGraph; OpenGraph; compile; underlying; initial)
  open import Definitions.Graph.Core N using (graphTheory)
  open import Definitions.Graph.Decision N using (wellBehaved?)
  open Check.Alg N using (module AlgCheck)

  WBGraph : Set
  WBGraph = Σ[ R ∈ RootedGraph ] T ⌊ wellBehaved? (underlying R) ⌋

  wb-of : (WR : WBGraph) → WellBehaved (graphTheory (underlying (proj₁ WR)))
  wb-of WR = toWitness (proj₂ WR)

  buildG :
    (OG : OpenGraph 0) → {p : T ⌊ wellBehaved? (underlying (compile OG)) ⌋}
    → WBGraph
  buildG OG {p} = compile OG , p

  typecheck :
    (WR : WBGraph) (P : Part) (Pr : Proc 0 0)
    → Dec (ProcessTyping (underlying (proj₁ WR)) (wb-of WR) [] P Pr
             (initial (proj₁ WR)))
  typecheck WR P Pr =
    AlgCheck.tc? (underlying (proj₁ WR)) (wb-of WR) [] [] P Pr
      (initial (proj₁ WR))

  typecheckSession :
    (WR : WBGraph) (M : Session)
    → Dec (SessionTyping (underlying (proj₁ WR)) (wb-of WR) M
             (initial (proj₁ WR)))
  typecheckSession WR M =
    AlgCheck.tcSession? (underlying (proj₁ WR)) (wb-of WR) M
      (initial (proj₁ WR))
