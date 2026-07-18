{-# OPTIONS --guardedness #-}

-- The network-level entry points of the decidable type checker.
--
-- `WBNet n` is the *compositional* well-behavedness certificate for a net:
--
--   * `base`: the component graph's `wellBehaved?`, decided on its own
--     (small) presentation;
--   * `_∥_` : the two sub-certificates plus decided participant-
--     disjointness — diamond and every other axiom of the product follow
--     compositionally (`ParWB`), with *no* sweep of the product state
--     space;
--   * `_⨾_` : the two sub-certificates plus the decided seam-causality
--     conditions (`SeamComm`/`SeamBranch`, seam-local) plus the decided
--     `stepback/~` of the composite (`finiteStepback?` on the composite's
--     presentation — the one genuinely global condition, which provably
--     cannot be checked locally; see LTS/NetworkSeq.agda).
--
-- All evidence fields are Boolean (`T ⌊ … ⌋`) implicits: on concrete nets
-- they normalize to `⊤` and are auto-solved, so a certificate is written
-- with the same syntax as the net itself, e.g. `base ⨾ (base ∥ base)`.
--
-- `typecheckNet`/`typecheckSessionNet` run the graph checker over the
-- net's finite presentation with the *transported compositional* witness
-- (`net→pres ∘ netWB`) — `wellBehaved?` is never re-decided on a product.

open import Data.Bool using (T)
open import Data.Nat using (ℕ)
open import Data.Vec using ([])
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness)

open import Definitions.Behav using (WellBehaved)
import Definitions.TypeChecker.Core as Core
import Definitions.TypeChecker.Completeness as Comp

module Definitions.TypeChecker.Network (N : ℕ) where

  open Core.Processes N using (ProcessTyping; SessionTyping)
  open Comp N using (module GraphCompleteness)

  open import Definitions.Common N using (Part)
  open import Definitions.Proc N using (Proc; Session)
  open import LTS.Algebra N using (underlying; initial)
  open import LTS.Bisimulation N using (bisimulationCorrect)
  open import LTS.Decision N using (wellBehaved?; finiteStepback?; stepback/sound)
  open import LTS.Network N
  open import LTS.NetworkPresent N using (pres→net; net→pres)
  open import LTS.NetworkWB N using (disjoint?; module ParWB)
  open import LTS.NetworkSeq N using (seamComm?; seamBranch?; module SeqWB)

  data WBNet : Net → Set where
    base :
      ∀ {G}
      → {p : T ⌊ wellBehaved? (underlying (present (base G))) ⌋}
      → WBNet (base G)
    _∥_ :
      ∀ {n₁ n₂}
      → WBNet n₁ → WBNet n₂
      → {d : T ⌊ disjoint? n₁ n₂ ⌋}
      → WBNet (n₁ ∥ n₂)
    _⨾_ :
      ∀ {n₁ n₂}
      → WBNet n₁ → WBNet n₂
      → {sc : T ⌊ seamComm? n₁ n₂ ⌋}
      → {sb : T ⌊ seamBranch? n₁ n₂ ⌋}
      → {gs : T ⌊ finiteStepback? (underlying (present (n₁ ⨾ n₂))) ⌋}
      → WBNet (n₁ ⨾ n₂)

  netWB : ∀ {n} → WBNet n → WellBehaved (netTheory n)
  netWB {base G} (base {p = p}) =
    pres→net (base G) (toWitness p)
  netWB {n₁ ∥ n₂} ((w₁ ∥ w₂) {d = d}) =
    ParWB.parWB n₁ n₂ (netWB w₁) (netWB w₂) (toWitness d)
  netWB {n₁ ⨾ n₂} ((w₁ ⨾ w₂) {sc = sc} {sb = sb} {gs = gs}) =
    SeqWB.seqWB n₁ n₂ (netWB w₁) (netWB w₂)
      (toWitness sc) (toWitness sb)
      (stepback/sound
        (bisimulationCorrect (underlying (present (n₁ ⨾ n₂))))
        (toWitness gs))

  -- the compositional witness, on the presentation's side of the fence
  wb-net : ∀ {n} → WBNet n → WellBehaved _
  wb-net {n} w = net→pres n (netWB w)

  typecheckNet :
    ∀ {n} (w : WBNet n) (P : Part) (Pr : Proc 0 0)
    → Dec (ProcessTyping (underlying (present n)) (wb-net w) [] P Pr
             (initial (present n)))
  typecheckNet {n} w P Pr =
    GraphCompleteness.checkClosedD (underlying (present n)) (wb-net w)
      [] P Pr (initial (present n))

  typecheckSessionNet :
    ∀ {n} (w : WBNet n) (M : Session)
    → Dec (SessionTyping (underlying (present n)) (wb-net w) M
             (initial (present n)))
  typecheckSessionNet {n} w M =
    GraphCompleteness.checkSessionD (underlying (present n)) (wb-net w)
      M (initial (present n))
