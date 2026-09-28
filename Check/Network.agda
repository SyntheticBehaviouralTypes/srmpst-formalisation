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

open import Definitions.Behav using (WellBehaved; Synchronous)
import Check.Core as Core
import Check.TypeCheck

module Check.Network (N : ℕ) where

  open Core.Processes N using (ProcessTyping; SessionTyping)
  open Check.TypeCheck N using (module TypeCheck)

  open import Definitions.Common N using (Part)
  open import Definitions.Proc N using (Proc; Session)
  open import Definitions.Graph.Algebra N using (underlying; initial)
  open import Definitions.Graph.Bisimulation N using (bisimulationCorrect)
  open import Definitions.Graph.Decision N
    using (wellBehaved?; synchronous?; finiteStepback?; stepback/sound)
  open import Definitions.Graph.Network N
  open import Definitions.Graph.NetworkPresent N
    using (pres→net; net→pres; pres→netSync; net→presSync)
  open import Definitions.Graph.NetworkWB N
    using (disjoint?; module ParWB; module ParSync)
  open import Definitions.Graph.NetworkSeq N
    using (seamComm?; seamBranch?; module SeqWB; module SeqSync)

  data WBNet : Net → Set where
    base :
      ∀ {G}
      → {p : T ⌊ wellBehaved? (underlying (present (base G))) ⌋}
      → {q : T ⌊ synchronous? (underlying (present (base G))) ⌋}
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
  netWB {n₁ ⨾ n₂} ((w₁ ⨾ w₂) {sb = sb} {gs = gs}) =
    SeqWB.seqWB n₁ n₂ (netWB w₁) (netWB w₂)
      (toWitness sb)
      (stepback/sound
        (bisimulationCorrect (underlying (present (n₁ ⨾ n₂))))
        (toWitness gs))

  netSync : ∀ {n} → WBNet n → Synchronous (netTheory n)
  netSync {base G} (base {q = q}) =
    pres→netSync (base G) (toWitness q)
  netSync {n₁ ∥ n₂} (w₁ ∥ w₂) =
    ParSync.parSync n₁ n₂ (netSync w₁) (netSync w₂)
  netSync {n₁ ⨾ n₂} ((w₁ ⨾ w₂) {sc = sc}) =
    SeqSync.seqSync n₁ n₂ (netSync w₁) (netSync w₂) (toWitness sc)

  -- the compositional witnesses, on the presentation's side of the fence
  wb-net : ∀ {n} → WBNet n → WellBehaved _
  wb-net {n} w = net→pres n (netWB w)

  sync-net : ∀ {n} → WBNet n → Synchronous _
  sync-net {n} w = net→presSync n (netSync w)

  -- Over `Check.TypeCheck`.  Note the checker runs on
  -- the net's finite *presentation* with the transported compositional
  -- witness — `wellBehaved?` is never re-decided on a product.
  typecheckNet :
    ∀ {n} (w : WBNet n) (P : Part) (Pr : Proc 0 0)
    → Dec (ProcessTyping (underlying (present n)) (wb-net w) [] P Pr
             (initial (present n)))
  typecheckNet {n} w P Pr =
    TypeCheck.tc? (underlying (present n)) (wb-net w) (sync-net w) [] [] P Pr
      (initial (present n))

  typecheckSessionNet :
    ∀ {n} (w : WBNet n) (M : Session)
    → Dec (SessionTyping (underlying (present n)) (wb-net w) M
             (initial (present n)))
  typecheckSessionNet {n} w M =
    TypeCheck.tcSession? (underlying (present n)) (wb-net w) (sync-net w) M
      (initial (present n))
