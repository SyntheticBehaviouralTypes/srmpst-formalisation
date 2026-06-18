{-# OPTIONS --guardedness #-}

-- Type checking over nets.  `WBNet n` certifies a net compositionally:
-- `base` decides its graph, `∥` adds `disjoint?`, `⨾` adds the seam
-- conditions.  Its evidence fields are `T ⌊ … ⌋` implicits, solved on
-- concrete nets.  `typecheckNet` runs the graph checker on `present n`.

open import Data.Bool using (T)
open import Data.Nat using (ℕ)
open import Data.Fin.Properties using (all?)
open import Data.Vec using () renaming (lookup to lu)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness)

open import Definitions.Behav using (WellBehaved; Synchronous)
open import Definitions.Typing.Declarative using (module Sessions)
import Check.View

module Check.Network (N : ℕ) where

  open Check.View N using (typecheckView)
  open import Definitions.Graph.Core N using (graphTheory)

  open import Definitions.Common N using (PartSet)
  open import Definitions.Proc N using (Proc; Assignment; module Over)
  open import Definitions.Graph.Algebra N using (underlying; initial)
  open import Definitions.Graph.Decision N using (wellBehaved?; synchronous?)
  open import Definitions.Graph.Network N
  open import Definitions.Graph.NetworkPresent N
    using (pres→net; net→pres; pres→netSync; net→presSync)
  open import Definitions.Graph.NetworkWB N
    using (disjoint?; module ParWB; module ParSync)
  open import Definitions.Graph.NetworkSeq N
    using ( Moves; moves?; moves/par; moves/seq
          ; seamComm?; seamBranch?; module SeqWB; module SeqSync )

  data WBNet : Net → Set where
    base :
      ∀ {G}
      → {p : T ⌊ wellBehaved? (underlying (present (base G))) ⌋}
      → {q : T ⌊ synchronous? (underlying (present (base G))) ⌋}
      → {m : T ⌊ moves? G ⌋}
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
      → WBNet (n₁ ⨾ n₂)

  netMoves : ∀ {n} → WBNet n → Moves n
  netMoves {base G} (base {m = m}) = toWitness m
  netMoves (w₁ ∥ w₂) = moves/par (netMoves w₁) (netMoves w₂)
  netMoves (w₁ ⨾ w₂) = moves/seq (netMoves w₁) (netMoves w₂)

  netWB : ∀ {n} → WBNet n → WellBehaved (netTheory n)
  netWB {base G} (base {p = p}) =
    pres→net (base G) (toWitness p)
  netWB {n₁ ∥ n₂} ((w₁ ∥ w₂) {d = d}) =
    ParWB.parWB n₁ n₂ (netWB w₁) (netWB w₂) (toWitness d)
  netWB {n₁ ⨾ n₂} ((w₁ ⨾ w₂) {sb = sb}) =
    SeqWB.seqWB n₁ n₂ (netWB w₁) (netWB w₂) (toWitness sb) (netMoves w₁)

  netSync : ∀ {n} → WBNet n → Synchronous (netTheory n)
  netSync {base G} (base {q = q}) =
    pres→netSync (base G) (toWitness q)
  netSync {n₁ ∥ n₂} (w₁ ∥ w₂) =
    ParSync.parSync n₁ n₂ (netSync w₁) (netSync w₂)
  netSync {n₁ ⨾ n₂} ((w₁ ⨾ w₂) {sc = sc}) =
    SeqSync.seqSync n₁ n₂ (netSync w₁) (netSync w₂) (toWitness sc)

  wb-net : ∀ {n} → WBNet n → WellBehaved _
  wb-net {n} w = net→pres n (netWB w)

  sync-net : ∀ {n} → WBNet n → Synchronous _
  sync-net {n} w = net→presSync n (netSync w)

  -- As `Check/Graph.agda`'s, on `present n`.
  module _ {n} (w : WBNet n) where

    open Sessions (graphTheory (underlying (present n))) using (⊢ᵛ[_]_∶_; ⊢s[_]_∶_)

    typecheckNet : (Ps : PartSet) (Pr : Proc 0 0) → Dec (⊢ᵛ[ Ps ] Pr ∶ initial (present n))
    typecheckNet Ps Pr =
      typecheckView (underlying (present n)) (sync-net w) Ps Pr (initial (present n))

    typecheckSessionNet :
      ∀ {K} (Ρ : Assignment K) (M : Over.Session Ρ)
      → Dec (⊢s[ Ρ ] M ∶ initial (present n))
    typecheckSessionNet Ρ M = all? λ j → typecheckNet (lu (Assignment.roles Ρ) j) (lu M j)
