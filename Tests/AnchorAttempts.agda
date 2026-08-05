{-# OPTIONS --guardedness #-}

-- Counterexample attempts for `advance-anchor`, a lemma that was DELETED on
-- 2026-08-04 along with the whole "move the anchor" idea; see
-- `docs/2026-08-04-DONE-algorithmic-normalisation.md` §5e.  Kept because the
-- graphs are still useful well-behavedness specimens and because the
-- rejections record which axiom excludes which shape.
--
-- Each graph below is a candidate for the configuration that would block
-- the proof.  Where `wellBehaved?` REJECTS a graph, that is recorded as a
-- proof (`not-wb`), so this file compiles and the rejection is checked
-- rather than asserted in a comment.  Edit freely: to test a new shape,
-- add a graph and try `wb`; if it fails, switch to `not-wb`.
--
-- Actions are written out in full in the graph tables.  Reading key:
--
--     A ⟶ B # mkChoice {nchoices = 0} zero s/unit
--        the comm A ⟶ B, one label only
--     C ⟶ D # mkChoice {nchoices = 1} zero      s/unit
--     C ⟶ D # mkChoice {nchoices = 1} (suc zero) s/unit
--        the comm C ⟶ D with TWO labels — i.e. one branch point where C
--        chooses.  These two are the "same comm, distinct choice" pair
--        that `recv-overlap⇒same-comm` forces, and the whole question is
--        whether they can fail to commute.
--
-- Participants: A is the process being typed (`P`), so `A`-free actions
-- are the `¬P` ones.

module Tests.AnchorAttempts where

open import Data.Nat using (_+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)

open import Definitions.Expr using (s/unit)
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 4
open import Definitions.Graph.Core 4 using (State; graphTheory; _-<_>->_)
open import Definitions.Graph.Decision 4 using (wellBehaved?)
open import Definitions.Actions 4
  using (Action; _⟶_; _#_; _∉α_; _∉α?_) renaming (_<_> to mkChoice)

-- ── Fin shortcuts ───────────────────────────────────────────────
-- `f0 … f5` are the Fin literals, polymorphic in the bound, so the same
-- names serve as participants, node indices, labels and states.

f0 : ∀ {n} → Fin (1 + n)
f0 = zero

f1 : ∀ {n} → Fin (2 + n)
f1 = suc f0

f2 : ∀ {n} → Fin (3 + n)
f2 = suc f1

f3 : ∀ {n} → Fin (4 + n)
f3 = suc f2

f4 : ∀ {n} → Fin (5 + n)
f4 = suc f3

f5 : ∀ {n} → Fin (6 + n)
f5 = suc f4

A B C D : Fin 4
A = f0
B = f1
C = f2
D = f3

-- ════════════════════════════════════════════════════════════════
-- Attempt 1 — off-path anchor, dead-ending branches.  REJECTED.
-- `V₀ ~ V₁`, and `stepback/~` then wants a `C ⟶ D ⟨0⟩`-edge into `V₁`
-- from something bisimilar to `W₁`, which `step-deterministic` forbids.
-- ════════════════════════════════════════════════════════════════

-- W=0  H=1  K=2  W₁=3  V₀=4  V₁=5   (6 = ended)
g₁ : OpenGraph 0
g₁ = openGraph 6 (node f0)
  ( ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , node f3)
    ∷ ((C ⟶ D # mkChoice {nchoices = 1} f0 s/unit)       , node f1)
    ∷ ((C ⟶ D # mkChoice {nchoices = 1} f1 s/unit)       , node f2) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , node f4) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , node f5) ∷ [] )
  v∷ ( ((C ⟶ D # mkChoice {nchoices = 1} f0 s/unit)       , node f4)
     ∷ ((C ⟶ D # mkChoice {nchoices = 1} f1 s/unit)       , node f5) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , ended) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , ended) ∷ [] )
  v∷ v[]
  )

G₁ = underlying (compile g₁)

not-wb₁ : ¬ Typing.WellBehaved (graphTheory G₁)
not-wb₁ = toWitnessFalse {a? = wellBehaved? G₁} tt

-- ════════════════════════════════════════════════════════════════
-- Attempt 2 — same shape, branch targets self-looping on the P-action
-- so they are not dead ends.  REJECTED for the same reason: `H ~ K`.
-- ════════════════════════════════════════════════════════════════

-- W=0  H=1  K=2  W₁=3   (4 = ended)
g₂ : OpenGraph 0
g₂ = openGraph 4 (node f0)
  ( ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , node f3)
    ∷ ((C ⟶ D # mkChoice {nchoices = 1} f0 s/unit)       , node f1)
    ∷ ((C ⟶ D # mkChoice {nchoices = 1} f1 s/unit)       , node f2) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , node f1) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , node f2) ∷ [] )
  v∷ ( ((C ⟶ D # mkChoice {nchoices = 1} f0 s/unit)       , node f1)
     ∷ ((C ⟶ D # mkChoice {nchoices = 1} f1 s/unit)       , node f2) ∷ [] )
  v∷ v[]
  )

G₂ = underlying (compile g₂)

not-wb₂ : ¬ Typing.WellBehaved (graphTheory G₂)
not-wb₂ = toWitnessFalse {a? = wellBehaved? G₂} tt

-- ════════════════════════════════════════════════════════════════
-- Attempt 3 — the SHARP case: `step-commute`'s open clause.
--
--     W --C⟶D⟨0⟩--> K        (the advance hop)
--     W --C⟶D⟨1⟩--> H        (the witness hop, a DIFFERENT choice)
--     H --C⟶D⟨0⟩--> H₀       (the advance is still enabled at H)
--
-- `step-commute` needs `K --C⟶D⟨1⟩--> H₀`.  This graph deliberately
-- omits it: K goes to a separate state X.  REJECTED — and instructively
-- so: X and H₀ have the SAME continuation (`A ⟶ B` then end), so
-- `X ~ H₀`, and `stepback/~` then demands a `C ⟶ D ⟨0⟩`-edge into X from
-- something bisimilar to H, which `step-deterministic` forbids.  Same
-- death as 1 and 2.
-- ════════════════════════════════════════════════════════════════

-- W=0  K=1  H=2  H₀=3  X=4   (5 = ended)
g₃ : OpenGraph 0
g₃ = openGraph 5 (node f0)
  ( ( ((C ⟶ D # mkChoice {nchoices = 1} f0 s/unit)       , node f1)
    ∷ ((C ⟶ D # mkChoice {nchoices = 1} f1 s/unit)       , node f2) ∷ [] )
  v∷ ( ((C ⟶ D # mkChoice {nchoices = 1} f1 s/unit)       , node f4) ∷ [] )
  v∷ ( ((C ⟶ D # mkChoice {nchoices = 1} f0 s/unit)       , node f3) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , ended) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , ended) ∷ [] )
  v∷ v[]
  )

G₃ = underlying (compile g₃)

not-wb₃ : ¬ Typing.WellBehaved (graphTheory G₃)
not-wb₃ = toWitnessFalse {a? = wellBehaved? G₃} tt

-- ════════════════════════════════════════════════════════════════
-- Attempt 4 — attempt 3, but with the two targets made OBSERVABLY
-- DIFFERENT so the `X ~ H₀` collapse that killed 1–3 cannot happen:
-- H₀ continues with `A ⟶ B`, X with `A ⟶ C`.
--
-- REJECTED, but for an UNRELATED reason: `no-new-comm/step` fires
-- because `A ⟶ C` appears after a `C ⟶ D` step with `A` not involved in
-- it.  Inconclusive — hence attempt 5.
-- ════════════════════════════════════════════════════════════════

-- W=0  K=1  H=2  H₀=3  X=4   (5 = ended)
g₄ : OpenGraph 0
g₄ = openGraph 5 (node f0)
  ( ( ((C ⟶ D # mkChoice {nchoices = 1} f0 s/unit)       , node f1)
    ∷ ((C ⟶ D # mkChoice {nchoices = 1} f1 s/unit)       , node f2) ∷ [] )
  v∷ ( ((C ⟶ D # mkChoice {nchoices = 1} f1 s/unit)       , node f4) ∷ [] )
  v∷ ( ((C ⟶ D # mkChoice {nchoices = 1} f0 s/unit)       , node f3) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , ended) ∷ [] )
  v∷ ( ((A ⟶ C # mkChoice {nchoices = 0} f0 s/unit)       , ended) ∷ [] )
  v∷ v[]
  )

G₄ = underlying (compile g₄)

not-wb₄ : ¬ Typing.WellBehaved (graphTheory G₄)
not-wb₄ = toWitnessFalse {a? = wellBehaved? G₄} tt

-- ════════════════════════════════════════════════════════════════
-- Attempt 5 — THE COUNTEREXAMPLE.  The minimal premise configuration of
-- `step-commute`'s open clause.  Nothing is present but
--
--     W --C⟶D⟨0⟩--> K,   W --C⟶D⟨1⟩--> H,   H --C⟶D⟨0⟩--> H₀
--
-- and the targets are told apart using ONLY participants that C ⟶ D
-- itself involves (`D ⟶ A` from K, `C ⟶ A` from H₀), so neither the
-- `X ~ H₀` collapse of 1–3 nor the `no-new-comm/step` trip of 4 applies.
--
-- VERDICT: **ACCEPTED** (`wb₅` below is a checked proof).  All three
-- premises hold with P = A (A is in neither choice of C ⟶ D), and the
-- conclusion `K --C⟶D⟨1⟩--> H₀` fails — K's only edge is `D ⟶ A`.
-- `step-commute` is therefore FALSE, and no purely graph-level
-- commutation lemma can close the anchor case.
--
-- What it also shows is WHERE the missing hypothesis lives: A is
-- *active* at K (it receives in `D ⟶ A`).  A real anchor case does not
-- come with a bare step out of W but with a `⊢skip` tree, whose
-- `skip/step` covers ALL successors of W carrying `na`.  No such tree
-- exists here, because K would have to be a main leaf.  The replacement
-- lemma must consume the tree, not the step.
-- ════════════════════════════════════════════════════════════════

-- W=0  K=1  H=2  H₀=3   (4 = ended)
g₅ : OpenGraph 0
g₅ = openGraph 4 (node f0)
  ( ( ((C ⟶ D # mkChoice {nchoices = 1} f0 s/unit)       , node f1)
    ∷ ((C ⟶ D # mkChoice {nchoices = 1} f1 s/unit)       , node f2) ∷ [] )
  v∷ ( ((D ⟶ A # mkChoice {nchoices = 0} f0 s/unit)       , ended) ∷ [] )
  v∷ ( ((C ⟶ D # mkChoice {nchoices = 1} f0 s/unit)       , node f3) ∷ [] )
  v∷ ( ((C ⟶ A # mkChoice {nchoices = 0} f0 s/unit)       , ended) ∷ [] )
  v∷ v[]
  )

G₅ = underlying (compile g₅)

wb₅ : Typing.WellBehaved (graphTheory G₅)
wb₅ = toWitness {a? = wellBehaved? G₅} tt

-- ── attempt 5, machine-checked ──────────────────────────────────
--
-- `compile` keeps the node numbering (`node s ↦ inject₁ s`), so the
-- state indices are the ones written above.  A step is `T (edge? …)`, so
-- a present edge is inhabited by `tt` and an absent one is `⊥` — the
-- premises and the refutation are both direct.

W K H H₀ : State G₅
W  = f0
K  = f1
H  = f2
H₀ = f3

-- the advance hop
prem₁ : _-<_>->_ {G₅} W (C ⟶ D # mkChoice {nchoices = 1} f0 s/unit) K
prem₁ = tt

-- the witness hop, a DIFFERENT choice of the same comm
prem₂ : _-<_>->_ {G₅} W (C ⟶ D # mkChoice {nchoices = 1} f1 s/unit) H
prem₂ = tt

-- the advance is still enabled after the witness hop
prem₃ : _-<_>->_ {G₅} H (C ⟶ D # mkChoice {nchoices = 1} f0 s/unit) H₀
prem₃ = tt

-- both hops avoid the process being typed
prem₄ : A ∉α (C ⟶ D # mkChoice {nchoices = 1} f0 s/unit)
prem₄ = toWitness {a? = A ∉α? (C ⟶ D # mkChoice {nchoices = 1} f0 s/unit)} tt

prem₅ : A ∉α (C ⟶ D # mkChoice {nchoices = 1} f1 s/unit)
prem₅ = toWitness {a? = A ∉α? (C ⟶ D # mkChoice {nchoices = 1} f1 s/unit)} tt

-- …and the conclusion `step-commute` would give is FALSE.
refutation : ¬ (_-<_>->_ {G₅} K (C ⟶ D # mkChoice {nchoices = 1} f1 s/unit) H₀)
refutation ()

-- ════════════════════════════════════════════════════════════════
-- Attempt 6 — attempt 5 with the premise I should have carried all
-- along: `P not-active-in K` and `P not-active-in H₀`, which the
-- `⊢skip` tree at the call site supplies via `skip/step`'s `na`.
--
-- G₅ violated exactly this (A receives at K in `D ⟶ A`).  So the test
-- is whether that was essential or incidental: here the two targets are
-- told apart by `D ⟶ B` and `C ⟶ B`, senders still inside C ⟶ D so
-- `no-new-comm/step` is satisfied, but now A is nowhere, so both `na`
-- premises hold.
--
-- If ACCEPTED, adding `na` does NOT rescue the commutation and the
-- obligation must be attacked some other way.
-- ════════════════════════════════════════════════════════════════

-- W=0  K=1  H=2  H₀=3   (4 = ended)
g₆ : OpenGraph 0
g₆ = openGraph 4 (node f0)
  ( ( ((C ⟶ D # mkChoice {nchoices = 1} f0 s/unit)       , node f1)
    ∷ ((C ⟶ D # mkChoice {nchoices = 1} f1 s/unit)       , node f2) ∷ [] )
  v∷ ( ((D ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , ended) ∷ [] )
  v∷ ( ((C ⟶ D # mkChoice {nchoices = 1} f0 s/unit)       , node f3) ∷ [] )
  v∷ ( ((C ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , ended) ∷ [] )
  v∷ v[]
  )

G₆ = underlying (compile g₆)

wb₆ : Typing.WellBehaved (graphTheory G₆)
wb₆ = toWitness {a? = wellBehaved? G₆} tt
