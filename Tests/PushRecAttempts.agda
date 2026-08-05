{-# OPTIONS --guardedness #-}

-- Counterexample attempts for the `rec` case of `push`
-- (`Definitions/Typing/Norm.agda`).
--
-- THE QUESTION.  A derivation of shape
--
--     t/skip ⟨ tree from G, leaves at Lᵢ ⟩
--       where each leaf is   t/unskip (Wᵢ ⇝ Lᵢ) (t/rec mg bodyᵢ)
--
-- types `rec Pr′` at G.  Can the skip tree be pushed forward past the
-- `rec` — i.e. is there a single anchor W with W ⇝ G (or W = G) and the
-- body typable at W anchored W?
--
-- The interesting case is an OFF-PATH anchor: Wᵢ ⇝ Lᵢ but G does not
-- reach Wᵢ.  Each graph below is one shape for that.  `wellBehaved?`
-- decides each, so the verdict is a checked proof (`wb` / `not-wb`), not
-- a comment.  Edit freely: to test a shape, try `wb`; if it fails,
-- switch to `not-wb`.
--
-- CONSTRAINT worth knowing before designing a graph: the first action of
-- the skip must avoid A (it is a `¬A` step) but must involve B, or
-- `no-new-comm/step` demands that `A ⟶ B` already be available at the
-- source.  That single rule kills most naive shapes.
--
-- Throughout: P = A is the process being typed, and the body process is
-- `B ! 0 ∙ v 0` (A sends to B, then loops), which is message-guarded.

module Tests.PushRecAttempts where

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
open import Definitions.Graph.Core 4 using (State; graphTheory)
open import Definitions.Graph.Decision 4 using (wellBehaved?)
open import Definitions.Actions 4
  using (Action; _⟶_; _#_) renaming (_<_> to mkChoice)

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

A B C D : Fin 4
A = f0
B = f1
C = f2
D = f3

-- ════════════════════════════════════════════════════════════════
-- 1 — BASELINE, no off-path anchor.  G --B⟶C--> L, L --A⟶B--> L.
--
-- Well-behaved, and the skip IS pushable: `a/rec skip/refl` works at G,
-- because the body's `v 0` resolves with the anchor G via the very step
-- the tree took (`G ⇝ L`, `L ~ L`).  Included as the control: any
-- genuine counterexample must break this.
-- ════════════════════════════════════════════════════════════════

-- G=0  L=1   (2 = ended)
g₁ : OpenGraph 0
g₁ = openGraph 2 (node f0)
  ( ( ((B ⟶ C # mkChoice {nchoices = 0} f0 s/unit)       , node f1) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , node f1) ∷ [] )
  v∷ v[]
  )

G₁ = underlying (compile g₁)

wb₁ : Typing.WellBehaved (graphTheory G₁)
wb₁ = toWitness {a? = wellBehaved? G₁} tt

-- ════════════════════════════════════════════════════════════════
-- 2 — OFF-PATH ANCHOR, loop target bisimilar to the anchor.
--
--     G --B⟶C--> L,  W --B⟶D--> L,  L --A⟶B--> M,  M --B⟶D--> L
--
-- W is unreachable from G.  M ~ W by construction, so the body's `v 0`
-- resolves at W with an EMPTY witness.  From G the only `¬A`-reachable
-- states are {G, L}, and neither is bisimilar to M — so the variable
-- cannot resolve at M with anchor G.
--
-- SUSPECTED LEAK: `a/act` may skip from M *before* resolving the
-- variable, and M --B⟶D--> L lands in R(G).  Recorded so the leak can be
-- checked against the axioms rather than argued.
-- ════════════════════════════════════════════════════════════════

-- G=0  W=1  L=2  M=3   (4 = ended)
g₂ : OpenGraph 0
g₂ = openGraph 4 (node f0)
  ( ( ((B ⟶ C # mkChoice {nchoices = 0} f0 s/unit)       , node f2) ∷ [] )
  v∷ ( ((B ⟶ D # mkChoice {nchoices = 0} f0 s/unit)       , node f2) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , node f3) ∷ [] )
  v∷ ( ((B ⟶ D # mkChoice {nchoices = 0} f0 s/unit)       , node f2) ∷ [] )
  v∷ v[]
  )

G₂ = underlying (compile g₂)

not-wb₂ : ¬ Typing.WellBehaved (graphTheory G₂)
not-wb₂ = toWitnessFalse {a? = wellBehaved? G₂} tt

-- ════════════════════════════════════════════════════════════════
-- 3 — OFF-PATH ANCHOR, loop target bisimilar to the JOIN state.
--
--     G --B⟶C--> L,  W --B⟶D--> L,  L --A⟶B--> L
--
-- Same topology as 2 but the send loops straight back to L.  Now the
-- variable resolves at L from either anchor, so the anchor should move
-- freely — this is the shape that says an off-path anchor is not by
-- itself enough.
-- ════════════════════════════════════════════════════════════════

-- G=0  W=1  L=2   (3 = ended)
g₃ : OpenGraph 0
g₃ = openGraph 3 (node f0)
  ( ( ((B ⟶ C # mkChoice {nchoices = 0} f0 s/unit)       , node f2) ∷ [] )
  v∷ ( ((B ⟶ D # mkChoice {nchoices = 0} f0 s/unit)       , node f2) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , node f2) ∷ [] )
  v∷ v[]
  )

G₃ = underlying (compile g₃)

wb₃ : Typing.WellBehaved (graphTheory G₃)
wb₃ = toWitness {a? = wellBehaved? G₃} tt

-- ════════════════════════════════════════════════════════════════
-- 4 — TWO BRANCHES, TWO DIFFERENT ANCHORS.
--
--     G --B⟶C⟨0⟩--> L₁,  G --B⟶C⟨1⟩--> L₂
--     L₁ --A⟶B--> L₁,     L₂ --A⟶D--> L₂
--
-- The tree at G has two leaves whose recs are anchored at L₁ and L₂,
-- which are NOT bisimilar (different partners).  A single anchor at G
-- would have to serve both branches at once.
-- ════════════════════════════════════════════════════════════════

-- G=0  L₁=1  L₂=2   (3 = ended)
g₄ : OpenGraph 0
g₄ = openGraph 3 (node f0)
  ( ( ((B ⟶ C # mkChoice {nchoices = 1} f0 s/unit)       , node f1)
    ∷ ((B ⟶ C # mkChoice {nchoices = 1} f1 s/unit)       , node f2) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , node f1) ∷ [] )
  v∷ ( ((A ⟶ D # mkChoice {nchoices = 0} f0 s/unit)       , node f2) ∷ [] )
  v∷ v[]
  )

G₄ = underlying (compile g₄)

not-wb₄ : ¬ Typing.WellBehaved (graphTheory G₄)
not-wb₄ = toWitnessFalse {a? = wellBehaved? G₄} tt

-- ════════════════════════════════════════════════════════════════
-- 5 — OFF-PATH ANCHOR REACHED ONLY THROUGH AN A-ACTION.
--
--     G --B⟶C--> L,  L --A⟶B--> M,  M --B⟶D--> W,  W --A⟶B--> W
--
-- The rec's anchor W lies past an A-action, so no `¬A` trace from G can
-- reach it: R(G) = {G, L}.  The leaf at L is `t/unskip` from … nothing
-- that G sees.  This is the sharpest form of "off-path".
-- ════════════════════════════════════════════════════════════════

-- G=0  L=1  M=2  W=3   (4 = ended)
g₅ : OpenGraph 0
g₅ = openGraph 4 (node f0)
  ( ( ((B ⟶ C # mkChoice {nchoices = 0} f0 s/unit)       , node f1) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , node f2) ∷ [] )
  v∷ ( ((B ⟶ D # mkChoice {nchoices = 0} f0 s/unit)       , node f3) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , node f3) ∷ [] )
  v∷ v[]
  )

G₅ = underlying (compile g₅)

wb₅ : Typing.WellBehaved (graphTheory G₅)
wb₅ = toWitness {a? = wellBehaved? G₅} tt

-- ════════════════════════════════════════════════════════════════
-- 6 — ANCHOR AND ROOT JOIN ONLY UP TO BISIMILARITY.
--
--     G --B⟶C--> L,  W --B⟶D--> L′,  L ~ L′ but L ≢ L′
--     L --A⟶B--> L,  L′ --A⟶B--> L′
--
-- The two routes into the loop end at distinct-but-bisimilar states, so
-- reachability alone cannot identify them — only `~` can.  Tests whether
-- the anchor move needs bisimilarity rather than a trace.
-- ════════════════════════════════════════════════════════════════

-- G=0  W=1  L=2  L′=3   (4 = ended)
g₆ : OpenGraph 0
g₆ = openGraph 4 (node f0)
  ( ( ((B ⟶ C # mkChoice {nchoices = 0} f0 s/unit)       , node f2) ∷ [] )
  v∷ ( ((B ⟶ D # mkChoice {nchoices = 0} f0 s/unit)       , node f3) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , node f2) ∷ [] )
  v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} f0 s/unit)       , node f3) ∷ [] )
  v∷ v[]
  )

G₆ = underlying (compile g₆)

not-wb₆ : ¬ Typing.WellBehaved (graphTheory G₆)
not-wb₆ = toWitnessFalse {a? = wellBehaved? G₆} tt
