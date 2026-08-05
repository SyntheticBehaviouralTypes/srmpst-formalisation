{-# OPTIONS --guardedness #-}

-- Is `t/skip` in front of `t/var` essential, or can it always be
-- normalised to `t/unskip tr (t/var eq)` (i.e. an `h/var` carrying only a
-- trace)?  It is essential.
--
--   s --β--> K --β--> ended        (β = B ⟶ C, so `A` is never active)
--
-- With `Δ = K ∷ []`, `v zero` types at `s` by walking forward:
-- `t/skip (skip/step …)` whose single leaf is `t/var (K ~ K)` at `K`.
-- An `h/var` would need `H` with `K ~ H` and `H -[¬ A]->* s`; but nothing
-- at all reaches `s` (it has no incoming edges), so the only candidate is
-- `H = s`, and `K ≁ s`.

module Tests.SkipBeforeVar where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_; _×_; ∃-syntax; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr using (s/unit)
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 3
open import Definitions.Graph.Core 3 using (State; graphTheory; step⇒listed)
open import Definitions.Graph.Decision 3 using (wellBehaved?)
open import Definitions.Graph.Bisimulation 3
  using (Bisimilar; bisimulationCorrect; complete)
open import Definitions.Actions 3
  using (Action; _⟶_; _#_) renaming (_<_> to mkChoice)

A B C : Fin 3
A = zero
B = suc zero
C = suc (suc zero)

-- `nchoices` pinned: `zero : Fin (suc nchoices)` leaves it ambiguous, and
-- an unsolved metavariable inside the action blocks every decision that
-- has to compare it (`_≟Action_`, hence `bisim?`, hence `wellBehaved?`).
β : Action
β = B ⟶ C # mkChoice {nchoices = 0} zero s/unit

g : OpenGraph 0
g = openGraph 2 (node zero)
  ( ( (β , node (suc zero)) ∷ [] )   -- s --β--> K
  v∷ ( (β , ended) ∷ [] )            -- K --β--> ended
  v∷ v[]
  )

G = underlying (compile g)

-- `opaque`, and it matters enormously: `toWitness (wellBehaved? G)` is a
-- module-level *definition*, and Agda unfolds definitions at every use
-- site (it shares argument thunks, not definition applications).  Left
-- transparent, every type mentioning `Typing.MPST wb` that has to be
-- normalised re-runs the whole decision procedure, and the cost compounds
-- per definition: this file — a TWO-state graph — went from 28 GB
-- resident and an OOM kill to ~1 GB.  It is still a real proof; only the
-- body is hidden from the evaluator, unlike a postulate.  Anything that
-- genuinely has to *compute* with the witness would opt back in with
-- `opaque unfolding wb`; nothing here does.
opaque
  wb : Typing.WellBehaved (graphTheory G)
  wb = toWitness {a? = wellBehaved? G} tt

open Typing.MPST wb hiding (_<_>; _#_; _⟶_)

s K E : State G
s = zero
K = suc zero
E = suc (suc zero)

A∉β : A ∉α β
A∉β = ¬∈c→∉c (λ { (∈S ()) ; (∈R ()) })

na : A not-active-in s
na {α} {G′} gr with step⇒listed {G = G} {s = s} {α = α} {t = G′} gr
... | here refl = A∉β
... | there ()

-- (1) `v zero` DOES type at `s`, by walking forward to `K`.
ktd :
  ∀ {G″ β′} → (gr : s -< β′ >-> G″)
  → (v[] & (K v∷ v[]) ⊢p_∶_) & (s v∷ v[]) ⊢skip A ◂ (v zero) ∶ G″
ktd gr with step⇒listed {G = G} {s = s} gr
... | here refl = skip/main (t/var ~refl)
... | there ()

-- `{G' = K}` (ASCII apostrophe — that is how `skip/step` spells it) has to
-- be given: with `wb` opaque the target is no longer recoverable by
-- computing `tt`'s type.
typed-via-skip : v[] & (K v∷ v[]) ⊢p A ◂ (v zero) ∶ s
typed-via-skip = t/skip (skip/step {α = β} {G' = K} tt na ktd)

-- (2) … but no `t/unskip tr (t/var eq)` can: nothing reaches `s`.
no-edge-into-s : ∀ {H α} → ¬ (H -< α >-> s)
no-edge-into-s {zero} {α} gr with step⇒listed {G = G} {s = zero} {α = α} {t = s} gr
... | here ()
... | there ()
no-edge-into-s {suc zero} {α} gr
  with step⇒listed {G = G} {s = suc zero} {α = α} {t = s} gr
... | here ()
... | there ()
-- `suc (suc zero)` is the `ended` state, whose edge list is literally
-- `[]`, so there is no `here` clause to write.
no-edge-into-s {suc (suc zero)} {α} gr
  with step⇒listed {G = G} {s = suc (suc zero)} {α = α} {t = s} gr
... | ()

reaches-s→≡ : ∀ {H} → H -[¬ A ]->* s → H ≡ s
reaches-s→≡ (_ , tr , _) = go tr
  where
  go : ∀ {H αs} → H -[ αs ]-> s → H ≡ s
  go tr/refl = refl
  go {H} (tr/step {G′ = M} gr tr) with go tr
  ... | refl = ⊥-elim (no-edge-into-s {H = H} gr)

-- `K ≁ s`: `K` steps to `ended`, `s` steps to `K`, and `K ≁ ended`.
--
-- Decided rather than hand-proved, as in `Tests/AnchorAttempts.agda`.
-- The hand-written version projected out of `_~_` with
-- `~L→ K~s {α = β} {G′ = E} tt`, which has not type-checked since
-- `Behav.agda` gave `~L→` its current signature (all four implicits come
-- *before* the explicit `G~G′`, so they cannot be supplied after it, and
-- the one named `G′` is the bisimilar state, not the step's target).  The
-- 28 GB blowup masked the error — the file never got that far.  Deciding
-- it is also what keeps `wb` fully opaque: `bisim?~` computes from the
-- graph, so nothing here needs `unfolding wb`.
-- Decided at the GRAPH level (`bisim?`/`bisimulationCorrect`), which never
-- mentions `wb` — so this needs no `unfolding` and `wb` stays opaque
-- throughout the file.  Going through `GraphChecker.bisim?~` would not
-- work: that module is applied to `wb`, and a module application
-- elaborated outside the opaque block stays blocked no matter what
-- `unfolding` a later block declares.
K≁s : ¬ (K ~ s)
K≁s K~s = notBisim (complete (bisimulationCorrect G) K~s)
  where
  notBisim : Bisimilar G K s → ⊥
  notBisim ()

no-unskip-var : ¬ (∃[ H ] (K ~ H) × (H -[¬ A ]->* s))
no-unskip-var (H , K~H , tr) with reaches-s→≡ tr
... | refl = K≁s K~H
