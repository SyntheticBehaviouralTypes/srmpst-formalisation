{-# OPTIONS --guardedness #-}

-- Smoke tests for `Check/Alg.agda` — the decision procedure for `⊢a`, and
-- through it for `⊢p`.  Every result below is *forced* (`T ⌊ … ⌋`), so this
-- file compiling is the checker actually running, not just type-checking.
--
-- `Ex6` is the interesting one.  It is the counterexample from
-- `Stale/PushRecDerivations.agda.stale` that proved the OLD `⊢a`
-- incomplete for `⊢p`: `rec (B ! 0 ∙ v 0)` types at `G` declaratively, by
-- anchoring the `rec` at `M` — a state *before* `G`'s tree root — while
-- the old `a/rec` forced one common anchor for the whole tree.  The fix
-- was `blocked/rec`, which parks the anchor inside each leaf.  TODO.md
-- listed "does `Ex6` now go through?" as unverified; it does, and the
-- checker finds it by itself (`ex6-typed` below), which also exercises the
-- backward anchor search that is the only real search in the procedure.

module Tests.AlgCheck where

open import Data.Bool using (T; not)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness)

open import Definitions.Expr using (s/unit; val; v/unit)
import Definitions.Typing as Typing

import Check.Alg

-- ══════════════════════════════════════════════════════════════════════
--  Ex6 — the anchor-before-the-root counterexample
-- ══════════════════════════════════════════════════════════════════════

module Ex6 where

  open import Definitions.Graph.Algebra 4
  open import Definitions.Graph.Core 4 using (State; graphTheory)
  open import Definitions.Graph.Decision 4 using (wellBehaved?)
  open import Definitions.Actions 4
    using (Action; _⟶_; _#_) renaming (_<_> to mkChoice)

  A B C D : Fin 4
  A = zero
  B = suc zero
  C = suc (suc zero)
  D = suc (suc (suc zero))

  -- G=0  L=1  M=2  H=3   (4 = ended)
  --
  --   G --B⟶D--> L --A⟶B--> M --B⟶C⟨0⟩--> L
  --                            --B⟶C⟨1⟩--> H --A⟶B--> H
  g : OpenGraph 0
  g = openGraph 4 (node zero)
    ( ( ((B ⟶ D # mkChoice {nchoices = 0} zero s/unit) , node (suc zero)) ∷ [] )
    v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} zero s/unit)
         , node (suc (suc zero))) ∷ [] )
    v∷ ( ((B ⟶ C # mkChoice {nchoices = 1} zero s/unit) , node (suc zero))
       ∷ ((B ⟶ C # mkChoice {nchoices = 1} (suc zero) s/unit)
         , node (suc (suc (suc zero)))) ∷ [] )
    v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} zero s/unit)
         , node (suc (suc (suc zero)))) ∷ [] )
    v∷ v[]
    )

  Gr = underlying (compile g)

  wb : Typing.WellBehaved (graphTheory Gr)
  wb = toWitness {a? = wellBehaved? Gr} tt

  open module M₆ = Typing.MPST wb hiding (Action; _⟶_; _#_; _<_>)
  open module K₆ = Check.Alg.AlgCheck 4 Gr wb using (alg; tc?)

  G L M H : State Gr
  G = zero
  L = suc zero
  M = suc (suc zero)
  H = suc (suc (suc zero))

  prog : Proc 0 0
  prog = rec (B ! (zero {0}) < val v/unit >∙ v zero)

  -- The anchor the checker has to find is `M`, which `G` does not reach:
  -- `M -[¬A]->* L` and the tree at `G` steps `G → L`.
  ex6-typed : T ⌊ alg v[] v[] A prog G ⌋
  ex6-typed = tt

  -- …and the same through `⊢p`, i.e. `alg/typing`/`norm` really do close
  -- the loop (TODO.md Step 4).
  ex6-typed/p : T ⌊ tc? v[] v[] A prog G ⌋
  ex6-typed/p = tt

  -- `C` never sends or receives anything reachable from `H`, so the empty
  -- process types there; at `G` it does not, because `C` is still due to
  -- receive `B ⟶ C`.
  ended-at-H : T ⌊ tc? v[] v[] C ∅ H ⌋
  ended-at-H = tt

  ended-not-at-G : T (not ⌊ tc? v[] v[] C ∅ G ⌋)
  ended-not-at-G = tt

  -- An unguarded loop is rejected by `MessageGuarded`, with no search.
  unguarded : T (not ⌊ tc? v[] v[] A (rec (v zero)) G ⌋)
  unguarded = tt

-- ══════════════════════════════════════════════════════════════════════
--  A `t/skip` in front of a variable (cf. `Tests/SkipBeforeVar.agda`)
-- ══════════════════════════════════════════════════════════════════════

module SkipVar where

  open import Definitions.Graph.Algebra 3
  open import Definitions.Graph.Core 3 using (State; graphTheory)
  open import Definitions.Graph.Decision 3 using (wellBehaved?)
  open import Definitions.Actions 3
    using (Action; _⟶_; _#_) renaming (_<_> to mkChoice)

  A B C : Fin 3
  A = zero
  B = suc zero
  C = suc (suc zero)

  β : Action
  β = B ⟶ C # mkChoice {nchoices = 0} zero s/unit

  -- s --β--> K --β--> ended;  `A` is active nowhere.
  g : OpenGraph 0
  g = openGraph 2 (node zero)
    ( ( (β , node (suc zero)) ∷ [] )
    v∷ ( (β , ended) ∷ [] )
    v∷ v[]
    )

  Gr = underlying (compile g)

  wb : Typing.WellBehaved (graphTheory Gr)
  wb = toWitness {a? = wellBehaved? Gr} tt

  open module M₃ = Typing.MPST wb hiding (Action; _⟶_; _#_; _<_>)
  open module K₃ = Check.Alg.AlgCheck 3 Gr wb using (tc?)

  s K : State Gr
  s = zero
  K = suc zero

  -- `v zero` types at `s` only by walking forward to `K`: nothing reaches
  -- `s`, so no trace-only derivation exists.  This is the whole of the
  -- `¬ P ∈T` regime — no `skip/cycle` is available anywhere here.
  skip-before-var : T ⌊ tc? v[] (K v∷ v[]) A (v zero) s ⌋
  skip-before-var = tt

  -- `B`, by contrast, is active at `s` itself, so the tree cannot even
  -- take its first `skip/step` (`na` fails), `skip/cycle` has an empty
  -- `Ξ`, and `blocked/var` would need `K ~ s` — which is false, since `K`
  -- steps once and `s` steps twice.
  no-var-for-B : T (not ⌊ tc? v[] (K v∷ v[]) B (v zero) s ⌋)
  no-var-for-B = tt
