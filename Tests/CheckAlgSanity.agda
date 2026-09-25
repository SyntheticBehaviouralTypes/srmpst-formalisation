{-# OPTIONS --guardedness #-}

-- Sanity checks for the pieces of `Check/Alg.agda` built so far
-- (TODO.md §7 step 6, in progress).  Every result is *forced*
-- (`T ⌊ … ⌋` / `not ⌊ … ⌋`), so this file compiling is the decision
-- procedure actually running, not just type-checking.

module Tests.CheckAlgSanity where

open import Data.Bool using (T; not)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; T?; _×-dec_)
open import Data.Vec using (lookup)
import Data.Fin.Properties as FinP

open import Definitions.Expr using (s/unit)
open import Definitions.Behav using (WellBehaved)

import Check.Alg

module ∈T?-sanity where

  open import Definitions.Graph.Algebra 3
  open import Definitions.Graph.Core 3 using (State; graphTheory)
  open import Definitions.Graph.Decision 3 using (wellBehaved?)
  open import Definitions.Actions 3
    using (Action; _⟶_; _#_) renaming (_<_> to mkChoice)

  A B C : Fin 3
  A = zero
  B = suc zero
  C = suc (suc zero)

  -- s0 --A⟶B<unit>--> s1 --A⟶B<unit>--> ended
  g : OpenGraph 0
  g = openGraph 2 (node zero)
    ( ( ((A ⟶ B # mkChoice {nchoices = 0} zero s/unit) , node (suc zero)) ∷ [] )
    v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} zero s/unit) , ended) ∷ [] )
    v∷ v[]
    )

  Gr = underlying (compile g)

  wb : WellBehaved (graphTheory Gr)
  wb = toWitness {a? = wellBehaved? Gr} tt

  open Check.Alg.AlgCheck 3 Gr wb using (env; module Env)

  ∈T? = λ P → Env.inT? (env P)

  s0 s1 fin : State Gr
  s0  = zero
  s1  = suc zero
  fin = suc (suc zero)

  -- `A` and `B` are both mentioned by every edge, everywhere upstream of
  -- the end.
  A-∈T-s0 : T ⌊ ∈T? A s0 ⌋
  A-∈T-s0 = tt

  B-∈T-s1 : T ⌊ ∈T? B s1 ⌋
  B-∈T-s1 = tt

  -- `C` is mentioned nowhere in this graph at all.
  C-∉T-s0 : T (not ⌊ ∈T? C s0 ⌋)
  C-∉T-s0 = tt

  -- `A` (and everyone else) is inactive at the end: no outgoing edges.
  A-∉T-fin : T (not ⌊ ∈T? A fin ⌋)
  A-∉T-fin = tt

-- ══════════════════════════════════════════════════════════════════════
--  `Reach₀?` on a state with BOTH a `P`-edge and an unrelated edge
--  enabled at once — the exact shape that makes a STATE-level filter
--  (`na?`) the wrong tool for `Reach₀`, and an ACTION-level filter the
--  only correct one.
-- ══════════════════════════════════════════════════════════════════════

module Reach₀?-sanity where

  open import Data.Bool using (Bool; true; false)
  open import Data.Vec using (Vec) renaming ([] to v[]; _∷_ to _v∷_)

  open import Definitions.Graph.Algebra 3
  open import Definitions.Graph.Core 3 using (State; graphTheory)
  open import Definitions.Graph.Decision 3 using (wellBehaved?)
  open import Definitions.Actions 3
    using (Action; _⟶_; _#_) renaming (_<_> to mkChoice)

  A B C : Fin 3
  A = zero
  B = suc zero
  C = suc (suc zero)

  -- s0 --B⟶C--> s1 --A⟶B--> ended
  --
  -- `s1` is reachable from `s0` without ever mentioning `A`; `ended` is not
  -- (the only edge into it is the `A`-edge itself).
  g : OpenGraph 0
  g = openGraph 2 (node zero)
    ( ( ((B ⟶ C # mkChoice {nchoices = 0} zero s/unit) , node (suc zero)) ∷ [] )
    v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} zero s/unit) , ended) ∷ [] )
    v∷ v[]
    )

  Gr = underlying (compile g)

  wb : WellBehaved (graphTheory Gr)
  wb = toWitness {a? = wellBehaved? Gr} tt

  open Check.Alg.AlgCheck 3 Gr wb using (env; module Env)

  -- The old `Reach₀?` from a bit-vector anchor, over the new `¬P`-run table.
  Reach₀? = λ P (anchor : Vec Bool 3) (t : State Gr) →
    FinP.any? λ a → T? (lookup anchor a) ×-dec Env.unskip? (env P) a t

  s0 s1 fin : State Gr
  s0  = zero
  s1  = suc zero
  fin = suc (suc zero)

  anchor-s0 : Vec Bool 3
  anchor-s0 = true v∷ false v∷ false v∷ v[]

  -- `s1` IS reachable from `s0` avoiding `A` entirely, via `B⟶C`.
  s1-Reach₀-A : T ⌊ Reach₀? A anchor-s0 s1 ⌋
  s1-Reach₀-A = tt

  -- `ended` is reachable from `s0` only by TAKING the `A`-edge, so it is
  -- not `¬A`-reachable.
  fin-not-Reach₀-A : T (not ⌊ Reach₀? A anchor-s0 fin ⌋)
  fin-not-Reach₀-A = tt

-- ══════════════════════════════════════════════════════════════════════
--  `Wait?` on the same chain: `s0 --B⟶C--> s1 --A⟶B--> ended`.
--  `A` is inactive at `s0` (its one edge is `B⟶C`), so `Wait A 𝒮 s0`
--  should walk that one step and defer to `s1`.
-- ══════════════════════════════════════════════════════════════════════

module Wait?-sanity where

  open import Data.Bool using (Bool; true; false)
  open import Data.Vec using (Vec) renaming ([] to v[]; _∷_ to _v∷_)

  open import Definitions.Graph.Algebra 3
  open import Definitions.Graph.Core 3 using (State; graphTheory)
  open import Definitions.Graph.Decision 3 using (wellBehaved?)
  open import Definitions.Actions 3
    using (Action; _⟶_; _#_) renaming (_<_> to mkChoice)

  A B C : Fin 3
  A = zero
  B = suc zero
  C = suc (suc zero)

  g : OpenGraph 0
  g = openGraph 2 (node zero)
    ( ( ((B ⟶ C # mkChoice {nchoices = 0} zero s/unit) , node (suc zero)) ∷ [] )
    v∷ ( ((A ⟶ B # mkChoice {nchoices = 0} zero s/unit) , ended) ∷ [] )
    v∷ v[]
    )

  Gr = underlying (compile g)

  wb : WellBehaved (graphTheory Gr)
  wb = toWitness {a? = wellBehaved? Gr} tt

  open Check.Alg.AlgCheck 3 Gr wb using (env; module Probing)

  -- The old `Wait?` over a bit-vector leaf set, over the new decider.
  Wait? = λ P (leaves : Vec Bool 3) (s : State Gr) →
    Probing.Wait? P (env P) {δ = 0} (λ { (_ , t) → T? (lookup leaves t) }) (v[] , s)

  s0 s1 fin : State Gr
  s0  = zero
  s1  = suc zero
  fin = suc (suc zero)

  leaf-s1 leaf-fin : Vec Bool 3
  leaf-s1  = false v∷ true  v∷ false v∷ v[]
  leaf-fin = false v∷ false v∷ true  v∷ v[]

  -- `A` is inactive at `s0`, and its only successor `s1` satisfies the
  -- leaf set — one `wv/step` then a `wv/leaf`.
  Wait-A-leaf-s1 : T ⌊ Wait? A leaf-s1 s0 ⌋
  Wait-A-leaf-s1 = tt

  -- The leaf set marks only `ended`, which is NOT reachable from `s0`
  -- without taking the `A`-edge at `s1` — `s1` itself has `A ∈T`, is not
  -- `na`, and is not a bisimilar ancestor, so no `WaitV` derivation exists.
  Wait-A-leaf-fin-fails : T (not ⌊ Wait? A leaf-fin s0 ⌋)
  Wait-A-leaf-fin-fails = tt
