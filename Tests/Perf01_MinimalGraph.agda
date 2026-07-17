{-# OPTIONS --guardedness #-}

-- Performance debugging (see Examples/TODO.md's "Blocking issue"): isolate
-- the smallest possible reproducer of `typecheck` being slow even on an
-- obviously-rejected process. Graph is a single state with *no* outgoing
-- edges at all (`end`) — as small as `OpenGraph 0` can be. If this alone is
-- slow, the blowup has nothing to do with graph size (state count, edges,
-- choices) and is purely about `processFuel`/the fuel-driven exploration
-- itself; if this is fast, graph size (iterated over by `Fin.any?`/
-- `Fin.all?` inside `checkWithFuelD`/`SkipDecide.semSkip?`) is a driving
-- factor and `Examples/CounterExamples.agda`'s 3-state graph is where the
-- blowup starts.

module Tests.Perf01_MinimalGraph where

open import Data.Fin using (Fin; zero)
open import Data.Vec using () renaming ([] to v[])
open import Data.Bool using (T; not)
open import Data.Product using (proj₁)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Definitions.TypeChecker
import Definitions.Typing as Typing

open import LTS.Algebra 1
open import Definitions.Proc 1

A : Fin 1
A = zero

-- the smallest possible graph: one state, no edges.
g : OpenGraph 0
g = end

wbg : WBGraph {N = 1}
wbg = buildG g

open Typing.MPST (wb-of wbg) using (_&_⊢p_∶_)

-- the smallest possible ill-typed process: an unguarded loop. Should be
-- rejected immediately via `MessageGuarded`, no graph exploration needed.
p : Proc 0 0
p = rec (v zero)

wtd : Dec (v[] & v[] ⊢p A ◂ p ∶ initial (proj₁ wbg))
wtd = typecheck wbg A p

-- force the decision to a bare Bool, no witness construction.
_ : T (not ⌊ wtd ⌋)
_ = _
