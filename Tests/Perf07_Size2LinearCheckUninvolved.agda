{-# OPTIONS --guardedness #-}

-- Size-2 linear graph (single A->B edge, then end), N=3 so a third
-- participant C exists but is never mentioned anywhere in the graph.
-- Checking C requires skipping exactly *one* action (the A->B edge) before
-- reaching `end`. Isolates: is skip-depth-1 already slow, or does it take
-- skip-depth-2 (as in Perf06) to trigger the blowup?

module Tests.Perf07_Size2LinearCheckUninvolved where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[])
open import Data.Bool using (T; not)
open import Data.Product using (proj₁)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Definitions.Expr using (s/bool)
open import Check
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 3
open import Definitions.Actions 3 renaming (_<_> to mkChoice)
open import Definitions.Proc 3

A B C : Fin 3
A = zero
B = suc zero
C = suc (suc zero)

here : Fin 1
here = zero

-- A --bool--> B, end   (size 2: s0, end; C never appears)
g : OpenGraph 0
g = (A ⟶ B # mkChoice here s/bool) ∙ end

wbg : WBGraph {N = 3}
wbg = buildG g

open Typing.MPST (wb-of wbg) using (_&_⊢p_∶_)

p : Proc 0 0
p = rec (v zero)

-- check C, uninvolved, skip-depth 1.
wtd : Dec (v[] & v[] ⊢p C ◂ p ∶ initial (proj₁ wbg))
wtd = typecheck wbg C p

_ : T (not ⌊ wtd ⌋)
_ = _
-- retime
