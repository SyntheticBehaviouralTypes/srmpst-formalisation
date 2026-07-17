{-# OPTIONS --guardedness #-}

-- Same linear (no-choice) size-3 graph as Perf03, but checking participant C
-- (who is not present in the root state's action, only two hops deep) rather
-- than A. Isolates: does "skip to a deep participant" alone (without
-- branching) reproduce the slowdown, or is branching (multiple actions to
-- skip per state) also required?

module Tests.Perf06_Size3LinearCheckC where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[])
open import Data.Bool using (T; not)
open import Data.Product using (proj₁)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Definitions.Expr using (s/bool)
open import Definitions.TypeChecker
import Definitions.Typing as Typing

open import LTS.Algebra 3
open import Definitions.Actions 3 renaming (_<_> to mkChoice)
open import Definitions.Proc 3

A B C : Fin 3
A = zero
B = suc zero
C = suc (suc zero)

here : Fin 1
here = zero

-- A --bool--> B --bool--> C, end   (size 3: s0, s1, end; no choice)
g : OpenGraph 0
g = (A ⟶ B # mkChoice here s/bool) ∙ ((B ⟶ C # mkChoice here s/bool) ∙ end)

wbg : WBGraph {N = 3}
wbg = buildG g

open Typing.MPST (wb-of wbg) using (_&_⊢p_∶_)

p : Proc 0 0
p = rec (v zero)

-- check C (two hops deep) rather than A.
wtd : Dec (v[] & v[] ⊢p C ◂ p ∶ initial (proj₁ wbg))
wtd = typecheck wbg C p

_ : T (not ⌊ wtd ⌋)
_ = _
-- retime
