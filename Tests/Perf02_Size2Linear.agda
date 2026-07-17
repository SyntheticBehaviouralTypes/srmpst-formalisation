{-# OPTIONS --guardedness #-}

-- Size-2, purely linear graph (one edge, no choice/branching at all),
-- negative decision. Isolates: does size alone (independent of branching)
-- already cause slowdown for a rejection?

module Tests.Perf02_Size2Linear where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[])
open import Data.Bool using (T; not)
open import Data.Product using (proj₁)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Definitions.Expr using (s/bool)
open import Definitions.TypeChecker
import Definitions.Typing as Typing

open import LTS.Algebra 2
open import Definitions.Actions 2 renaming (_<_> to mkChoice)
open import Definitions.Proc 2

A B : Fin 2
A = zero
B = suc zero

here : Fin 1
here = zero

-- A --bool--> B, end   (size 2: s0, end)
g : OpenGraph 0
g = (A ⟶ B # mkChoice here s/bool) ∙ end

wbg : WBGraph {N = 2}
wbg = buildG g

open Typing.MPST (wb-of wbg) using (_&_⊢p_∶_)

p : Proc 0 0
p = rec (v zero)

wtd : Dec (v[] & v[] ⊢p A ◂ p ∶ initial (proj₁ wbg))
wtd = typecheck wbg A p

_ : T (not ⌊ wtd ⌋)
_ = _
