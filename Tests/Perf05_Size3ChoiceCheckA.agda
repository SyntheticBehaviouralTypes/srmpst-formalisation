{-# OPTIONS --guardedness #-}

-- Exact same 3-state graph as Examples/CounterExamples.agda (2-way choice at
-- s0 sharing sender/receiver A->B, then B->C, shared end), but checking
-- participant A (who *is* mentioned in the root state's edges) with the
-- trivial rejection, instead of C (who only appears two hops deep, via one
-- branch). Isolates: is checking a "deep" participant (not present at the
-- initial state) what's slow, or is it the 3-state+choice graph itself
-- regardless of which participant is checked?

module Tests.Perf05_Size3ChoiceCheckA where

open import Data.Fin using (Fin; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Bool using (T; not)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Definitions.Expr using (s/bool)
open import Check
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 3
open import Definitions.Actions 3 renaming (_<_> to mkChoice) hiding (_,_)
open import Definitions.Proc 3

A B C : Fin 3
A = zero
B = suc zero
C = suc (suc zero)

here : Fin 1
here = zero

lbl0 lbl1 : Fin 2
lbl0 = zero
lbl1 = suc zero

-- The end state is `ended`, NOT a node of its own: `compile` already
-- appends it, so a spare edge-less node would be bisimilar to it, and two
-- distinct-but-bisimilar dead ends break `stepback/~`.  This file predates
-- the `Ref` datatype — it used to say `inj₂`, from back when a reference
-- was a plain sum with no `ended` case.
round : OpenGraph 0
round = openGraph 2 (node zero)
  ( ( ((A ⟶ B # mkChoice lbl0 s/bool) , ended)
    ∷ ((A ⟶ B # mkChoice lbl1 s/bool) , node (suc zero))
    ∷ [] )                                              -- s0
  v∷ ( ((B ⟶ C # mkChoice here s/bool) , ended) ∷ [] )  -- s1
  v∷ v[]
  )

wbg : WBGraph {N = 3}
wbg = buildG round {p = tt}

open Typing.MPST (wb-of wbg) using (_&_⊢p_∶_)

p : Proc 0 0
p = rec (v zero)

-- check A (present at the initial state's edges) rather than C.
wtd : Dec (v[] & v[] ⊢p A ◂ p ∶ initial (proj₁ wbg))
wtd = typecheck wbg A p

_ : T (not ⌊ wtd ⌋)
_ = _
