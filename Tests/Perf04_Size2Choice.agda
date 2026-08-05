{-# OPTIONS --guardedness #-}

-- Size-2, 2-way choice at the root (both branches to the same shared `end`),
-- negative decision. Isolates: does branching/choice alone (independent of
-- the linear "size 3" already shown fast) reproduce the slowdown?

module Tests.Perf04_Size2Choice where

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

open import Definitions.Graph.Algebra 2
open import Definitions.Actions 2 renaming (_<_> to mkChoice) hiding (_,_)
open import Definitions.Proc 2

A B : Fin 2
A = zero
B = suc zero

lbl0 lbl1 : Fin 2
lbl0 = zero
lbl1 = suc zero

-- s0 --A→B[0]--> ended
-- s0 --A→B[1]--> ended       (both branches share the same end state)
--
-- The shared end is `ended`, NOT a node of its own.  `compile` already
-- appends the ended state, so a spare edge-less node would be bisimilar
-- to it, and two distinct-but-bisimilar dead ends break `stepback/~`
-- (same death as the rejected graphs in `Tests/AnchorAttempts.agda`).
-- This file predates the `Ref` datatype — it used to say `inj₂`, from
-- back when a reference was a plain sum with no `ended` case.
round : OpenGraph 0
round = openGraph 1 (node zero)
  ( ( ((A ⟶ B # mkChoice lbl0 s/bool) , ended)
    ∷ ((A ⟶ B # mkChoice lbl1 s/bool) , ended)
    ∷ [] )
  v∷ v[] )

wbg : WBGraph {N = 2}
wbg = buildG round {p = tt}

open Typing.MPST (wb-of wbg) using (_&_⊢p_∶_)

p : Proc 0 0
p = rec (v zero)

wtd : Dec (v[] & v[] ⊢p A ◂ p ∶ initial (proj₁ wbg))
wtd = typecheck wbg A p

_ : T (not ⌊ wtd ⌋)
_ = _
