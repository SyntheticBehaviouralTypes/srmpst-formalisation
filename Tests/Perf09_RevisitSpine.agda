{-# OPTIONS --guardedness #-}

-- Regression test for skip-tree completeness: a well-behaved graph where
-- the only `prod` skip tree must REVISIT its spine.
--
--   u --A→B[0]--> t,   u --A→B[1]--> ℓ,   t --B→A--> u,   ℓ --A→C--> end
--
-- Checking C's receive at `u`: the skip tree steps u → t, and from `t` the
-- only continuation loops back to `u`, where the tree must step AGAIN
-- (visited or not) to reach `ℓ`.  A "fresh-stepping only" search would
-- close t → u as a nonprod cycle and wrongly reject this process — the
-- graph is well-behaved (the two u-actions share the comm A→B, so no
-- diamond forces the ℓ-branch to exist at `t`; the reply B→A overlaps A→B
-- in both participants, silencing no-new-comm/branch).  The semantic skip
-- clause (`SemSkipP`) accepts it, as it must.

module Tests.Perf09_RevisitSpine where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (toWitness)

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

-- states: 0 = u, 1 = t, 2 = ℓ, plus the DSL's distinguished end
g : OpenGraph 0
g = openGraph 3 (node zero)
  ( ( ((A ⟶ B # mkChoice lbl0 s/bool) , node (suc zero))
    ∷ ((A ⟶ B # mkChoice lbl1 s/bool) , node (suc (suc zero)))
    ∷ [] )                                                            -- u
  v∷ ( ((B ⟶ A # mkChoice here s/bool) , node zero) ∷ [] )            -- t → u
  v∷ ( ((A ⟶ C # mkChoice here s/bool) , ended) ∷ [] )                 -- ℓ
  v∷ v[]
  )

wbg : WBGraph {N = 3}
wbg = buildG g {p = tt}

open Typing.MPST (wb-of wbg) using (_&_⊢p_∶_)

-- C waits for A's message — deliverable only through the revisiting spine
p : Proc 0 0
p = Σ A ？· (∅ v∷ v[])

wtd : Dec (v[] & v[] ⊢p C ◂ p ∶ initial (proj₁ wbg))
wtd = typecheck wbg C p

C-well-typed : v[] & v[] ⊢p C ◂ p ∶ initial (proj₁ wbg)
C-well-typed = toWitness {a? = wtd} _
