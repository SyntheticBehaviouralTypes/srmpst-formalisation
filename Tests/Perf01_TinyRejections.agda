{-# OPTIONS --guardedness #-}

-- Forced rejections of `rec (v 0)` on tiny graphs.  `rec (v 0)` is not
-- `MessageGuarded`, so every one of these must come back `no`, and cheaply.
--
-- These were seven files (`Perf01`–`Perf07`), written to isolate a blowup in
-- the old fuel-driven checker, one shape each: graph size, linear vs choice,
-- and which participant is checked (at the root, two hops deep, or never
-- mentioned).  That checker is gone; the shapes stay as a regression net,
-- one module each, so the file costs one Agda start-up instead of seven.

module Tests.Perf01_TinyRejections where

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

-- The single label of a one-choice action.  Its type pins `nchoices = 0`;
-- a bare `zero` leaves that implicit unsolved, and `wellBehaved?` then
-- grinds on a graph with a meta in it (560 s / 8 GB, then unsolved metas).
here : Fin 1
here = zero

-- A single state with no edges at all.
module MinimalGraph where
  open import Definitions.Graph.Algebra 1
  open import Definitions.Proc 1

  A : Fin 1
  A = zero

  wbg : WBGraph {N = 1}
  wbg = buildG end

  open Typing.MPST (wb-of wbg) using (_&_⊢p_∶_)

  wtd : Dec (v[] & v[] ⊢p A ◂ rec (v zero) ∶ initial (proj₁ wbg))
  wtd = typecheck wbg A (rec (v zero))

  _ : T (not ⌊ wtd ⌋)
  _ = _

-- `A → B`, end: size 2, no choice.
module Size2Linear where
  open import Definitions.Graph.Algebra 2
  open import Definitions.Actions 2 renaming (_<_> to mkChoice)
  open import Definitions.Proc 2

  A B : Fin 2
  A = zero
  B = suc zero

  wbg : WBGraph {N = 2}
  wbg = buildG ((A ⟶ B # mkChoice here s/bool) ∙ end)

  open Typing.MPST (wb-of wbg) using (_&_⊢p_∶_)

  wtd : Dec (v[] & v[] ⊢p A ◂ rec (v zero) ∶ initial (proj₁ wbg))
  wtd = typecheck wbg A (rec (v zero))

  _ : T (not ⌊ wtd ⌋)
  _ = _

-- `A → B → C`, end: size 3, no choice; checking `A` (at the root) and `C`
-- (two hops deep).
module Size3Linear where
  open import Definitions.Graph.Algebra 3
  open import Definitions.Actions 3 renaming (_<_> to mkChoice)
  open import Definitions.Proc 3

  A B C : Fin 3
  A = zero
  B = suc zero
  C = suc (suc zero)

  wbg : WBGraph {N = 3}
  wbg = buildG ((A ⟶ B # mkChoice here s/bool) ∙ ((B ⟶ C # mkChoice here s/bool) ∙ end))

  open Typing.MPST (wb-of wbg) using (_&_⊢p_∶_)

  wtdA : Dec (v[] & v[] ⊢p A ◂ rec (v zero) ∶ initial (proj₁ wbg))
  wtdA = typecheck wbg A (rec (v zero))

  _ : T (not ⌊ wtdA ⌋)
  _ = _

  wtdC : Dec (v[] & v[] ⊢p C ◂ rec (v zero) ∶ initial (proj₁ wbg))
  wtdC = typecheck wbg C (rec (v zero))

  _ : T (not ⌊ wtdC ⌋)
  _ = _

-- `A → B`, end, with a third participant `C` never mentioned: checking `C`
-- skips exactly one action.
module Size2LinearUninvolved where
  open import Definitions.Graph.Algebra 3
  open import Definitions.Actions 3 renaming (_<_> to mkChoice)
  open import Definitions.Proc 3

  A B C : Fin 3
  A = zero
  B = suc zero
  C = suc (suc zero)

  wbg : WBGraph {N = 3}
  wbg = buildG ((A ⟶ B # mkChoice here s/bool) ∙ end)

  open Typing.MPST (wb-of wbg) using (_&_⊢p_∶_)

  wtd : Dec (v[] & v[] ⊢p C ◂ rec (v zero) ∶ initial (proj₁ wbg))
  wtd = typecheck wbg C (rec (v zero))

  _ : T (not ⌊ wtd ⌋)
  _ = _

-- A 2-way choice at the root, both branches to the shared `ended`.
module Size2Choice where
  open import Definitions.Graph.Algebra 2
  open import Definitions.Actions 2 renaming (_<_> to mkChoice) hiding (_,_)
  open import Definitions.Proc 2

  A B : Fin 2
  A = zero
  B = suc zero

  lbl0 lbl1 : Fin 2
  lbl0 = zero
  lbl1 = suc zero

  round : OpenGraph 0
  round = openGraph 1 (node zero)
    ( ( ((A ⟶ B # mkChoice lbl0 s/bool) , ended)
      ∷ ((A ⟶ B # mkChoice lbl1 s/bool) , ended)
      ∷ [] )
    v∷ v[] )

  wbg : WBGraph {N = 2}
  wbg = buildG round {p = tt}

  open Typing.MPST (wb-of wbg) using (_&_⊢p_∶_)

  wtd : Dec (v[] & v[] ⊢p A ◂ rec (v zero) ∶ initial (proj₁ wbg))
  wtd = typecheck wbg A (rec (v zero))

  _ : T (not ⌊ wtd ⌋)
  _ = _

-- `Examples/CounterExamples.agda`'s graph (a 2-way `A → B` choice, one
-- branch continuing `B → C`), checking `A`, who is active at the root.
module Size3Choice where
  open import Definitions.Graph.Algebra 3
  open import Definitions.Actions 3 renaming (_<_> to mkChoice) hiding (_,_)
  open import Definitions.Proc 3

  A B C : Fin 3
  A = zero
  B = suc zero
  C = suc (suc zero)

  lbl0 lbl1 : Fin 2
  lbl0 = zero
  lbl1 = suc zero

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

  wtd : Dec (v[] & v[] ⊢p A ◂ rec (v zero) ∶ initial (proj₁ wbg))
  wtd = typecheck wbg A (rec (v zero))

  _ : T (not ⌊ wtd ⌋)
  _ = _
