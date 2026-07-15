{-# OPTIONS --guardedness #-}

-- Port of `main`'s Examples/CounterExamples.agda: three processes for
-- participant `C` that should all be rejected by the type checker. `main`
-- proved each rejection by hand (~10 lines of case-splitting per process,
-- pattern-matching on every possible derivation shape); here `typecheck`
-- simply returns `no`, and `toWitnessFalse` extracts the actual refutation.
--
-- Both alternatives out of `s0` share the same sender *and* receiver
-- (`A ⟶ B`, different labels), so this isn't a "diamond" case (see
-- Examples/TODO.md) — but it still needs the raw graph construction, for a
-- *different* reason: the `LTS.Algebra` DSL's `choice`/`_∙_`/`end` allocate a
-- fresh node per use, and here the label-0 branch's `end` and the label-1
-- branch's eventual `end` are two separate (merely bisimilar, not equal)
-- states — which breaks `wellBehaved?`'s `Stepback` axiom (not diamond, but
-- the same root cause: two distinct states meant to represent the same
-- state). Confirmed by direct test: `wellBehaved?` fails on the two-`end`
-- construction and succeeds once both branches share one `end` index. So the
-- rule from the diamond finding turns out to be broader than diamond itself:
-- *any* state reachable by more than one path in an `OpenGraph` term needs a
-- literally shared index, not just independent-action convergence points.

module Examples.CounterExamples where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)

open import Definitions.Expr using (s/bool)
open import Definitions.TypeChecker
import Definitions.Typing as Typing

open import LTS.Algebra 3
open import Definitions.Actions 3 renaming (_<_> to mkChoice) hiding (_,_)
open import Definitions.Proc 3

A B C : Fin 3
A = zero
B = suc zero
C = suc (suc zero)

here : Fin 1
here = zero

-- the two labels of the A→B choice
lbl0 lbl1 : Fin 2
lbl0 = zero
lbl1 = suc zero

-- s0 --A→B[0]--> s2(end)
-- s0 --A→B[1]--> s1 --B→C--> s2(end)     (both branches share the same s2)
round : OpenGraph 0
round = openGraph 3 (inj₂ zero)
  ( ( ((A ⟶ B # mkChoice lbl0 s/bool) , inj₂ (suc (suc zero)))
    ∷ ((A ⟶ B # mkChoice lbl1 s/bool) , inj₂ (suc zero))
    ∷ [] )                                                            -- s0
  v∷ ( ((B ⟶ C # mkChoice here s/bool) , inj₂ (suc (suc zero))) ∷ [] ) -- s1
  v∷ [] v∷ v[]                                                        -- s2 = end
  )

wbg : WBGraph {N = 3}
wbg = buildG round {p = tt}

open Typing.MPST (wb-of wbg) using (_&_⊢p_∶_)

-- `C` waits for two sequential messages from `B` — but `B` only ever
-- forwards *one* message to `C` (the label-1 branch), so this is ill-typed.
p/C2 : Proc 0 0
p/C2 = Σ B ？[ s/bool v∷ v[] ]· (Σ B ？[ s/bool v∷ v[] ]· (∅ v∷ v[]) v∷ v[])

wtd/C2 : Dec (v[] & v[] ⊢p C ◂ p/C2 ∶ initial (proj₁ wbg))
wtd/C2 = typecheck wbg C p/C2

C2-illtyped : ¬ (v[] & v[] ⊢p C ◂ p/C2 ∶ initial (proj₁ wbg))
C2-illtyped = toWitnessFalse {a? = wtd/C2} _

-- `C` waits to receive from `A` first — but `C` is never a direct receiver
-- of `A`'s initial choice (only `B` is), so this is ill-typed.
p/C3 : Proc 0 0
p/C3 = Σ A ？[ s/bool v∷ v[] ]· (Σ B ？[ s/bool v∷ v[] ]· (∅ v∷ v[]) v∷ v[])

wtd/C3 : Dec (v[] & v[] ⊢p C ◂ p/C3 ∶ initial (proj₁ wbg))
wtd/C3 = typecheck wbg C p/C3

C3-illtyped : ¬ (v[] & v[] ⊢p C ◂ p/C3 ∶ initial (proj₁ wbg))
C3-illtyped = toWitnessFalse {a? = wtd/C3} _

-- an unproductive loop — `rec (v zero)` immediately refers to the
-- recursion variable with no message action first, violating
-- `MessageGuarded`, so this is ill-typed regardless of the graph.
p/C4 : Proc 0 0
p/C4 = rec (v zero)

wtd/C4 : Dec (v[] & v[] ⊢p C ◂ p/C4 ∶ initial (proj₁ wbg))
wtd/C4 = typecheck wbg C p/C4

C4-illtyped : ¬ (v[] & v[] ⊢p C ◂ p/C4 ∶ initial (proj₁ wbg))
C4-illtyped = toWitnessFalse {a? = wtd/C4} _

-- sanity check that the graph itself is sound (the rejections above aren't
-- vacuous): the "obviously correct" single-receive process for `C` *does*
-- type check.
p/C-good : Proc 0 0
p/C-good = Σ B ？[ s/bool v∷ v[] ]· (∅ v∷ v[])

wtd/C-good : Dec (v[] & v[] ⊢p C ◂ p/C-good ∶ initial (proj₁ wbg))
wtd/C-good = typecheck wbg C p/C-good

C-good-well-typed : v[] & v[] ⊢p C ◂ p/C-good ∶ initial (proj₁ wbg)
C-good-well-typed = toWitness {a? = wtd/C-good} _
