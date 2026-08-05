{-# OPTIONS --guardedness #-}

-- Port of `main`'s Examples/CounterExamples.agda: processes for participant
-- `C` that should be rejected by the type checker, plus one genuinely
-- well-typed process as a sanity check that the rejections aren't vacuous.
-- `main` proved each rejection by hand (~10 lines of case-splitting per
-- process); here `typecheck` simply returns `no`, and `toWitnessFalse`
-- extracts the actual refutation of the declarative judgment.
--
-- Graph-construction notes (see Examples/TODO.md):
--   * both A→B branches must eventually message `C` — on a graph where one
--     branch ends without involving `C`, *no* process for `C` is typeable
--     (`C ∈T s0` rules out `∅`, and a receive dies in the silent branch):
--     `C` cannot know which branch `A` chose.  An earlier version of this
--     file had exactly that graph and wrongly expected its "good" process
--     to typecheck — the (complete) decision procedure caught it.
--   * the two B→C states must not be bisimilar (here: distinct labels of a
--     2-ary choice), or the duplicate-but-bisimilar states break the
--     `Stepback` axiom of well-behavedness (same finding as the diamond
--     one: states meant to be "the same" need a literally shared node).
--   * the shared final state forces the raw `openGraph` construction — the
--     `Definitions.Graph.Algebra` DSL allocates a fresh node per use.

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
open import Check
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 3
open import Definitions.Actions 3 renaming (_<_> to mkChoice) hiding (_,_)
open import Definitions.Proc 3

A B C : Fin 3
A = zero
B = suc zero
C = suc (suc zero)

-- the two labels of the A→B choice (and of the B→C forwarding)
lbl0 lbl1 : Fin 2
lbl0 = zero
lbl1 = suc zero

-- s0 --A→B[0]--> s1 --B→C[0]--> ended
-- s0 --A→B[1]--> s2 --B→C[1]--> ended    (`ended` is the DSL's unique end)
round : OpenGraph 0
round = openGraph 3 (node zero)
  ( ( ((A ⟶ B # mkChoice lbl0 s/bool) , node (suc zero))
    ∷ ((A ⟶ B # mkChoice lbl1 s/bool) , node (suc (suc zero)))
    ∷ [] )                                                            -- s0
  v∷ ( ((B ⟶ C # mkChoice lbl0 s/bool) , ended) ∷ [] )                 -- s1
  v∷ ( ((B ⟶ C # mkChoice lbl1 s/bool) , ended) ∷ [] )                 -- s2
  v∷ v[]
  )

wbg : WBGraph {N = 3}
wbg = buildG round {p = tt}

open Typing.MPST (wb-of wbg) using (_&_⊢p_∶_)

-- the well-typed reference: `C` receives `B`'s (2-ary) forward, then ends
p/C-good : Proc 0 0
p/C-good = Σ B ？[ s/bool v∷ s/bool v∷ v[] ]· (∅ v∷ ∅ v∷ v[])

wtd/good : Dec (v[] & v[] ⊢p C ◂ p/C-good ∶ initial (proj₁ wbg))
wtd/good = typecheck wbg C p/C-good

C-good-well-typed : v[] & v[] ⊢p C ◂ p/C-good ∶ initial (proj₁ wbg)
C-good-well-typed = toWitness {a? = wtd/good} _

-- `C` waits for two sequential messages from `B` — but `B` only ever
-- forwards *one* message to `C`, so this is ill-typed.
p/C2 : Proc 0 0
p/C2 = Σ B ？[ s/bool v∷ s/bool v∷ v[] ]·
         (  Σ B ？[ s/bool v∷ s/bool v∷ v[] ]· (∅ v∷ ∅ v∷ v[])
         v∷ Σ B ？[ s/bool v∷ s/bool v∷ v[] ]· (∅ v∷ ∅ v∷ v[])
         v∷ v[])

wtd/C2 : Dec (v[] & v[] ⊢p C ◂ p/C2 ∶ initial (proj₁ wbg))
wtd/C2 = typecheck wbg C p/C2

C2-illtyped : ¬ (v[] & v[] ⊢p C ◂ p/C2 ∶ initial (proj₁ wbg))
C2-illtyped = toWitnessFalse {a? = wtd/C2} _

-- `C` waits to receive from `A` first — but `A` never messages `C`
-- directly, so this is ill-typed.
p/C3 : Proc 0 0
p/C3 = Σ A ？[ s/bool v∷ v[] ]·
         (Σ B ？[ s/bool v∷ s/bool v∷ v[] ]· (∅ v∷ ∅ v∷ v[]) v∷ v[])

wtd/C3 : Dec (v[] & v[] ⊢p C ◂ p/C3 ∶ initial (proj₁ wbg))
wtd/C3 = typecheck wbg C p/C3

C3-illtyped : ¬ (v[] & v[] ⊢p C ◂ p/C3 ∶ initial (proj₁ wbg))
C3-illtyped = toWitnessFalse {a? = wtd/C3} _

-- an unproductive loop — `rec (v zero)` immediately hits the recursion
-- variable with no message action first, violating `MessageGuarded`, so
-- this is ill-typed regardless of the graph.
p/C4 : Proc 0 0
p/C4 = rec (v zero)

wtd/C4 : Dec (v[] & v[] ⊢p C ◂ p/C4 ∶ initial (proj₁ wbg))
wtd/C4 = typecheck wbg C p/C4

C4-illtyped : ¬ (v[] & v[] ⊢p C ◂ p/C4 ∶ initial (proj₁ wbg))
C4-illtyped = toWitnessFalse {a? = wtd/C4} _
