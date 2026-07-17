{-# OPTIONS --guardedness #-}

-- Smoke test for the NEW restricted checker (Definitions/TypeChecker/
-- Restricted.agda) on exactly the shapes that made the old fuel-based
-- checker blow up:
--   * Perf06's case: 3-state linear graph A⟶B⟶C, checking participant C
--     (2 hops deep) with the trivially ill-formed `rec (v zero)` — the old
--     checker needs >90s; this should be seconds.
--   * the positive deep-skip case: C's correct process (receive from B,
--     then end), which requires skipping over s0 before C's receive at s1.

module Tests.Perf08_Restricted where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using ([])
open import Data.Bool using (T; not)
open import Data.Product using (proj₁)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Definitions.Expr using (s/bool)
open import Definitions.TypeChecker using (WBGraph; buildG; wb-of)
open import Definitions.TypeChecker.Restricted 3

open import LTS.Algebra 3
open import Definitions.Actions 3 renaming (_<_> to mkChoice)
open import Definitions.Proc 3

A B C : Fin 3
A = zero
B = suc zero
C = suc (suc zero)

here : Fin 1
here = zero

-- A --bool--> B --bool--> C, end   (Perf06's graph)
g : OpenGraph 0
g = (A ⟶ B # mkChoice here s/bool) ∙ ((B ⟶ C # mkChoice here s/bool) ∙ end)

wbg : WBGraph {N = 3}
wbg = buildG g

open GraphRestricted (underlying (proj₁ wbg)) (wb-of wbg)

-- negative: unguarded recursion, checked for the deep participant C
p/bad : Proc 0 0
p/bad = rec (v zero)

wtd/bad : Dec ([] & [] ⊢r C ◂ p/bad ∶ initial (proj₁ wbg))
wtd/bad = R? [] [] C p/bad (initial (proj₁ wbg))

_ : T (not ⌊ wtd/bad ⌋)
_ = _

-- positive: C's correct process — receive from B (2 hops deep), then end
p/good : Proc 0 0
p/good = Σ B ？[ s/bool ∷ [] ]· ((∅ ∷ []))
  where open Data.Vec using (_∷_)

wtd/good : Dec ([] & [] ⊢r C ◂ p/good ∶ initial (proj₁ wbg))
wtd/good = R? [] [] C p/good (initial (proj₁ wbg))

_ : T ⌊ wtd/good ⌋
_ = _

-- probe
