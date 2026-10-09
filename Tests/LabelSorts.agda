{-# OPTIONS --guardedness #-}

-- Can ONE label carry DIFFERENT sorts at two states that a single receive
-- has to cover?  Yes — `step-sort-det` compares two steps out of
-- *one* state, so it says nothing across states.
--
--        A⟶C # 0<unit>          A⟶B # 0<nat>
--   s₀ ──────────────────► s₁ ──────────────────► ended
--    │
--    │   A⟶C # 1<unit>          A⟶B # 0<bool>
--    └──────────────────► s₂ ──────────────────► ended
--
-- `A` chooses a branch with `C`, then sends `B` a `nat` or a `bool` under
-- the same label.  `B`'s one receive must cover both sorts, so `a/recv`'s
-- continuations are indexed by `(j , U)`, not `j`.

module Tests.LabelSorts where

open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
open import Data.Bool using (true)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Nullary.Decidable using (from-yes; from-no)

open import Definitions.Expr
  using (s/bool; s/nat; s/unit; val; v/nat; v/bool; v/unit; is-zero; var)
open import Check hiding (base; _∥_; _⨾_)
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 3 renaming (var to gvar)
open import Data.Fin.Subset using (⁅_⁆)
open import Definitions.Actions 3 renaming (_<_> to mkChoice)
open import Definitions.Proc 3

A B C : Fin 3
A = 0F
B = 1F
C = 2F

here : Fin 1
here = 0F

lbl0 lbl1 : Fin 2
lbl0 = 0F
lbl1 = 1F

g : OpenGraph 0
g =
  choice
    ((A ⟶ ⁅ C ⁆ # mkChoice lbl0 s/unit) ⇒
      ((A ⟶ ⁅ B ⁆ # mkChoice here s/nat) ∙ end))
    ( ((A ⟶ ⁅ C ⁆ # mkChoice lbl1 s/unit) ⇒
        ((A ⟶ ⁅ B ⁆ # mkChoice here s/bool) ∙ end))
    ∷ [])

wbg : WBGraph {N = 3}
wbg = buildG g {p = tt}

open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_)

-- `A` picks a branch, then sends the sort that branch carries
p/A : Proc 0 0
p/A =
  ifp val (v/bool true)
  then (A ⇒ ⁅ C ⁆ ! lbl0 < val v/unit >∙
         (A ⇒ ⁅ B ⁆ ! here < val (v/nat 0) >∙ ∅))
  else (A ⇒ ⁅ C ⁆ ! lbl1 < val v/unit >∙
         (A ⇒ ⁅ B ⁆ ! here < val (v/bool true) >∙ ∅))

p/C : Proc 0 0
p/C = C ⇐ A ？· (∅ v∷ ∅ v∷ v[])

-- ══════════════════════════════════════════════════════════════════════
--  Accepted: the branch ignores its bound variable, so both sorts are fine
-- ══════════════════════════════════════════════════════════════════════

p/B : Proc 0 0
p/B = B ⇐ A ？·(∅ v∷ v[])

M/good : Over.Session singletons
M/good = p/A v∷ p/B v∷ p/C v∷ v[]

wtd/good : Dec (⊢s[ singletons ] M/good ∶ initial (proj₁ wbg))
wtd/good = typecheckSession wbg singletons M/good

well-typed : ⊢s[ singletons ] M/good ∶ initial (proj₁ wbg)
well-typed = from-yes wtd/good

-- ══════════════════════════════════════════════════════════════════════
--  Control: the `s/bool` leaf really IS inspected
-- ══════════════════════════════════════════════════════════════════════
--
-- The branch body needs `var 0F ∶ s/nat`, so the `s/bool` leaf rejects.

p/B′ : Proc 0 0
p/B′ = B ⇐ A ？·((ifp is-zero (var 0F) then ∅ else ∅) v∷ v[])

M/bad : Over.Session singletons
M/bad = p/A v∷ p/B′ v∷ p/C v∷ v[]

wtd/bad : Dec (⊢s[ singletons ] M/bad ∶ initial (proj₁ wbg))
wtd/bad = typecheckSession wbg singletons M/bad

not-well-typed : ¬ (⊢s[ singletons ] M/bad ∶ initial (proj₁ wbg))
not-well-typed = from-no wtd/bad
