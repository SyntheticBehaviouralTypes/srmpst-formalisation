{-# OPTIONS --guardedness #-}

-- Can ONE label carry DIFFERENT sorts at two states that a single receive
-- has to cover?  Yes — `step-sort-deterministic` compares two steps out of
-- *one* state, so it says nothing across states.
--
--        A⟶C # 0<unit>          A⟶B # 0<nat>
--   s₀ ──────────────────► s₁ ──────────────────► ended
--    │
--    │   A⟶C # 1<unit>          A⟶B # 0<bool>
--    └──────────────────► s₂ ──────────────────► ended
--
-- `A` makes an internal choice to `C`; in one branch it then sends `B` a
-- `nat`, in the other a `bool`, under the same label and the same arity.
-- The graph is well behaved (`buildG … {p = tt}` elaborates), and it survives
-- the "no new communication" axioms for a specific reason:
-- `no-new-comm/step` would push `A⟶B` back to `s₀` — making `B` active there,
-- and killing the skip — but only if the skip step involves neither `A` nor
-- `B`, and here it involves `A`.  `no-new-branch/step` never fires, since
-- `s₀` offers no `A⟶B` comm at all.
--
-- `B` is inactive at `s₀`, so its derivation is `a/skip` with a `skip/step`
-- branching over BOTH edges, landing on two `blocked/recv` leaves that type
-- the one branch under `s/nat ∷ []` and under `s/bool ∷ []` respectively.
--
-- Consequence for any set-based reformulation of the judgment: the set at
-- which branch `j` types must be indexed by `(j , U)`, not by `j` alone.
-- Indexing by `j` alone forces a choice between the two leaves, and both are
-- wrong — `M/good` below is the case a `s/bool`-only reading rejects, and
-- `M/bad` is the case a `s/nat`-only reading unsoundly accepts.
--
-- This file is also why `Σ` carries no declared sort vector: a single receive
-- covers leaves whose sorts differ, so there is no one sort to declare.  Each
-- branch's sort is read off the graph edge it matches.

module Tests.LabelSorts where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
open import Data.Bool using (true)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)

open import Definitions.Expr
  using (s/bool; s/nat; s/unit; val; v/nat; v/bool; v/unit; is-zero; var)
open import Check hiding (base; _∥_; _⨾_)
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 3 renaming (var to gvar)
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

g : OpenGraph 0
g =
  choice
    ((A ⟶ C # mkChoice lbl0 s/unit) ⇒
      ((A ⟶ B # mkChoice here s/nat) ∙ end))
    ( ((A ⟶ C # mkChoice lbl1 s/unit) ⇒
        ((A ⟶ B # mkChoice here s/bool) ∙ end))
    ∷ [])

wbg : WBGraph {N = 3}
wbg = buildG g {p = tt}

open Typing.MPST (wb-of wbg) using (⊢s_∶_)

-- `A` picks a branch, then sends the sort that branch carries
p/A : Proc 0 0
p/A =
  ifp val (v/bool true)
  then (C ! lbl0 < val v/unit >∙ (B ! here < val (v/nat 0) >∙ ∅))
  else (C ! lbl1 < val v/unit >∙ (B ! here < val (v/bool true) >∙ ∅))

p/C : Proc 0 0
p/C = Σ A ？· (∅ v∷ ∅ v∷ v[])

-- ══════════════════════════════════════════════════════════════════════
--  Accepted: the branch ignores its bound variable, so both sorts are fine
-- ══════════════════════════════════════════════════════════════════════

p/B : Proc 0 0
p/B = Σ A ？·(∅ v∷ v[])

M/good : Session
M/good = p/A v∷ p/B v∷ p/C v∷ v[]

wtd/good : Dec (⊢s M/good ∶ initial (proj₁ wbg))
wtd/good = typecheckSession wbg M/good

well-typed : ⊢s M/good ∶ initial (proj₁ wbg)
well-typed = toWitness {a? = wtd/good} _

-- ══════════════════════════════════════════════════════════════════════
--  Control: the `s/bool` leaf really IS inspected
-- ══════════════════════════════════════════════════════════════════════
--
-- The only change is that the branch body now needs `var zero ∶ s/nat`.  If
-- the search visited only the `s/nat` leaf this would be accepted and
-- `toWitnessFalse` would fail to elaborate.

p/B′ : Proc 0 0
p/B′ = Σ A ？·((ifp is-zero (var zero) then ∅ else ∅) v∷ v[])

M/bad : Session
M/bad = p/A v∷ p/B′ v∷ p/C v∷ v[]

wtd/bad : Dec (⊢s M/bad ∶ initial (proj₁ wbg))
wtd/bad = typecheckSession wbg M/bad

not-well-typed : ¬ (⊢s M/bad ∶ initial (proj₁ wbg))
not-well-typed = toWitnessFalse {a? = wtd/bad} _
