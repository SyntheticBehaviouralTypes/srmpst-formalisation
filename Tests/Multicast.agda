{-# OPTIONS --guardedness #-}

-- Multicast sends (PLAN.md step 13).  One send, `A ! {B, C}`, synchronises
-- with BOTH receivers in one step.  Every result is FORCED (`T ⌊ … ⌋`,
-- `T (not ⌊ … ⌋)`), so this file compiling is the checker running.
--
--   1. accepted: `A` multicasts to `⁅ B ⁆ ∪ ⁅ C ⁆`, both receive;
--   2. the receiver set is order-free: `⁅ C ⁆ ∪ ⁅ B ⁆` is the same set;
--   3. rejected: a receiver (`C`) is missing;
--   4. rejected: `A` sends to `⁅ B ⁆` only, against the two-receiver edge;
--   5. rejected by `synchronous?`: a self-send (`A ∈ Qs`), an empty
--      multicast (`Qs = ⊥`), and a lone receive with no sender;
--   6. accepted: `rec` over a multicast.

module Tests.Multicast where

open import Data.Bool using (T; not; true)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Subset using (⁅_⁆; _∪_; ⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
import Data.Vec as V
open V using () renaming ([] to v[]; _∷_ to _v∷_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Definitions.Expr using (s/bool; val; v/bool)
open import Check

open import Definitions.Common 3 using (PartSet)
open import Definitions.Graph.Algebra 3
open import Definitions.Graph.Decision 3 using (synchronous?)
open import Definitions.Actions 3 renaming (_<_> to mkChoice)
open import Definitions.Proc 3

A B C : Fin 3
A = zero
B = suc zero
C = suc (suc zero)

-- the singleton index: pins `I = 0` for a non-branching send.
here : Fin 1
here = zero

BC CB : PartSet
BC = ⁅ B ⁆ ∪ ⁅ C ⁆
CB = ⁅ C ⁆ ∪ ⁅ B ⁆

recv : Proc 0 0
recv = Σ A ？· (∅ V.∷ V.[])

-- ══════════════════════════════════════════════════════════════════════
--  1–4: one multicast, then end
-- ══════════════════════════════════════════════════════════════════════

module Once where

  g : OpenGraph 0
  g = (A ⟶ BC # mkChoice here s/bool) ∙ end

  wbg : WBGraph {N = 3}
  wbg = buildG g

  send : PartSet → Proc 0 0
  send Qs = Qs ! here < val (v/bool true) >∙ ∅

  -- 1. accepted.
  accepted : T ⌊ typecheckSession wbg (send BC v∷ recv v∷ recv v∷ v[]) ⌋
  accepted = tt

  -- 2. the receiver set is order-free.
  order-free : T ⌊ typecheckSession wbg (send CB v∷ recv v∷ recv v∷ v[]) ⌋
  order-free = tt

  -- 3. `C` never receives.
  missing-receiver :
    T (not ⌊ typecheckSession wbg (send BC v∷ recv v∷ ∅ v∷ v[]) ⌋)
  missing-receiver = tt

  -- 4. `A` sends to `B` alone, but the protocol's step is to `{B, C}`.
  wrong-receivers :
    T (not ⌊ typecheckSession wbg (send ⁅ B ⁆ v∷ recv v∷ recv v∷ v[]) ⌋)
  wrong-receivers = tt

-- ══════════════════════════════════════════════════════════════════════
--  5: not synchronous
-- ══════════════════════════════════════════════════════════════════════

module NotSynchronous where

  -- A self-send: `A` is among its own receivers.
  self : OpenGraph 0
  self = (A ⟶ ⁅ A ⁆ # mkChoice here s/bool) ∙ end

  self-rejected : T (not ⌊ synchronous? (underlying (compile self)) ⌋)
  self-rejected = tt

  -- An empty multicast: `A` sends to nobody.
  nobody : OpenGraph 0
  nobody = (A ⟶ ⊥ # mkChoice here s/bool) ∙ end

  nobody-rejected : T (not ⌊ synchronous? (underlying (compile nobody)) ⌋)
  nobody-rejected = tt

  -- A lone receive: `A` receives from itself, and nobody sends.
  lone : Action
  lone =
    just ((？ A) # mkChoice here s/bool) V.∷ nothing V.∷ nothing V.∷ V.[]

  lonely : OpenGraph 0
  lonely = openGraph 1 (node zero) (((lone , ended) ∷ []) v∷ v[])

  lone-rejected : T (not ⌊ synchronous? (underlying (compile lonely)) ⌋)
  lone-rejected = tt

-- ══════════════════════════════════════════════════════════════════════
--  6: a loop of multicasts
-- ══════════════════════════════════════════════════════════════════════

module Loop where

  g : OpenGraph 0
  g = μ ((A ⟶ BC # mkChoice here s/bool) ∙ var zero)

  wbg : WBGraph {N = 3}
  wbg = buildG g

  p/A : Proc 0 0
  p/A = rec (BC ! here < val (v/bool true) >∙ v zero)

  p/R : Proc 0 0
  p/R = rec (Σ A ？· (v zero V.∷ V.[]))

  looping : T ⌊ typecheckSession wbg (p/A v∷ p/R v∷ p/R v∷ v[]) ⌋
  looping = tt
