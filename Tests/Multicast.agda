{-# OPTIONS --guardedness #-}

-- Multicast sends: `A ! {B, C}` synchronises with both receivers in one
-- step.  Every result is forced.
--
--   1. accepted: `A` multicasts to `⁅ B ⁆ ∪ ⁅ C ⁆`, both receive;
--   2. the receiver set is order-free: `⁅ C ⁆ ∪ ⁅ B ⁆` is the same set;
--   3. rejected: a receiver (`C`) is missing;
--   4. rejected: `A` sends to `⁅ B ⁆` only, against the two-receiver edge;
--   5. rejected by `synchronous?`: a self-send (`A ∈ Qs`), an empty
--      multicast (`Qs = ⊥`), and a lone receive with no sender;
--   6. accepted: `rec` over a multicast.

module Tests.Multicast where

open import Data.Bool using (true)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Fin.Subset using (⁅_⁆; _∪_; ⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
import Data.Vec as V
open V using () renaming ([] to v[]; _∷_ to _v∷_)
open import Relation.Nullary.Decidable using (True; False)

open import Definitions.Expr using (s/bool; val; v/bool)
open import Check

open import Definitions.Common 3 using (Part; PartSet)
open import Definitions.Graph.Algebra 3
open import Definitions.Graph.Decision 3 using (synchronous?)
open import Definitions.Actions 3
open import Definitions.Proc 3 hiding (rec; _⇐_？·_)
open import Definitions.Proc.Syntax 3
open import Utils.Branch using (⟪_⟫; _↦_; _∣_)

A B C : Fin 3
A = 0F
B = 1F
C = 2F

-- `A`'s one message (a single label pins `I = 0`)
announce : Fin 1
announce = 0F

BC CB : PartSet
BC = ⁅ B ⁆ ∪ ⁅ C ⁆
CB = ⁅ C ⁆ ∪ ⁅ B ⁆

recv : Part → Proc 0 0
recv R = R ⇐ A ？· ⟪ announce ↦ ∅ ⟫

-- ══════════════════════════════════════════════════════════════════════
--  1–4: one multicast, then end
-- ══════════════════════════════════════════════════════════════════════

module Once where

  g : OpenGraph 0
  g = A ⟶ BC # announce < s/bool > ∙ end

  wbg : WBGraph {N = 3}
  wbg = buildG g

  send : PartSet → Proc 0 0
  send Qs = A ⇒ Qs ! announce < val (v/bool true) >∙ ∅

  -- 1. accepted.
  accepted :
    True (typecheckSession wbg singletons
            (send BC v∷ recv B v∷ recv C v∷ v[]))
  accepted = tt

  -- 2. the receiver set is order-free.
  order-free :
    True (typecheckSession wbg singletons
            (send CB v∷ recv B v∷ recv C v∷ v[]))
  order-free = tt

  -- 3. `C` never receives.
  missing-receiver :
    False (typecheckSession wbg singletons (send BC v∷ recv B v∷ ∅ v∷ v[]))
  missing-receiver = tt

  -- 4. `A` sends to `B` alone, but the protocol's step is to `{B, C}`.
  wrong-receivers :
    False (typecheckSession wbg singletons
             (send ⁅ B ⁆ v∷ recv B v∷ recv C v∷ v[]))
  wrong-receivers = tt

-- ══════════════════════════════════════════════════════════════════════
--  5: not synchronous
-- ══════════════════════════════════════════════════════════════════════

module NotSynchronous where

  -- A self-send: `A` is among its own receivers.
  self : OpenGraph 0
  self = A ⟶ ⁅ A ⁆ # announce < s/bool > ∙ end

  self-rejected : False (synchronous? (underlying (compile self)))
  self-rejected = tt

  -- An empty multicast: `A` sends to nobody.
  nobody : OpenGraph 0
  nobody = A ⟶ ⊥ # announce < s/bool > ∙ end

  nobody-rejected : False (synchronous? (underlying (compile nobody)))
  nobody-rejected = tt

  -- A lone receive: `A` receives from itself, and nobody sends.
  lone : Action
  lone =
    just ((？ A) # announce < s/bool >) V.∷ nothing V.∷ nothing V.∷ V.[]

  lonely : OpenGraph 0
  lonely = lone ∙ end

  lone-rejected : False (synchronous? (underlying (compile lonely)))
  lone-rejected = tt

-- ══════════════════════════════════════════════════════════════════════
--  6: a loop of multicasts
-- ══════════════════════════════════════════════════════════════════════

module Loop where

  g : OpenGraph 0
  g = μ λ X → A ⟶ BC # announce < s/bool > ∙ X

  wbg : WBGraph {N = 3}
  wbg = buildG g

  p/A : Proc 0 0
  p/A = rec λ X → A ⇒ BC ! announce < val (v/bool true) >∙ X

  p/R : Part → Proc 0 0
  p/R R = rec λ X → R ⇐ A ？· ⟪ announce ↦ X ⟫

  looping :
    True (typecheckSession wbg singletons (p/A v∷ p/R B v∷ p/R C v∷ v[]))
  looping = tt
