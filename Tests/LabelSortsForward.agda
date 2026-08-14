{-# OPTIONS --guardedness #-}

-- Follow-up to `Tests/LabelSorts.agda`.  There, one label carried two sorts
-- at two leaves of a single receive's skip tree, and the branch body ignored
-- its bound variable.  Is ignoring it the ONLY option — is a process facing
-- two sorts forced to discard the value?
--
-- No.  The body must typecheck under EVERY sort the leaves offer, and that is
-- satisfiable while USING the value, provided the protocol varies in lockstep
-- downstream:
--
--    A⟶C # 0<unit>       A⟶B # 0<nat>        B⟶C # 0<nat>
-- s₀ ───────────────► s₁ ───────────────► t₁ ───────────────► ended
--  │
--  │ A⟶C # 1<unit>       A⟶B # 0<bool>       B⟶C # 0<bool>
--  └───────────────► s₂ ───────────────► t₂ ───────────────► ended
--
-- `p/B` forwards what it received: `C ! here < var zero >∙ ∅`.  At the `s/nat`
-- leaf `var zero ∶ s/nat` and the outgoing edge carries `s/nat`; at the
-- `s/bool` leaf both are `s/bool`.  So the receive types at `s₀` — through a
-- skip tree with two leaves at different sorts — with the value in use.
--
-- The process is, in effect, implicitly parametric in the payload sort: `⊢e`
-- assigns `var zero` the sort `lookup Γ x` (`te/var`), which is whatever the
-- leaf's context supplies.  What it CANNOT do is inspect the value
-- (`is-zero`, `minus1`), since those pin the sort — that is the rejected case
-- `M/bad` in `Tests/LabelSorts.agda`.

module Tests.LabelSortsForward where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
open import Data.Bool using (true)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr
  using (s/bool; s/nat; s/unit; val; v/nat; v/bool; v/unit; var)
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
      ((A ⟶ B # mkChoice here s/nat) ∙ (B ⟶ C # mkChoice here s/nat) ∙ end))
    ( ((A ⟶ C # mkChoice lbl1 s/unit) ⇒
        ((A ⟶ B # mkChoice here s/bool) ∙ (B ⟶ C # mkChoice here s/bool) ∙ end))
    ∷ [])

wbg : WBGraph {N = 3}
wbg = buildG g {p = tt}

open Typing.MPST (wb-of wbg) using (⊢s_∶_)

p/A : Proc 0 0
p/A =
  ifp val (v/bool true)
  then (C ! lbl0 < val v/unit >∙ (B ! here < val (v/nat 0) >∙ ∅))
  else (C ! lbl1 < val v/unit >∙ (B ! here < val (v/bool true) >∙ ∅))

-- USES the bound variable, at two different sorts, in one derivation
p/B : Proc 0 0
p/B = Σ A ？[ s/nat v∷ v[] ]· ((C ! here < var zero >∙ ∅) v∷ v[])

p/C : Proc 0 0
p/C =
  Σ A ？[ s/unit v∷ s/unit v∷ v[] ]·
    (  (Σ B ？[ s/nat  v∷ v[] ]· (∅ v∷ v[]))
    v∷ (Σ B ？[ s/bool v∷ v[] ]· (∅ v∷ v[]))
    v∷ v[])

M : Session
M = p/A v∷ p/B v∷ p/C v∷ v[]

wtd : Dec (⊢s M ∶ initial (proj₁ wbg))
wtd = typecheckSession wbg M

well-typed : ⊢s M ∶ initial (proj₁ wbg)
well-typed = toWitness {a? = wtd} _
