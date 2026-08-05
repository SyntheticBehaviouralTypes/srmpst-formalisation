{-# OPTIONS --guardedness #-}

-- Port of `main`'s Examples/RecMW.agda: a recursive master/workers protocol.
-- `M` sends a datum to `W1` then `W2`; the workers independently report to
-- `R` (the `M→W2` send and the `W1→R` report are interleavable — the graph
-- has a genuine diamond, with both interleavings converging); `R` then tells
-- `M` to continue (loop) or stop (→ `M` stops both workers, end).
--
-- The densest example on `main`: a hand-written `BTheory` (~200 lines) plus
-- SEVEN `Causal?`/`Active?` skip-justification pairs.  Here: one
-- `typecheckSession` call.  The diamond's convergence state and the loop
-- back to the initial state force the raw `openGraph` construction.

module Examples.RecMW where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Data.Bool using (true; false)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr
  using (s/bool; s/nat; val; v/nat; v/bool; is-zero; var)
open import Check hiding (base; _∥_; _⨾_)
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 4 renaming (var to gvar)
open import Definitions.Actions 4 renaming (_<_> to mkChoice) hiding (_,_)
open import Definitions.Proc 4

M R W1 W2 : Fin 4
M  = zero
R  = suc zero
W1 = suc (suc zero)
W2 = suc (suc (suc zero))

here : Fin 1
here = zero

-- M→W datum/stop ([nat, bool]); R→M continue/stop ([nat, bool])
lbl0 lbl1 : Fin 2
lbl0 = zero
lbl1 = suc zero

-- The protocol, written in the graph algebra: one round is `M→W1`, then the
-- *parallel* pair `M→W2 ∥ W1→R` (the diamond of interleavings comes out of
-- `∥` — no hand-placed convergence states), then `W2→R`; `R` then chooses
-- to loop or to stop (`M` stopping both workers, ended).
recmw : OpenGraph 0
recmw =
  μ ( (M ⟶ W1 # mkChoice lbl0 s/nat) ∙
      (   ((M ⟶ W2 # mkChoice lbl0 s/nat) ∙ end)
        ∥ ((W1 ⟶ R # mkChoice here s/nat) ∙ end)
      ⨾ (W2 ⟶ R # mkChoice here s/nat) ∙
        choice ((R ⟶ M # mkChoice lbl0 s/nat) ⇒ gvar zero)
               ( ((R ⟶ M # mkChoice lbl1 s/bool) ⇒
                   ((M ⟶ W1 # mkChoice lbl1 s/bool) ∙
                    (M ⟶ W2 # mkChoice lbl1 s/bool) ∙ end))
               ∷ []) ) )

wbg : WBGraph {N = 4}
wbg = buildG recmw {p = tt}

open Typing.MPST (wb-of wbg) using (⊢s_∶_)

p/M : Proc 0 0
p/M = rec (W1 ! lbl0 < val (v/nat 0) >∙
          (W2 ! lbl0 < val (v/nat 1) >∙
          (Σ R ？[ s/nat v∷ s/bool v∷ v[] ]·
            (  v zero
            v∷ (W1 ! lbl1 < val (v/bool false) >∙
                (W2 ! lbl1 < val (v/bool false) >∙ ∅))
            v∷ v[]))))

p/R : Proc 0 0
p/R = rec (Σ W1 ？[ s/nat v∷ v[] ]·
            (  (Σ W2 ？[ s/nat v∷ v[] ]·
                 (  (ifp is-zero (var zero)
                     then (M ! lbl1 < val (v/bool true) >∙ ∅)
                     else (M ! lbl0 < var (suc zero) >∙ v zero))
                 v∷ v[]))
            v∷ v[]))

-- both workers run the same shape: receive a datum, then loop reporting to
-- `R` until `M` says stop
p/W : Proc 0 0
p/W = Σ M ？[ s/nat v∷ s/bool v∷ v[] ]·
        (  (rec (R ! here < val (v/nat 0) >∙
                 (Σ M ？[ s/nat v∷ s/bool v∷ v[] ]·
                   (v zero v∷ ∅ v∷ v[]))))
        v∷ ∅
        v∷ v[])

Msess : Session
Msess = p/M v∷ p/R v∷ p/W v∷ p/W v∷ v[]

wtd : Dec (⊢s Msess ∶ initial (proj₁ wbg))
wtd = typecheckSession wbg Msess

M-well-typed : ⊢s Msess ∶ initial (proj₁ wbg)
M-well-typed = toWitness {a? = wtd} _
