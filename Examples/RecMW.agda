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
open import Definitions.TypeChecker
import Definitions.Typing as Typing

open import LTS.Algebra 4 hiding (var)
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

private
  t0 t1 t1a t1b t2 t3 t4 t5 t6 : Ref 0 9
  t0  = inj₂ zero
  t1  = inj₂ (suc zero)
  t1a = inj₂ (suc (suc zero))
  t1b = inj₂ (suc (suc (suc zero)))
  t2  = inj₂ (suc (suc (suc (suc zero))))
  t3  = inj₂ (suc (suc (suc (suc (suc zero)))))
  t4  = inj₂ (suc (suc (suc (suc (suc (suc zero))))))
  t5  = inj₂ (suc (suc (suc (suc (suc (suc (suc zero)))))))
  t6  = inj₂ (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

-- s0 --M→W1 datum--> s1;  s1 --M→W2 datum--> s1a  |  s1 --W1→R result--> s1b
-- s1a --W1→R result--> s2;  s1b --M→W2 datum--> s2      (the diamond)
-- s2 --W2→R result--> s3
-- s3 --R→M continue--> s0 (loop)  |  s3 --R→M stop--> s4
-- s4 --M→W1 stop--> s5 --M→W2 stop--> s6(end)
recmw : OpenGraph 0
recmw = openGraph 9 (inj₂ zero)
  (  ( ((M ⟶ W1 # mkChoice lbl0 s/nat) , t1) ∷ [] )                   -- s0
  v∷ ( ((M ⟶ W2 # mkChoice lbl0 s/nat) , t1a)
     ∷ ((W1 ⟶ R # mkChoice here s/nat) , t1b)
     ∷ [] )                                                           -- s1
  v∷ ( ((W1 ⟶ R # mkChoice here s/nat) , t2) ∷ [] )                   -- s1a
  v∷ ( ((M ⟶ W2 # mkChoice lbl0 s/nat) , t2) ∷ [] )                   -- s1b
  v∷ ( ((W2 ⟶ R # mkChoice here s/nat) , t3) ∷ [] )                   -- s2
  v∷ ( ((R ⟶ M # mkChoice lbl0 s/nat) , t0)
     ∷ ((R ⟶ M # mkChoice lbl1 s/bool) , t4)
     ∷ [] )                                                           -- s3
  v∷ ( ((M ⟶ W1 # mkChoice lbl1 s/bool) , t5) ∷ [] )                  -- s4
  v∷ ( ((M ⟶ W2 # mkChoice lbl1 s/bool) , t6) ∷ [] )                  -- s5
  v∷ []                                                               -- s6
  v∷ v[]
  )

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
