{-# OPTIONS --guardedness #-}

-- Port of `main`'s Examples/Rec2Buy.agda: a recursive two-buyer protocol.
-- `A` asks the seller `S` for an item and gets a price; then `A` repeatedly
-- either cancels (telling `B` and then `S`) or proposes a split to `B`, who
-- answers `yes` (→ `A` buys from `S`) or `no` (→ back to the proposal
-- point).  The `split`/`no` cycle re-enters the protocol mid-chain (`s4 →
-- s2`) and both final branches share the terminal state, so the graph is
-- built with the raw `openGraph` constructor and explicit indices.
--
-- On `main`: a hand-written `BTheory` instance (~150 lines) plus several
-- `Causal?`/`Active?` skip lemmas for `S` and `B`.  Here: one
-- `typecheckSession` call.

module Examples.Rec2Buy where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr
  using (s/bool; s/nat; s/unit; val; v/nat; v/unit; is-zero; var)
open import Check
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 3 hiding (var)
open import Definitions.Actions 3 renaming (_<_> to mkChoice) hiding (_,_)
open import Definitions.Proc 3

A B S : Fin 3
A = zero
B = suc zero
S = suc (suc zero)

here : Fin 1
here = zero

lbl0 lbl1 : Fin 2
lbl0 = zero
lbl1 = suc zero

private
  -- state references (`Ref 0 6`)
  t0 t1 t2 t3 t4 t5 : Ref 0 6
  t0 = node zero
  t1 = node (suc zero)
  t2 = node (suc (suc zero))
  t3 = node (suc (suc (suc zero)))
  t4 = node (suc (suc (suc (suc zero))))
  t5 = node (suc (suc (suc (suc (suc zero)))))

-- s0 --A→S item(nat)--> s1 --S→A price(nat)--> s2
-- s2 --A→B split(nat)--> s4 | --A→B cancel(unit)--> s3
-- s4 --B→A yes(nat)--> s5   | --B→A no(unit)-----> s2   (the loop)
-- s3 --A→S no(unit)--> ended;  s5 --A→S buy(unit)--> ended
rec2buy : OpenGraph 0
rec2buy = openGraph 6 (node zero)
  (  ( ((A ⟶ S # mkChoice here s/nat) , t1) ∷ [] )                    -- s0
  v∷ ( ((S ⟶ A # mkChoice here s/nat) , t2) ∷ [] )                    -- s1
  v∷ ( ((A ⟶ B # mkChoice lbl0 s/nat) , t4)                           -- s2: split
     ∷ ((A ⟶ B # mkChoice lbl1 s/unit) , t3)                          --     cancel
     ∷ [] )
  v∷ ( ((A ⟶ S # mkChoice lbl1 s/unit) , ended) ∷ [] )                 -- s3: no-s
  v∷ ( ((B ⟶ A # mkChoice lbl0 s/nat) , t5)                           -- s4: yes
     ∷ ((B ⟶ A # mkChoice lbl1 s/unit) , t2)                          --     no (loop)
     ∷ [] )
  v∷ ( ((A ⟶ S # mkChoice lbl0 s/unit) , ended) ∷ [] )                 -- s5: buy
  v∷ v[]
  )

wbg : WBGraph {N = 3}
wbg = buildG rec2buy {p = tt}

open Typing.MPST (wb-of wbg) using (⊢s_∶_)

p/A : Proc 0 0
p/A =
  S ! here < val (v/nat 0) >∙
  (Σ S ？·
    ( rec (ifp is-zero (var zero)
           then (B ! lbl0 < val (v/nat 0) >∙
                 (Σ B ？·
                   (  (S ! lbl0 < val v/unit >∙ ∅)
                   v∷ v zero
                   v∷ v[])))
           else (B ! lbl1 < val v/unit >∙
                 (S ! lbl1 < val v/unit >∙ ∅)))
    v∷ v[]))

p/B : Proc 0 0
p/B =
  rec (Σ A ？·
        (  (ifp is-zero (var zero)
            then (A ! lbl0 < val (v/nat 0) >∙ ∅)
            else (A ! lbl1 < val v/unit >∙ v zero))
        v∷ ∅
        v∷ v[]))

p/S : Proc 0 0
p/S =
  Σ A ？·
    (  (A ! here < val (v/nat 0) >∙
        (Σ A ？· (∅ v∷ ∅ v∷ v[])))
    v∷ v[])

M : Session
M = p/A v∷ p/B v∷ p/S v∷ v[]

wtd : Dec (⊢s M ∶ initial (proj₁ wbg))
wtd = typecheckSession wbg M

M-well-typed : ⊢s M ∶ initial (proj₁ wbg)
M-well-typed = toWitness {a? = wtd} _
