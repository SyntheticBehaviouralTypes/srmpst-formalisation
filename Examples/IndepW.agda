{-# OPTIONS --guardedness #-}

-- Port of `main`'s Examples/IndepW.agda: two independent worker pipelines
-- `S → A1 → B1 → C1` and `S → A2 → B2 → C2` behind a shared source `S`,
-- with all cross-pipeline steps interleavable — the stress test for the
-- diamond/independence machinery.  The 7-state graph is `main`'s, verbatim
-- (it is already diamond-closed: every independent pair converges on a
-- literally shared state), built raw since it is nothing but shared states
-- and loops.
--
-- `main` needed ~1040 lines (custom `BTheory` + ~7 mutually recursive
-- `Active?`/`Causal?` families per pipeline) and never assembled a full
-- session judgment — only per-participant typings.  Here the whole 7-way
-- session is one `typecheckSession` call.

module Examples.IndepW where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr using (s/unit; val; v/unit)
open import Definitions.TypeChecker
import Definitions.Typing as Typing

open import LTS.Algebra 7 hiding (var)
open import Definitions.Actions 7 renaming (_<_> to mkChoice) hiding (_,_)
open import Definitions.Proc 7

S A1 B1 C1 A2 B2 C2 : Fin 7
S  = zero
A1 = suc zero
B1 = suc (suc zero)
C1 = suc (suc (suc zero))
A2 = suc (suc (suc (suc zero)))
B2 = suc (suc (suc (suc (suc zero))))
C2 = suc (suc (suc (suc (suc (suc zero)))))

here : Fin 1
here = zero

private
  t0 t1 t2 t3 t4 t5 t6 : Ref 0 7
  t0 = inj₂ zero
  t1 = inj₂ (suc zero)
  t2 = inj₂ (suc (suc zero))
  t3 = inj₂ (suc (suc (suc zero)))
  t4 = inj₂ (suc (suc (suc (suc zero))))
  t5 = inj₂ (suc (suc (suc (suc (suc zero)))))
  t6 = inj₂ (suc (suc (suc (suc (suc (suc zero))))))

  itm : Fin 7 → Fin 7 → _
  itm P Q = P ⟶ Q # mkChoice here s/unit

-- `main`'s 7-state interleaving graph, edge for edge
indepw : OpenGraph 0
indepw = openGraph 7 (inj₂ zero)
  (  ( (itm S A1 , t1) ∷ [] )                                -- s0
  v∷ ( (itm S A2 , t3) ∷ (itm A1 B1 , t2) ∷ [] )             -- s1
  v∷ ( (itm S A2 , t4) ∷ (itm B1 C1 , t1) ∷ [] )             -- s2
  v∷ ( (itm A1 B1 , t4) ∷ (itm A2 B2 , t5) ∷ [] )            -- s3
  v∷ ( (itm B1 C1 , t3) ∷ (itm A2 B2 , t6) ∷ [] )            -- s4
  v∷ ( (itm B2 C2 , t3) ∷ (itm A1 B1 , t6) ∷ [] )            -- s5
  v∷ ( (itm B1 C1 , t5) ∷ (itm B2 C2 , t4) ∷ [] )            -- s6
  v∷ v[]
  )

wbg : WBGraph {N = 7}
wbg = buildG indepw {p = tt}

open Typing.MPST (wb-of wbg) using (⊢s_∶_)

p/S : Proc 0 0
p/S = A1 ! here < val v/unit >∙ (A2 ! here < val v/unit >∙ ∅)

-- generic pipeline stages, as on `main`
p/A : Fin 7 → Proc 0 0
p/A B = Σ S ？[ s/unit v∷ v[] ]·
          (  (B ! here < val v/unit >∙
              (rec (B ! here < val v/unit >∙ v zero)))
          v∷ v[])

p/B : Fin 7 → Fin 7 → Proc 0 0
p/B A C = rec (Σ A ？[ s/unit v∷ v[] ]·
                ((C ! here < val v/unit >∙ v zero) v∷ v[]))

p/C : Fin 7 → Proc 0 0
p/C B = rec (Σ B ？[ s/unit v∷ v[] ]· (v zero v∷ v[]))

M : Session
M = p/S v∷ p/A B1 v∷ p/B A1 C1 v∷ p/C B1
        v∷ p/A B2 v∷ p/B A2 C2 v∷ p/C B2 v∷ v[]

wtd : Dec (⊢s M ∶ initial (proj₁ wbg))
wtd = typecheckSession wbg M

M-well-typed : ⊢s M ∶ initial (proj₁ wbg)
M-well-typed = toWitness {a? = wtd} _
