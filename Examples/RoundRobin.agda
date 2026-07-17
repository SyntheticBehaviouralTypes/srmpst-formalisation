{-# OPTIONS --guardedness #-}

-- Port of `main`'s Examples/RoundRobin.agda: a token ring A → B → C → A.
--
-- On `main` this was by far the worst manual proof burden of all examples:
-- two full multi-page `must-skip` instances (`MS1`, `MS2`) existed purely to
-- justify that `A` (having sent to `B`) skips over the intervening `B → C`
-- step before receiving from `C`, and likewise for `C` awaiting `B`.  All of
-- that is now a single `typecheckSession` call.
--
-- `main` also contains a commented-out `Recursive` variant it gave up on
-- (the manual skip burden per unfolding was evidently not worth it) — with
-- the decision procedure it costs nothing, so it is finished here.

module Examples.RoundRobin where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using ([]; _∷_)
open import Data.Bool using (true)
open import Data.Product using (proj₁)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr using (s/bool; val; v/bool)
open import Definitions.TypeChecker
import Definitions.Typing as Typing

open import LTS.Algebra 3
open import Definitions.Actions 3 renaming (_<_> to mkChoice)
open import Definitions.Proc 3

A B C : Fin 3
A = zero
B = suc zero
C = suc (suc zero)

here : Fin 1
here = zero

module NonRecursive where
  -- A --bool--> B --bool--> C --bool--> A, end
  round : OpenGraph 0
  round =
    (A ⟶ B # mkChoice here s/bool) ∙
    ((B ⟶ C # mkChoice here s/bool) ∙
     ((C ⟶ A # mkChoice here s/bool) ∙ end))

  wbg : WBGraph {N = 3}
  wbg = buildG round

  open Typing.MPST (wb-of wbg) using (⊢s_∶_)

  p/A : Proc 0 0
  p/A = B ! here < val (v/bool true) >∙ (Σ C ？[ s/bool ∷ [] ]· (∅ ∷ []))

  p/B : Proc 0 0
  p/B = Σ A ？[ s/bool ∷ [] ]· ((C ! here < val (v/bool true) >∙ ∅) ∷ [])

  p/C : Proc 0 0
  p/C = Σ B ？[ s/bool ∷ [] ]· ((A ! here < val (v/bool true) >∙ ∅) ∷ [])

  M : Session
  M = p/A ∷ p/B ∷ p/C ∷ []

  wtd : Dec (⊢s M ∶ initial (proj₁ wbg))
  wtd = typecheckSession wbg M

  M-well-typed : ⊢s M ∶ initial (proj₁ wbg)
  M-well-typed = toWitness {a? = wtd} _

module Recursive where
  -- μ (A --bool--> B --bool--> C --bool--> loop) — the variant `main` left
  -- unfinished.
  round : OpenGraph 0
  round =
    μ ((A ⟶ B # mkChoice here s/bool) ∙
       ((B ⟶ C # mkChoice here s/bool) ∙
        ((C ⟶ A # mkChoice here s/bool) ∙ var zero)))

  wbg : WBGraph {N = 3}
  wbg = buildG round

  open Typing.MPST (wb-of wbg) using (⊢s_∶_)

  p/A : Proc 0 0
  p/A = rec (B ! here < val (v/bool true) >∙
              (Σ C ？[ s/bool ∷ [] ]· (v zero ∷ [])))

  p/B : Proc 0 0
  p/B = rec (Σ A ？[ s/bool ∷ [] ]·
              ((C ! here < val (v/bool true) >∙ v zero) ∷ []))

  p/C : Proc 0 0
  p/C = rec (Σ B ？[ s/bool ∷ [] ]·
              ((A ! here < val (v/bool true) >∙ v zero) ∷ []))

  M : Session
  M = p/A ∷ p/B ∷ p/C ∷ []

  wtd : Dec (⊢s M ∶ initial (proj₁ wbg))
  wtd = typecheckSession wbg M

  M-well-typed : ⊢s M ∶ initial (proj₁ wbg)
  M-well-typed = toWitness {a? = wtd} _
