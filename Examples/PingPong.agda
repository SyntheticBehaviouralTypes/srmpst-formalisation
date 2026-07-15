{-# OPTIONS --guardedness #-}

-- Port of `main`'s Examples/PingPong.agda: A sends a bool to B, B replies
-- with a nat. `main` needed one `t/send`/`t/recv` pair per participant per
-- variant (plus, for the recursive variant, a `t/bisim (~sym ~unfold)`); here
-- `typecheckSession` discharges both variants outright.

module Examples.PingPong where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using ([]; _∷_)
open import Data.Bool using (true)
open import Data.Product using (proj₁)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr using (s/bool; s/nat; val; v/bool; v/nat)
open import Definitions.TypeChecker
import Definitions.Typing as Typing

open import LTS.Algebra 2
open import Definitions.Actions 2 renaming (_<_> to mkChoice)
open import Definitions.Proc 2

A B : Fin 2
A = zero
B = suc zero

here : Fin 1
here = zero

module NonRecursive where
  -- A --bool--> B --nat--> A, end
  ping-pong : OpenGraph 0
  ping-pong =
    (A ⟶ B # mkChoice here s/bool) ∙ ((B ⟶ A # mkChoice here s/nat) ∙ end)

  wbg : WBGraph {N = 2}
  wbg = buildG ping-pong

  open Typing.MPST (wb-of wbg) using (⊢s_∶_)

  p/A : Proc 0 0
  p/A = B ! here < val (v/bool true) >∙ (Σ B ？[ s/nat ∷ [] ]· (∅ ∷ []))

  p/B : Proc 0 0
  p/B =
    Σ A ？[ s/bool ∷ [] ]· ((A ! here < val (v/nat 0) >∙ ∅) ∷ [])

  M : Session
  M = p/A ∷ p/B ∷ []

  wtd : Dec (⊢s M ∶ initial (proj₁ wbg))
  wtd = typecheckSession wbg M

  M-well-typed : ⊢s M ∶ initial (proj₁ wbg)
  M-well-typed = toWitness {a? = wtd} _

module Recursive where
  -- μ (A --bool--> B --nat--> loop)
  ping-pong : OpenGraph 0
  ping-pong =
    μ ((A ⟶ B # mkChoice here s/bool) ∙ ((B ⟶ A # mkChoice here s/nat) ∙ var zero))

  wbg : WBGraph {N = 2}
  wbg = buildG ping-pong

  open Typing.MPST (wb-of wbg) using (⊢s_∶_)

  p/A : Proc 0 0
  p/A = rec (B ! here < val (v/bool true) >∙ (Σ B ？[ s/nat ∷ [] ]· (v zero ∷ [])))

  p/B : Proc 0 0
  p/B =
    rec (Σ A ？[ s/bool ∷ [] ]· ((A ! here < val (v/nat 0) >∙ v zero) ∷ []))

  M : Session
  M = p/A ∷ p/B ∷ []

  wtd : Dec (⊢s M ∶ initial (proj₁ wbg))
  wtd = typecheckSession wbg M

  M-well-typed : ⊢s M ∶ initial (proj₁ wbg)
  M-well-typed = toWitness {a? = wtd} _
