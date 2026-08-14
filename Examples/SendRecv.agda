{-# OPTIONS --guardedness #-}

-- Port of `main`'s Examples/SendRecv.agda onto the graph-based decision
-- procedure: the protocol is an `OpenGraph`, the session is typed by calling
-- `typecheckSession`, and there is no hand-written derivation anywhere in
-- this file (`main` needed one `t/send`/`t/recv` per case, plus a
-- `t/bisim (~sym ~unfold)` for the `RecursiveUnfoldOnce` variant).

module Examples.SendRecv where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using ([]; _∷_)
open import Data.Bool using (true)
open import Data.Product using (proj₁)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr using (s/bool; val; v/bool)
open import Check
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 2
open import Definitions.Actions 2 renaming (_<_> to mkChoice)
open import Definitions.Proc 2

A B : Fin 2
A = zero
B = suc zero

-- the singleton index: pins `I = 0` for a non-branching send/choice (Agda
-- can't otherwise solve it — nothing else in a bare `zero` constrains `I`).
here : Fin 1
here = zero

module NonRecursive where
  -- A --bool--> B, end
  sendrecv : OpenGraph 0
  sendrecv = (A ⟶ B # mkChoice here s/bool) ∙ end

  wbg : WBGraph {N = 2}
  wbg = buildG sendrecv

  open Typing.MPST (wb-of wbg) using (⊢s_∶_)

  p/A : Proc 0 0
  p/A = B ! here < val (v/bool true) >∙ ∅

  p/B : Proc 0 0
  p/B = Σ A ？· (∅ ∷ [])

  M : Session
  M = p/A ∷ p/B ∷ []

  -- the explicit `⊢s M ∶ G` type: decide it, then extract the derivation.
  wtd : Dec (⊢s M ∶ initial (proj₁ wbg))
  wtd = typecheckSession wbg M

  M-well-typed : ⊢s M ∶ initial (proj₁ wbg)
  M-well-typed = toWitness {a? = wtd} _

module Recursive where
  -- μ (A --bool--> loop)
  sendrecv : OpenGraph 0
  sendrecv = μ ((A ⟶ B # mkChoice here s/bool) ∙ var zero)

  wbg : WBGraph {N = 2}
  wbg = buildG sendrecv

  open Typing.MPST (wb-of wbg) using (⊢s_∶_)

  p/A : Proc 0 0
  p/A = rec (B ! here < val (v/bool true) >∙ v zero)

  p/B : Proc 0 0
  p/B = rec (Σ A ？· (v zero ∷ []))

  M : Session
  M = p/A ∷ p/B ∷ []

  wtd : Dec (⊢s M ∶ initial (proj₁ wbg))
  wtd = typecheckSession wbg M

  M-well-typed : ⊢s M ∶ initial (proj₁ wbg)
  M-well-typed = toWitness {a? = wtd} _

module RecursiveUnfoldOnce where
  -- same graph as `Recursive`, but `A`'s process unfolds the loop once
  -- before recursing — on `main` this needed an explicit bisimilarity-up-to-
  -- `unfold` step; here it's just another process for `typecheckSession` to
  -- check, no different from any other.
  open Recursive using (sendrecv; wbg)
  open Typing.MPST (wb-of wbg) using (⊢s_∶_)

  p/A : Proc 0 0
  p/A = B ! here < val (v/bool true) >∙ (rec (B ! here < val (v/bool true) >∙ v zero))

  p/B : Proc 0 0
  p/B = rec (Σ A ？· (v zero ∷ []))

  M : Session
  M = p/A ∷ p/B ∷ []

  wtd : Dec (⊢s M ∶ initial (proj₁ wbg))
  wtd = typecheckSession wbg M

  M-well-typed : ⊢s M ∶ initial (proj₁ wbg)
  M-well-typed = toWitness {a? = wtd} _
