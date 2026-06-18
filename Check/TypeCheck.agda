{-# OPTIONS --guardedness #-}

-- Deciding `⊢p` over a graph: `⊢p` at `(Δ , G)` is `⊢a` at that state
-- (`alg⇒typing`, `typing⇒alg`).

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
open import Data.Product using (_,_)

open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary.PropositionalEquality using (refl)

open import Definitions.Behav using (WellBehaved; Balanced)
open import Definitions.Expr using (Sort)

import Definitions.Typing as Typing
import Check.Alg

module Check.TypeCheck (N : ℕ) where

  open import Definitions.Graph.Core N using (Graph; graphTheory)

  -- `typing⇒alg` needs `bal`.
  module TypeCheck
    (G : Graph)
    (wb : WellBehaved (graphTheory G))
    (bal : Balanced (graphTheory G))
    where

    open Typing.MPST wb
    open import Definitions.Typing.Alg wb using (alg/mono)
    open import Definitions.Typing.AlgNorm wb using (typing⇒alg)
    open import Definitions.Typing.AlgDeclarative wb using (alg⇒typing)
    open Check.Alg.AlgCheck N G wb using (alg?)

    tc? :
      ∀ {γ δ}
        (Γ : Vec Sort γ)(Δ : Vec Behav δ)(P : PartSet)(Pr : Proc γ δ)
        (s : Behav)
      → Dec (Γ & Δ ⊢p P ◂ Pr ∶ s)
    tc? Γ Δ P Pr s =
      map′ (λ d → alg⇒typing d refl)
           (λ td → alg/mono (λ { refl → td }) (typing⇒alg bal Pr td))
           (alg? Γ P Pr (Δ , s))
