{-# OPTIONS --guardedness #-}

-- Deciding the DECLARATIVE judgment `⊢p` (and `⊢s`) over a concrete graph.
--
-- `⊢p` at `(Δ , G)` is `⊢a` at the singleton `{(Δ , G)}`, both ways:
-- `alg⇒typing` (`AlgDeclarative.agda`) and `typing⇒alg` (`AlgNorm.agda`).
-- So `tc?` is `alg?` at that singleton.

open import Data.Nat using (ℕ)
open import Data.Fin.Properties as FinP using (_≟_)
open import Data.Vec using (Vec; [])
import Data.Vec.Properties as VecP
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Product.Properties using (≡-dec)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Definitions.Behav using (WellBehaved)
open import Definitions.Expr using (Sort)

import Definitions.Typing as Typing
import Check.Alg

module Check.TypeCheck (N : ℕ) where

  open import Definitions.Graph.Core N using (Graph; graphTheory)

  module TypeCheck
    (G : Graph)
    (wb : WellBehaved (graphTheory G))
    where

    open Typing.MPST wb
    open import Definitions.Typing.Alg wb
    open import Definitions.Typing.AlgNorm wb using (typing⇒alg)
    open import Definitions.Typing.AlgDeclarative wb using (alg⇒typing)
    open Check.Alg.AlgCheck N G wb
      using (Env; env; Shared; shared-tables; env-with; alg?-in)

    -- The singleton `{ x }`, decidably.
    at : ∀ {δ} → State δ → States δ
    at x = x ≡_

    at? : ∀ {δ}(x : State δ) → ∀ y → Dec (at x y)
    at? x = ≡-dec (VecP.≡-dec _≟_) _≟_ x

    -- Over a participant's tables built by the caller.
    tc?-in :
      ∀ {γ δ}{P : Part} → Env P
      → (Γ : Vec Sort γ)(Δ : Vec Behav δ)(Pr : Proc γ δ)(s : Behav)
      → Dec (Γ & Δ ⊢p P ◂ Pr ∶ s)
    tc?-in E Γ Δ Pr s =
      map′ (λ d → alg⇒typing d refl)
           (λ td → alg/mono (λ { refl → td }) (typing⇒alg Pr td))
           (alg?-in E Γ Pr (at (Δ , s)) (at? (Δ , s)))

    tc? :
      ∀ {γ δ}
        (Γ : Vec Sort γ)(Δ : Vec Behav δ)(P : Part)(Pr : Proc γ δ)(s : Behav)
      → Dec (Γ & Δ ⊢p P ◂ Pr ∶ s)
    tc? Γ Δ P = tc?-in (env P) Γ Δ

    -- The per-graph tables are computed ONCE, as an argument, and shared by
    -- every participant's tables.
    tcSession? : (M : Session)(s : Behav) → Dec (⊢s M ∶ s)
    tcSession? M s = with-tables shared-tables
      where
        with-tables : Shared → Dec (⊢s M ∶ s)
        with-tables sh =
          FinP.all? λ P → tc?-in (env-with sh P) [] [] (M [ P ]s) s
