{-# OPTIONS --guardedness #-}

-- Tests of `Check/Alg.agda`, every result forced.  `Ex6`: `rec` types at
-- `G` only with its anchor at `M`, a state `G` does not reach; the checker
-- must find it (`Past`).

module Tests.AlgCheck where

open import Data.Bool using (T; not)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness)
open import Data.Fin.Subset using (⁅_⁆)

open import Definitions.Expr using (s/unit; val; v/unit)
import Definitions.Typing as Typing

import Check.Alg
import Check.TypeCheck

-- ══════════════════════════════════════════════════════════════════════
--  Ex6 — the anchor-before-the-root counterexample
-- ══════════════════════════════════════════════════════════════════════

module Ex6 where

  open import Definitions.Graph.Algebra 4
  open import Definitions.Graph.Core 4 using (State; graphTheory)
  open import Definitions.Graph.Decision 4 using (wellBehaved?; synchronous?)
  open import Definitions.Actions 4
    using (Action; _⟶_#_) renaming (_<_> to mkChoice)

  A B C D : Fin 4
  A = zero
  B = suc zero
  C = suc (suc zero)
  D = suc (suc (suc zero))

  -- G=0  L=1  M=2  H=3   (4 = ended)
  --
  --   G --B⟶D--> L --A⟶B--> M --B⟶C⟨0⟩--> L
  --                            --B⟶C⟨1⟩--> H --A⟶B--> H
  g : OpenGraph 0
  g = openGraph 4 (node zero)
    ( ( ((B ⟶ ⁅ D ⁆ # mkChoice {nchoices = 0} zero s/unit) , node (suc zero)) ∷ [] )
    v∷ ( ((A ⟶ ⁅ B ⁆ # mkChoice {nchoices = 0} zero s/unit)
         , node (suc (suc zero))) ∷ [] )
    v∷ ( ((B ⟶ ⁅ C ⁆ # mkChoice {nchoices = 1} zero s/unit) , node (suc zero))
       ∷ ((B ⟶ ⁅ C ⁆ # mkChoice {nchoices = 1} (suc zero) s/unit)
         , node (suc (suc (suc zero)))) ∷ [] )
    v∷ ( ((A ⟶ ⁅ B ⁆ # mkChoice {nchoices = 0} zero s/unit)
         , node (suc (suc (suc zero)))) ∷ [] )
    v∷ v[]
    )

  Gr = underlying (compile g)

  -- `opaque`: see `Tests/SkipBeforeVar.agda`.
  opaque
    wb : Typing.WellBehaved (graphTheory Gr)
    wb = toWitness {a? = wellBehaved? Gr} tt

    sync : Typing.Synchronous (graphTheory Gr)
    sync = toWitness {a? = synchronous? Gr} tt

  open module M₆ = Typing.MPST wb hiding (Action; _⟶_#_; _<_>)
  open module K₆ = Check.Alg.AlgCheck 4 Gr wb using (alg?)
  open module T₆ = Check.TypeCheck.TypeCheck 4 Gr wb (Typing.Synchronous.bal sync)
    using (tc?)

  G L M H : State Gr
  G = zero
  L = suc zero
  M = suc (suc zero)
  H = suc (suc (suc zero))

  prog : Proc 0 0
  prog = rec (A ⇒ ⁅ B ⁆ ! (zero {0}) < val v/unit >∙ v zero)

  -- The anchor the checker has to find is `M`, which `G` does not reach:
  -- `M -[¬A]->* L` and the tree at `G` steps `G → L`.
  ex6-typed : T ⌊ alg? v[] ⁅ A ⁆ prog (v[] , G) ⌋
  ex6-typed = tt

  -- …and the same through `⊢p`.
  ex6-typed/p : T ⌊ tc? v[] v[] ⁅ A ⁆ prog G ⌋
  ex6-typed/p = tt

  -- `C` takes no part after `H`, but does after `G`.
  ended-at-H : T ⌊ tc? v[] v[] ⁅ C ⁆ ∅ H ⌋
  ended-at-H = tt

  ended-not-at-G : T (not ⌊ tc? v[] v[] ⁅ C ⁆ ∅ G ⌋)
  ended-not-at-G = tt

  -- An unguarded loop is rejected by `MessageGuarded`, with no search.
  unguarded : T (not ⌊ tc? v[] v[] ⁅ A ⁆ (rec (v zero)) G ⌋)
  unguarded = tt

-- ══════════════════════════════════════════════════════════════════════
--  A `t/skip` in front of a variable (cf. `Tests/SkipBeforeVar.agda`)
-- ══════════════════════════════════════════════════════════════════════

module SkipVar where

  open import Definitions.Graph.Algebra 3
  open import Definitions.Graph.Core 3 using (State; graphTheory)
  open import Definitions.Graph.Decision 3 using (wellBehaved?; synchronous?)
  open import Definitions.Actions 3
    using (Action; _⟶_#_) renaming (_<_> to mkChoice)

  A B C : Fin 3
  A = zero
  B = suc zero
  C = suc (suc zero)

  β : Action
  β = B ⟶ ⁅ C ⁆ # mkChoice {nchoices = 0} zero s/unit

  -- s --β--> K --β--> ended;  `A` is active nowhere.
  g : OpenGraph 0
  g = openGraph 2 (node zero)
    ( ( (β , node (suc zero)) ∷ [] )
    v∷ ( (β , ended) ∷ [] )
    v∷ v[]
    )

  Gr = underlying (compile g)

  opaque
    wb : Typing.WellBehaved (graphTheory Gr)
    wb = toWitness {a? = wellBehaved? Gr} tt

    sync : Typing.Synchronous (graphTheory Gr)
    sync = toWitness {a? = synchronous? Gr} tt

  open module M₃ = Typing.MPST wb hiding (Action; _⟶_#_; _<_>)
  open module K₃ = Check.TypeCheck.TypeCheck 3 Gr wb (Typing.Synchronous.bal sync)
    using (tc?)

  s K : State Gr
  s = zero
  K = suc zero

  -- `v zero` types at `s` only by stepping forward to `K`.
  skip-before-var : T ⌊ tc? v[] (K v∷ v[]) ⁅ A ⁆ (v zero) s ⌋
  skip-before-var = tt

  -- `B` is active at `s`, so it cannot step forward, and `K ≁ s`.
  no-var-for-B : T (not ⌊ tc? v[] (K v∷ v[]) ⁅ B ⁆ (v zero) s ⌋)
  no-var-for-B = tt
