{-# OPTIONS --guardedness #-}

-- Tests of `Check/Alg.agda`'s `inT?`, `unskip?` and `Wait?`, every result
-- forced.

module Tests.CheckAlgSanity where

open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Relation.Nullary.Decidable using (T?; True; False; from-yes)
open import Data.Vec using (lookup)
open import Data.Fin.Subset using (⁅_⁆)

open import Definitions.Expr using (s/unit)
open import Definitions.Behav using (WellBehaved)

import Check.Alg

module ∈T?-sanity where

  open import Definitions.Graph.Algebra 3
  open import Definitions.Graph.Core 3 using (State; graphTheory)
  open import Definitions.Graph.Decision 3 using (wellBehaved?)
  open import Definitions.Actions 3
    using (_⟶_#_) renaming (_<_> to mkChoice)

  A B C : Fin 3
  A = 0F
  B = 1F
  C = 2F

  -- s0 --A⟶B<unit>--> s1 --A⟶B<unit>--> ended
  g : OpenGraph 0
  g = openGraph 2 (node 0F)
    ( ( ((A ⟶ ⁅ B ⁆ # mkChoice {nchoices = 0} 0F s/unit) , node 1F) ∷ [] )
    v∷ ( ((A ⟶ ⁅ B ⁆ # mkChoice {nchoices = 0} 0F s/unit) , ended) ∷ [] )
    v∷ v[]
    )

  Gr = underlying (compile g)

  opaque
    wb : WellBehaved (graphTheory Gr)
    wb = from-yes (wellBehaved? Gr)

  open Check.Alg.AlgCheck 3 Gr wb using (env; module Env)

  ∈T? = λ P → Env.inT? (env P)

  s0 s1 fin : State Gr
  s0  = 0F
  s1  = 1F
  fin = 2F

  A-∈T-s0 : True (∈T? ⁅ A ⁆ s0)
  A-∈T-s0 = tt

  B-∈T-s1 : True (∈T? ⁅ B ⁆ s1)
  B-∈T-s1 = tt

  -- `C` is mentioned nowhere in this graph at all.
  C-∉T-s0 : False (∈T? ⁅ C ⁆ s0)
  C-∉T-s0 = tt

  -- `A` (and everyone else) is inactive at the end: no outgoing edges.
  A-∉T-fin : False (∈T? ⁅ A ⁆ fin)
  A-∉T-fin = tt

-- ══════════════════════════════════════════════════════════════════════
--  `unskip?` filters by action: a run may pass a state where `P` is active.
-- ══════════════════════════════════════════════════════════════════════

module unskip?-sanity where

  open import Definitions.Graph.Algebra 3
  open import Definitions.Graph.Core 3 using (State; graphTheory)
  open import Definitions.Graph.Decision 3 using (wellBehaved?)
  open import Definitions.Actions 3
    using (_⟶_#_) renaming (_<_> to mkChoice)

  A B C : Fin 3
  A = 0F
  B = 1F
  C = 2F

  -- s0 --B⟶C--> s1 --A⟶B--> ended
  g : OpenGraph 0
  g = openGraph 2 (node 0F)
    ( ( ((B ⟶ ⁅ C ⁆ # mkChoice {nchoices = 0} 0F s/unit) , node 1F) ∷ [] )
    v∷ ( ((A ⟶ ⁅ B ⁆ # mkChoice {nchoices = 0} 0F s/unit) , ended) ∷ [] )
    v∷ v[]
    )

  Gr = underlying (compile g)

  opaque
    wb : WellBehaved (graphTheory Gr)
    wb = from-yes (wellBehaved? Gr)

  open Check.Alg.AlgCheck 3 Gr wb using (env; module Env)

  unskip? = λ P → Env.unskip? (env P)

  s0 s1 fin : State Gr
  s0  = 0F
  s1  = 1F
  fin = 2F

  -- Via `B⟶C`, though `A` is active at `s1`.
  s1-unskip-A : True (unskip? ⁅ A ⁆ s0 s1)
  s1-unskip-A = tt

  -- Only by taking the `A`-edge.
  fin-not-unskip-A : False (unskip? ⁅ A ⁆ s0 fin)
  fin-not-unskip-A = tt

-- ══════════════════════════════════════════════════════════════════════
--  `Wait?` on the same chain: `s0 --B⟶C--> s1 --A⟶B--> ended`.
-- ══════════════════════════════════════════════════════════════════════

module Wait?-sanity where

  open import Data.Bool using (Bool; true; false)
  open import Data.Vec using (Vec) renaming ([] to v[]; _∷_ to _v∷_)

  open import Definitions.Graph.Algebra 3
  open import Definitions.Graph.Core 3 using (State; graphTheory)
  open import Definitions.Graph.Decision 3 using (wellBehaved?)
  open import Definitions.Actions 3
    using (_⟶_#_) renaming (_<_> to mkChoice)

  A B C : Fin 3
  A = 0F
  B = 1F
  C = 2F

  g : OpenGraph 0
  g = openGraph 2 (node 0F)
    ( ( ((B ⟶ ⁅ C ⁆ # mkChoice {nchoices = 0} 0F s/unit) , node 1F) ∷ [] )
    v∷ ( ((A ⟶ ⁅ B ⁆ # mkChoice {nchoices = 0} 0F s/unit) , ended) ∷ [] )
    v∷ v[]
    )

  Gr = underlying (compile g)

  opaque
    wb : WellBehaved (graphTheory Gr)
    wb = from-yes (wellBehaved? Gr)

  open Check.Alg.AlgCheck 3 Gr wb using (env; module Probing)

  -- `Wait?` over a bit-vector leaf set.
  Wait? = λ P (leaves : Vec Bool 3) (s : State Gr) →
    Probing.Wait? P (env P) {δ = 0} (λ { (_ , t) → T? (lookup leaves t) }) (v[] , s)

  s0 s1 fin : State Gr
  s0  = 0F
  s1  = 1F
  fin = 2F

  leaf-s1 leaf-fin : Vec Bool 3
  leaf-s1  = false v∷ true  v∷ false v∷ v[]
  leaf-fin = false v∷ false v∷ true  v∷ v[]

  -- One `wv/step`, then a `wv/leaf` at `s1`.
  Wait-A-leaf-s1 : True (Wait? ⁅ A ⁆ leaf-s1 s0)
  Wait-A-leaf-s1 = tt

  -- `ended` is reached only through `A`'s edge, where `A` is active.
  Wait-A-leaf-fin-fails : False (Wait? ⁅ A ⁆ leaf-fin s0)
  Wait-A-leaf-fin-fails = tt
