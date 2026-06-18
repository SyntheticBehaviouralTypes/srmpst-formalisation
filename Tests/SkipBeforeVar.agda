{-# OPTIONS --guardedness #-}

-- `t/skip` before `t/var` cannot be replaced by `t/unskip tr (t/var eq)`.
--
--   s --β--> K --β--> ended        (β = B ⟶ C, so `A` is never active)
--
-- With `Δ = K ∷ []`, `v zero` types at `s` by stepping to `K`.  Nothing
-- reaches `s`, and `K ≁ s`, so no trace-only derivation exists.

module Tests.SkipBeforeVar where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr using (s/unit)
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 3
open import Definitions.Graph.Core 3 using (State; graphTheory; step⇒listed; gstep)
open import Definitions.Graph.Decision 3 using (wellBehaved?)
open import Definitions.Graph.Bisimulation 3
  using (Bisimilar; bisimulationCorrect; complete)
open import Definitions.Actions 3
  using (Action; _⟶_#_) renaming (_<_> to mkChoice)
open import Data.Fin.Subset using (⁅_⁆)

A B C : Fin 3
A = zero
B = suc zero
C = suc (suc zero)

-- `nchoices` pinned: an unsolved one blocks every decision on the graph.
β : Action
β = B ⟶ ⁅ C ⁆ # mkChoice {nchoices = 0} zero s/unit

g : OpenGraph 0
g = openGraph 2 (node zero)
  ( ( (β , node (suc zero)) ∷ [] )   -- s --β--> K
  v∷ ( (β , ended) ∷ [] )            -- K --β--> ended
  v∷ v[]
  )

G = underlying (compile g)

-- `opaque`: a transparent `toWitness (wellBehaved? G)` re-runs the decision
-- at every use site (28 GB here, against ~1 GB).
opaque
  wb : Typing.WellBehaved (graphTheory G)
  wb = toWitness {a? = wellBehaved? G} tt

open Typing.MPST wb hiding (_<_>; _⟶_#_)

s K E : State G
s = zero
K = suc zero
E = suc (suc zero)

A∉β : A ∉α β
A∉β = refl

na : ⁅ A ⁆ not-active-in s
na gr with step⇒listed gr
... | here refl = ∉α→∉αˢ⁅⁆ {A} {β} A∉β
... | there ()

-- (1) `v zero` DOES type at `s`, by walking forward to `K`.
ktd :
  ∀ {G″ β′} → (gr : s -< β′ >-> G″)
  → (v[] & (K v∷ v[]) ⊢p_∶_) & (s v∷ v[]) ⊢skip ⁅ A ⁆ ◂ (v zero) ∶ G″
ktd gr with step⇒listed gr
... | here refl = skip/main (t/var ~refl)
... | there ()

-- `{G' = K}` (ASCII apostrophe) must be given, since `wb` is opaque.
typed-via-skip : v[] & (K v∷ v[]) ⊢p ⁅ A ⁆ ◂ (v zero) ∶ s
typed-via-skip = t/skip (skip/step {α = β} {G' = K} (gstep tt) na ktd)

-- (2) … but no `t/unskip tr (t/var eq)` can: nothing reaches `s`.
no-edge-into-s : ∀ {H α} → ¬ (H -< α >-> s)
no-edge-into-s {zero} gr with step⇒listed gr
... | here ()
... | there ()
no-edge-into-s {suc zero} gr with step⇒listed gr
... | here ()
... | there ()
-- `ended` has no edges.
no-edge-into-s {suc (suc zero)} gr with step⇒listed gr
... | ()

reaches-s→≡ : ∀ {H} → H -[¬ ⁅ A ⁆ ]->* s → H ≡ s
reaches-s→≡ (_ , tr , _) = go tr
  where
  go : ∀ {H αs} → H -[ αs ]-> s → H ≡ s
  go tr/refl = refl
  go {H} (tr/step {G′ = M} gr tr) with go tr
  ... | refl = ⊥-elim (no-edge-into-s {H = H} gr)

-- `K ≁ s`, decided at the graph level (`bisim?`), which does not mention
-- `wb`.
K≁s : ¬ (K ~ s)
K≁s K~s = notBisim (complete (bisimulationCorrect G) K~s)
  where
  notBisim : Bisimilar G K s → ⊥
  notBisim ()

no-unskip-var : ¬ (∃[ H ] (K ~ H) × (H -[¬ ⁅ A ⁆ ]->* s))
no-unskip-var (H , K~H , tr) with reaches-s→≡ tr
... | refl = K≁s K~H
