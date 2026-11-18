{-# OPTIONS --guardedness #-}

-- `skip` before `var` cannot be replaced by `forward (var eq) run`.
--
--   s --β--> K --β--> ended        (β = B ⟶ C, so `A` is never active)
--
-- With `Δ = [ K ] ∷ []`, `v 0F` types at `[ s ]` by stepping to `K`.
-- Nothing reaches `s`, and `K ≁ s`, so no trace-only derivation exists.

module Tests.SkipBeforeVar where

open import Definitions.Expr.Syntax
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)
open import Relation.Nullary.Decidable using (from-yes)
open import Function.Bundles using (Equivalence)

open import Definitions.Expr using (s/unit)
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 3 hiding (var)
open import Definitions.Graph.Core 3 using (State; graphTheory; step⇒listed; gstep)
open import Definitions.Graph.Decision 3 using (wellBehaved?)
open import Definitions.Graph.Bisimulation 3
  using (Bisimilar; bisimulationCorrect)
open import Definitions.Actions 3
  using (Action; _⟶_#_; _<_>)
open import Data.Fin.Subset using (⁅_⁆)

A B C : Fin 3
A = 0F
B = 1F
C = 2F

-- a typed label pins `nchoices`: an unsolved one blocks every decision on
-- the graph.
tick : ℕ
tick = 0

β : Action
β = B ⟶ ⁅ C ⁆ # tick < s/unit >

g : OpenGraph 0
g = β ∙ β ∙ end   -- s --β--> K --β--> ended

G = underlying (compile g)

-- `opaque`: a transparent `toWitness (wellBehaved? G)` re-runs the decision
-- at every use site (28 GB here, against ~1 GB).
opaque
  wb : Typing.WellBehaved (graphTheory G)
  wb = from-yes (wellBehaved? G)

open Typing.MPST wb hiding (_<_>; _⟶_#_)

s K E : State G
s = 0F
K = 1F
E = 2F

A∉β : A ∉α β
A∉β = ≡nothing→∉α {A} {β} refl

na : ¬ s -⟨ ⁅ A ⁆ ⟩->
na (_ , _ , gr , own) with step⇒listed gr
... | here refl = ∉α→∉αˢ⁅⁆ {A} {β} A∉β own
... | there ()

-- (1) `v 0F` DOES type at `[ s ]`, by walking forward to `K`.
ktd :
  ∀ {β′ G″} → [ s ] C.-< β′ >-> G″
  → v[] & ([ K ] v∷ v[]) & ([ s ] v∷ v[]) ⊢[ ⁅ A ⁆ ] v 0F ∶ G″
ktd (_ , H″~ , gr) with step⇒listed gr
... | here refl = skip-main (var H″~)
... | there ()

typed-via-skip : v[] & ([ K ] v∷ v[]) ⊢[ ⁅ A ⁆ ] v 0F ∶ [ s ]
typed-via-skip =
  skip
    (skip-step (β , [ K ] , step⇒ᶜ {G′ = K} (gstep tt))
      (λ act → na (actᶜ⇒ act))
      ktd)

-- (2) … but no `forward (var eq) run` can: nothing reaches `s`.
no-edge-into-s : ∀ {H α} → ¬ (H -< α >-> s)
no-edge-into-s {0F} gr with step⇒listed gr
... | here ()
... | there ()
no-edge-into-s {1F} gr with step⇒listed gr
... | here ()
... | there ()
-- `ended` has no edges.
no-edge-into-s {2F} gr with step⇒listed gr
... | ()

reaches-s→≡ : ∀ {H} → H -[¬ ⁅ A ⁆ ]->* s → H ≡ s
reaches-s→≡ ε = refl
reaches-s→≡ {H} ((_ , gr , _) ◅ run) with reaches-s→≡ run
... | refl = ⊥-elim (no-edge-into-s {H = H} gr)

-- `K ≁ s`, decided at the graph level (`bisim?`), which does not mention
-- `wb`.
K≁s : ¬ (K ~ s)
K≁s K~s = notBisim (Equivalence.from (bisimulationCorrect G) K~s)
  where
  notBisim : Bisimilar G K s → ⊥
  notBisim ()

no-unskip-var : ¬ (∃[ H ] (K ~ H) × (H -[¬ ⁅ A ⁆ ]->* s))
no-unskip-var (H , K~H , tr) with reaches-s→≡ tr
... | refl = K≁s K~H
