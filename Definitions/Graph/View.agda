{-# OPTIONS --guardedness #-}

-- The local view of a block, as a graph: at `s`, the outsiders' edges, and
-- `Ps`'s non-internal edges at every `u` its internal edges reach from `s`.
-- Its steps are the view's (`view⇒`, `view⇐`).

open import Data.Bool using (true)
open import Utils.Bits using () renaming (_∈?_ to _∈ˢ?_)
open import Data.List using (List; _++_; filter; concatMap; allFin)
open import Data.List.Membership.Propositional
  using (find; lose) renaming (_∈_ to _∈L_)
open import Data.List.Membership.Propositional.Properties
  using ( ∈-filter⁺; ∈-filter⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻
        ; ∈-concatMap⁺; ∈-concatMap⁻; ∈-allFin )
open import Data.Nat using (ℕ; suc)
open import Data.Product using (∃-syntax; _,_; _×_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; tabulate)
import Data.Vec as Vec
import Data.Vec.Properties as VecP
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; subst)
open import Relation.Nullary using (Dec; ¬_; ¬?)
open import Relation.Nullary.Decidable using (_×?_)

import Definitions.View as View

module Definitions.Graph.View (N : ℕ) where

  open import Definitions.Common N
  open import Definitions.Actions N
  open import Definitions.Graph.Core N
  open import Definitions.Graph.Reachability N

  module _ (G : Graph) (Ps : PartSet) where

    private
      n = size G
      module V = View (graphTheory G)

    -- `Ps` takes part, not internally.
    External : Action → Set
    External α = ¬ V.Internal Ps α × Ps ∈αˢ α

    external? : ∀ α → Dec (External α)
    external? α = ¬? (V.internal? Ps α) ×? (Ps ∈αˢ? α)

    -- ══════════════════════════════════════════════════════════════════
    --  `Ps`'s internal edges, and what they reach
    -- ══════════════════════════════════════════════════════════════════

    Gτ : Graph
    Gτ =
      graph n (Vec.map (filter (λ e → V.internal? Ps (proj₁ e))) (outgoing G))

    edgeτ⇒ :
      ∀ {s α t} → _-<_>->_ {Gτ} s α t
      → _-<_>->_ {G} s α t × V.Internal Ps α
    edgeτ⇒ {s} gr
      with ∈-filter⁻ (λ e → V.internal? Ps (proj₁ e))
             (subst (_ ∈L_) (VecP.lookup-map s _ (outgoing G))
                (step⇒listed gr))
    ... | mem , int = listed⇒step mem , int

    ⇒edgeτ :
      ∀ {s α t} → _-<_>->_ {G} s α t → V.Internal Ps α
      → _-<_>->_ {Gτ} s α t
    ⇒edgeτ {s} gr int =
      listed⇒step
        (subst (_ ∈L_) (sym (VecP.lookup-map s _ (outgoing G)))
          (∈-filter⁺ (λ e → V.internal? Ps (proj₁ e)) (step⇒listed gr) int))

    path⇒τs :
      ∀ {s t k} → PathVia Gτ (λ _ → true) s t k
      → Star (V._-τ->_ Ps) s t
    path⇒τs path/nil = ε
    path⇒τs (path/cons _ gr rest) =
      let gr′ , int = edgeτ⇒ gr in (_ , gr′ , int) ◅ path⇒τs rest

    τs⇒path :
      ∀ {s t} → Star (V._-τ->_ Ps) s t
      → ∃[ k ] PathVia Gτ (λ _ → true) s t k
    τs⇒path ε = _ , path/nil
    τs⇒path ((_ , gr , int) ◅ τs) =
      let k , p = τs⇒path τs in suc k , path/cons tt (⇒edgeτ gr int) p

    -- The states `Ps`'s internal steps reach from `s`.
    closure : State G → List (State G)
    closure s =
      filter (_∈ˢ? reachVia Gτ (λ _ → true) s) (allFin n)

    closure⇒ : ∀ {s u} → u ∈L closure s → Star (V._-τ->_ Ps) s u
    closure⇒ {s} {u} mem =
      let _ , bit =
            ∈-filter⁻ (_∈ˢ? reachVia Gτ (λ _ → true) s) {xs = allFin n} mem
          _ , p = reachVia-sound Gτ _ s bit
      in path⇒τs p

    ⇒closure : ∀ {s u} → Star (V._-τ->_ Ps) s u → u ∈L closure s
    ⇒closure {s} {u} τs =
      let _ , p = τs⇒path τs
      in ∈-filter⁺ (_∈ˢ? reachVia Gτ (λ _ → true) s)
           (∈-allFin u) (reachVia-complete Gτ _ s p)

    -- ══════════════════════════════════════════════════════════════════
    --  The view graph
    -- ══════════════════════════════════════════════════════════════════

    idleOut : State G → List (Edge n)
    idleOut s = filter (λ e → Ps ∉αˢ? proj₁ e) (edges G s)

    ownOut : State G → List (Edge n)
    ownOut u = filter (λ e → external? (proj₁ e)) (edges G u)

    viewOut : State G → List (Edge n)
    viewOut s = idleOut s ++ concatMap ownOut (closure s)

    viewGraph : Graph
    viewGraph = graph n (tabulate viewOut)

    private
      out≡ : ∀ s → edges viewGraph s ≡ viewOut s
      out≡ s = VecP.lookup∘tabulate viewOut s

    view⇒ :
      ∀ {s α t} → _-<_>->_ {viewGraph} s α t → V._-<_>->ᵛ_ Ps s α t
    view⇒ {s} gr
      with ∈-++⁻ (idleOut s) (subst (_ ∈L_) (out≡ s) (step⇒listed gr))
    ... | inj₁ mem =
      let mem′ , idle = ∈-filter⁻ (λ e → Ps ∉αˢ? proj₁ e) mem
      in inj₁ (idle , listed⇒step mem′)
    ... | inj₂ mem =
      let u , u∈ , memᵤ = find (∈-concatMap⁻ ownOut mem)
          mem′ , ¬int , own = ∈-filter⁻ (λ e → external? (proj₁ e)) memᵤ
      in inj₂ (¬int , own , u , closure⇒ u∈ , listed⇒step mem′)

    view⇐ :
      ∀ {s α t} → V._-<_>->ᵛ_ Ps s α t → _-<_>->_ {viewGraph} s α t
    view⇐ {s} (inj₁ (idle , gr)) =
      listed⇒step
        (subst (_ ∈L_) (sym (out≡ s))
          (∈-++⁺ˡ (∈-filter⁺ (λ e → Ps ∉αˢ? proj₁ e) (step⇒listed gr) idle)))
    view⇐ {s} (inj₂ (¬int , own , u , τs , gr)) =
      listed⇒step
        (subst (_ ∈L_) (sym (out≡ s))
          (∈-++⁺ʳ (idleOut s)
            (∈-concatMap⁺ ownOut
              (lose (⇒closure τs)
                (∈-filter⁺ (λ e → external? (proj₁ e)) (step⇒listed gr)
                  (¬int , own))))))
