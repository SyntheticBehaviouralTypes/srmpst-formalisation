{-# OPTIONS --guardedness #-}

-- §5, §3.5, §6 of decidable.md: the cost measure, Theorem A (necessity of the
-- semantic skip characterisation), and the completeness theorem that turns the
-- fuelled algorithmic judgment `Alg` into a genuine `Dec` of the declarative
-- typing judgment.
--
-- This module lives OUTSIDE the `Definitions` aggregator on purpose: it imports
-- both `Definitions.TypeChecker` (for `Alg`/`alg-sound`/…) and `Safety.Skip`
-- (for the `~`-transport machinery Theorem A needs).  Since the aggregator does
-- not re-export it, `Safety.* → Definitions → TypeChecker` stays acyclic.

open import Data.Bool using (true)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _≤_; _<_; s≤s)
open import Data.Nat.Properties
  using (m≤m⊔n; n≤m⊔n; m≤n+m; ≤-trans; <-trans; <⇒≤; n<1+n; ≤-refl)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Data.Vec using (Vec; lookup; _∷_; [])
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Definitions.Behav using (BTheory; WellBehaved)
open import Definitions.Expr using (Sort)
open import Definitions.TypeChecker
import Definitions.Typing as Typing

import Safety.Skip

module Definitions.TypeChecker.Complete (N : ℕ) where

  open Processes N
  open import LTS.Core N
  open import LTS.Action N
  open import LTS.Reachability N using (PathVia; path/nil; path/cons)

  module GraphComplete
    (G : Graph)
    (wb : WellBehaved (graphTheory G))
    where

    open GraphChecker G wb
    open Typing.MPST wb hiding (_,_)
    module SK = Safety.Skip {N} {graphTheory G} wb

    -- ── §5: a cost measure on declarative derivations ──
    --
    --  Structural recursion on the derivation fails for completeness because
    --  the skip/unskip rounds replace subderivations by *other* derivations,
    --  so §6 recurses on `cost` instead.  Function-shaped premises (`t/recv`'s
    --  continuations, `skip/step`'s `ktd`) are combined via `max` through the
    --  edge list: each outgoing edge contributes the cost of the premise
    --  instantiated at `listed⇒step`.  Using `max` (rather than sum) makes the
    --  measure independent of edge-list multiplicity, hence `~`-invariant (C2).

    -- fold over `xs`, applying `f` at membership in the *original* list.
    -- `max` (not sum): its value depends only on the *set* of `f`-results, so
    -- `cost` becomes invariant under `~`-transport of a derivation (bisimilar
    -- states have corresponding transition *sets*), which is what C2 (§6) needs.
    maxWithMem :
      ∀ {A : Set} (xs : List A) → (∀ x → x ∈ xs → ℕ) → ℕ
    maxWithMem []       f = 0
    maxWithMem (x ∷ xs) f =
      f x (here refl) ⊔ maxWithMem xs (λ y mem → f y (there mem))

    traceLen : ∀ {H P H′} → H -[¬ P ]->* H′ → ℕ
    traceLen skip/refl          = 0
    traceLen (skip/step _ _ tr) = suc (traceLen tr)

    mutual
      cost :
        ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
          {P} {Pr : Proc γ δ} {s}
        → Γ & Δ ⊢p P ◂ Pr ∶ s → ℕ
      cost (t/send _ _ td)  = suc (cost td)
      cost {s = s} (t/recv {P = P} {Q = Q} {I = I} gr conts) =
        suc (maxWithMem (edges G s) recvEdge)
        where
          -- cost contributed by one edge: the branch's cost if the edge is a
          -- matching receive, 0 otherwise.  `conts` stays the clause's pattern
          -- variable so `conts (…)` is seen as a subderivation for termination.
          recvEdge : ∀ e → e ∈ edges G s → ℕ
          recvEdge (α , t) mem with matchRecv? P Q I α
          ... | yes (j , U , refl) =
            cost (conts (listed⇒step {G = G} mem))
          ... | no _ = 0
      cost (t/skip std)     = suc (costSkip std)
      cost (t/unskip tr td) = suc (traceLen tr + cost td)
      cost (t/if _ ttd ftd) = suc (cost ttd ⊔ cost ftd)
      cost (t/rec _ td)     = suc (cost td)
      cost (t/var _)        = 1
      cost (t/end _)        = 1

      costSkip :
        ∀ {γ δ ξ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
          {Ξ : Vec (State G) ξ} {m} {P} {Pr : Proc γ δ} {s}
        → Γ & Δ & Ξ ⊢skip[ m ] P ◂ Pr ∶ s → ℕ
      costSkip (skip/main leaf)   = suc (cost leaf)
      costSkip {s = s} (skip/step gr na ktd _) =
        suc (maxWithMem (edges G s)
              (λ { (β , t) mem →
                   suc (costSkip (proj₂ (ktd (listed⇒step {G = G} mem)))) }))
      costSkip (skip/cycle _)     = 1

    -- ── §5: cost lemmas (C1) ──

    -- every element of a `maxWithMem` is bounded by the whole max (the key
    -- fact behind "a subderivation reached through a canonical edge is cheaper")
    maxWithMem-lb :
      ∀ {A : Set} (xs : List A) (f : ∀ x → x ∈ xs → ℕ)
        {e} (mem : e ∈ xs)
      → f e mem ≤ maxWithMem xs f
    maxWithMem-lb (x ∷ xs) f (here refl) =
      m≤m⊔n (f x (here refl)) _         -- head ≤ head ⊔ rest
    maxWithMem-lb (x ∷ xs) f (there mem) =
      ≤-trans
        (maxWithMem-lb xs (λ y m → f y (there m)) mem)
        (n≤m⊔n (f x (here refl))
               (maxWithMem xs (λ y m → f y (there m))))  -- rest ≤ head ⊔ rest

    -- C1, structural: the immediate subderivation of an unskip is cheaper
    cost-unskip< :
      ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {P} {Pr : Proc γ δ} {G′ s}
      → (tr : G′ -[¬ P ]->* s) (td : Γ & Δ ⊢p P ◂ Pr ∶ G′)
      → cost td < cost (t/unskip tr td)
    cost-unskip< tr td = s≤s (m≤n+m _ (traceLen tr))

    -- C1, skip: the skip subtree of a `t/skip` node is cheaper
    costSkip<skip :
      ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {P} {Pr : Proc γ δ} {s}
      → (std : Γ & Δ & [] ⊢skip[ prod ] P ◂ Pr ∶ s)
      → costSkip std < cost (t/skip std)
    costSkip<skip std = n<1+n (costSkip std)

    -- C1, skip leaf: a `skip/main` leaf's derivation is cheaper than the leaf
    cost-main<skip :
      ∀ {γ δ ξ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {Ξ : Vec (State G) ξ} {P} {Pr : Proc γ δ} {s}
      → (leaf : Γ & Δ ⊢p P ◂ Pr ∶ s)
      → cost leaf < costSkip {Ξ = Ξ} (skip/main leaf)
    cost-main<skip leaf = n<1+n (cost leaf)

    -- C1, skip step child: a `skip/step` child reached through a canonical edge
    -- is cheaper than the whole `skip/step` node
    costSkip-child< :
      ∀ {γ δ ξ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {Ξ : Vec (State G) ξ} {P} {Pr : Proc γ δ} {s α s′}
        (gr : BTheory._-<_>->_ (graphTheory G) s α s′)
        (na : P not-active-in s)
        (ktd : ∀ {G″ β} → BTheory._-<_>->_ (graphTheory G) s β G″
             → ∃[ m ] Γ & Δ & (s ∷ Ξ) ⊢skip[ m ] P ◂ Pr ∶ G″)
        (prf : proj₁ (ktd gr) ≡ prod)
        {β t} (mem : (β , t) ∈ edges G s)
      → costSkip (proj₂ (ktd (listed⇒step {G = G} mem)))
          < costSkip (skip/step gr na ktd prf)
    costSkip-child< {s = s} gr na ktd prf mem =
      s≤s (<⇒≤
        (maxWithMem-lb (edges G s)
          (λ { (β , t) m →
               suc (costSkip (proj₂ (ktd (listed⇒step {G = G} m)))) })
          mem))

    -- ── §3.5 Theorem A, part 1: main leaves + the spine lemma (S1) ──
    --
    --  `HasMainLeaf D ℓ` witnesses that the skip tree `D` contains a
    --  `skip/main` leaf at state `ℓ` (reached by descending through the
    --  `skip/step` `ktd` function-premises).  This is the interface the walk
    --  uses to conclude `L ℓ` from the "main leaves ⊆ L" hypothesis.
    data HasMainLeaf
      {γ δ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P} {Pr : Proc γ δ}
      : ∀ {ξ} {Ξ : Vec (State G) ξ} {m} {s}
      → (Γ & Δ & Ξ ⊢skip[ m ] P ◂ Pr ∶ s) → State G → Set where
      hml/main :
        ∀ {ξ} {Ξ : Vec (State G) ξ} {u}
          (leaf : Γ & Δ ⊢p P ◂ Pr ∶ u)
        → HasMainLeaf {Ξ = Ξ} (skip/main leaf) u
      hml/step :
        ∀ {ξ} {Ξ : Vec (State G) ξ} {s α s'}
          {gr : BTheory._-<_>->_ (graphTheory G) s α s'}
          {na : P not-active-in s}
          {ktd : ∀ {G″ β} → BTheory._-<_>->_ (graphTheory G) s β G″
               → ∃[ m ] Γ & Δ & (s ∷ Ξ) ⊢skip[ m ] P ◂ Pr ∶ G″}
          {prf : proj₁ (ktd gr) ≡ prod}
          {β G″} (gr' : BTheory._-<_>->_ (graphTheory G) s β G″) {u}
        → HasMainLeaf (proj₂ (ktd gr')) u
        → HasMainLeaf (skip/step gr na ktd prf) u

    --  A `prod` skip tree reaches a `skip/main` leaf: following each
    --  `skip/step`'s chosen `prod` child strictly descends the finite tree.
    --  Returns the leaf state ℓ, an (unfiltered) path `s → ℓ`, and a
    --  `HasMainLeaf` witness.  (`skip/cycle` cannot occur: it is `nonprod`.)
    --  The `with … in eq` recovers `ktd gr ≡ (prod , d)`, which the plain
    --  `with` drops, so the child `d` can be re-attached to `ktd gr`.
    spine :
      ∀ {γ δ ξ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {Ξ : Vec (State G) ξ} {P} {Pr : Proc γ δ} {s}
      → (D : Γ & Δ & Ξ ⊢skip[ prod ] P ◂ Pr ∶ s)
      → ∃[ ℓ ] (∃[ n ] PathVia G (λ _ → true) s ℓ n) × HasMainLeaf D ℓ
    spine (skip/main {G = ℓ} leaf) = ℓ , (zero , path/nil) , hml/main leaf
    spine {Γ = Γ} {Δ} {Ξ} {P} {Pr} {s}
          (skip/step {G' = s'} gr na ktd prf) = go (ktd gr) refl
      where
        go : (kg : ∃[ m ] Γ & Δ & (s ∷ Ξ) ⊢skip[ m ] P ◂ Pr ∶ s')
           → ktd gr ≡ kg
           → ∃[ ℓ ] (∃[ n ] PathVia G (λ _ → true) s ℓ n)
                  × HasMainLeaf (skip/step gr na ktd prf) ℓ
        go (prod , d) eq =
          let ℓ , (n , path′) , hml = spine d
          in ℓ , (suc n , path/cons _ gr path′)
               , hml/step gr (subst (λ z → HasMainLeaf (proj₂ z) ℓ) (sym eq) hml)
        go (nonprod , d) eq with trans (sym prf) (cong proj₁ eq)
        ... | ()

    -- ── §3.5 Theorem A, part 2: the Anc invariant + inactivity ──
    --
    --  `Anc Ξ` records that every visited state `lu Ξ X` is an internal
    --  (`skip/step`, hence `prod`) node of the enclosing derivation, whose own
    --  subderivation lives over the *shorter* tail `drop (suc X) Ξ`.  This is
    --  the invariant the walk maintains so that a `skip/cycle` back-edge to
    --  `lu Ξ X` can be discharged by transporting that ancestor's derivation.
    Anc :
      ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
        (P : Part) (Pr : Proc γ δ)
      → ∀ {ξ} → Vec (State G) ξ → Set
    Anc Γ Δ P Pr []       = ⊤
    Anc Γ Δ P Pr (r ∷ Ξ) =
      (Γ & Δ & Ξ ⊢skip[ prod ] P ◂ Pr ∶ r) × Anc Γ Δ P Pr Ξ

    -- The easy half of the walk's base case: a `prod` skip tree at a state that
    -- is *not* in the leaf set `L` must be a `skip/step` (a `skip/main` would
    -- witness `t`'s typability, hence `t ∈ L`), and its `na` field is exactly
    -- the inactivity `SemSkipP` demands.
    skip-na :
      ∀ {γ δ ξ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {Ξ : Vec (State G) ξ} {P} {Pr : Proc γ δ} {t}
        {L : State G → Set}
      → Γ & Δ & Ξ ⊢skip[ prod ] P ◂ Pr ∶ t
      → ((Γ & Δ ⊢p P ◂ Pr ∶ t) → L t)     -- any typing of `t` lands in `L`
      → ¬ L t
      → P not-active-in t
    skip-na (skip/main leaf)        cover ¬Lt = ⊥-elim (¬Lt (cover leaf))
    skip-na (skip/step gr na ktd _) _     _   = na
