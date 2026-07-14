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
open import Data.Fin using (Fin)
import Data.Fin as F
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _⊔_; _≤_; _<_; s≤s)
open import Data.Nat.Properties
  using ( m≤m⊔n; n≤m⊔n; m≤m+n; m≤n+m; ≤-trans; <-trans; <⇒≤; n<1+n; n≤1+n
        ; ≤-refl; *-monoʳ-≤)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (Vec; lookup; _∷_; []; _++_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Definitions.Behav using (BTheory; WellBehaved)
open import Definitions.Expr using (Sort)
open import Definitions.TypeChecker
import Definitions.Typing as Typing

import Safety.Skip
import Definitions.TypeChecker.Saturate

module Definitions.TypeChecker.Complete (N : ℕ) where

  open Processes N
  open import LTS.Core N
  open import LTS.Action N
  open import LTS.Reachability N
    using (PathVia; path/nil; path/cons; PathViaP; pathP/nil; pathP/cons)
  open import LTS.Decision N using (wellBehaved?)
  open import LTS.Algebra N using (RootedGraph; underlying; initial)

  module GraphComplete
    (G : Graph)
    (wb : WellBehaved (graphTheory G))
    where

    open GraphChecker G wb
    open Typing.MPST wb hiding (_,_)
    module SK = Safety.Skip {N} {graphTheory G} wb
    open Definitions.TypeChecker.Saturate.GraphSaturate N G wb
      using (F; sat; branchFuel-lb)

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

    -- ── §3.5 Theorem A, part 2: the AncL invariant + inactivity ──
    --
    --  `AncL L Ξ` records, for every visited state `lookup Ξ X`, a `prod` skip
    --  tree for it over the shorter tail `dropSuc X Ξ`, TOGETHER WITH a proof
    --  that all its main leaves land in `L`.  The walk maintains this so a
    --  `skip/cycle` back-edge to `lookup Ξ X` is discharged by transporting
    --  that ancestor's derivation — and its leaf coverage — to the cycle
    --  target (via `weakenTo` + `skip-td/bisim` + `hml-bisim`).
    AncL :
      ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
        (P : Part) (Pr : Proc γ δ) (L : State G → Set)
      → ∀ {ξ} → Vec (State G) ξ → Set
    AncL Γ Δ P Pr L []       = ⊤
    AncL Γ Δ P Pr L (r ∷ Ξ) =
      (Σ[ D ∈ Γ & Δ & Ξ ⊢skip[ prod ] P ◂ Pr ∶ r ]
         (∀ {ℓ} → HasMainLeaf D ℓ → L ℓ))
      × AncL Γ Δ P Pr L Ξ

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

    -- ════════════════════════════════════════════════════════════════
    --  Phase T:  `~`-transport pack
    --
    --  T1–T4 make `SemSkipP` invariant under `~` for a `~`-closed leaf set
    --  `L` (used by Phase C's `t/skip` case); T5–T6 relate the main leaves
    --  and the visited vector of a `~`-transported / prefix-weakened skip
    --  tree (used by Phase A's walk).
    -- ════════════════════════════════════════════════════════════════

    -- T1: pull a `¬L`-filtered path back along `~` (right-to-left).
    pathViaP-pull :
      ∀ {L : State G → Set} {s s′ t′}
      → (Lcl : ∀ {u u′} → L u → u ~ u′ → L u′)
      → s ~ s′
      → PathViaP G (λ u → ¬ L u) s′ t′
      → ∃[ t ] PathViaP G (λ u → ¬ L u) s t × t ~ t′
    pathViaP-pull Lcl s~s′ pathP/nil = _ , pathP/nil , s~s′
    pathViaP-pull Lcl s~s′ (pathP/cons ¬Ls′ gr′ rest)
      with pathViaP-pull Lcl (~R→~ s~s′ gr′) rest
    ... | t , path , t~t′ =
      t , pathP/cons (λ Ls → ¬Ls′ (Lcl Ls s~s′)) (~R→ s~s′ gr′) path , t~t′

    -- T2: push an unfiltered path forward along `~` (left-to-right).
    pathVia-push :
      ∀ {t t′ ℓ n}
      → t ~ t′
      → PathVia G (λ _ → true) t ℓ n
      → ∃[ ℓ′ ] PathVia G (λ _ → true) t′ ℓ′ n × ℓ ~ ℓ′
    pathVia-push t~t′ path/nil = _ , path/nil , t~t′
    pathVia-push t~t′ (path/cons _ gr rest)
      with pathVia-push (~L→~ t~t′ gr) rest
    ... | ℓ′ , path′ , ℓ~ℓ′ =
      ℓ′ , path/cons _ (~L→ t~t′ gr) path′ , ℓ~ℓ′

    -- T3: inactivity travels along `~`.
    na-~ : ∀ {t t′ P} → t ~ t′ → P not-active-in t → P not-active-in t′
    na-~ t~t′ na gr′ = na (~R→ t~t′ gr′)

    -- T4: the composite — `SemSkipP` is `~`-invariant for a `~`-closed `L`.
    semSkipP-bisim :
      ∀ {L : State G → Set} {P s s′}
      → (Lcl : ∀ {u u′} → L u → u ~ u′ → L u′)
      → s ~ s′
      → SemSkipP L P s → SemSkipP L P s′
    semSkipP-bisim Lcl s~s′ sem t′ (path′ , ¬Lt′)
      with pathViaP-pull Lcl s~s′ path′
    ... | t , path , t~t′
      with sem t (path , λ Lt → ¬Lt′ (Lcl Lt t~t′))
    ... | na , ℓ , (n , p) , Lℓ
      with pathVia-push t~t′ p
    ... | ℓ′ , p′ , ℓ~ℓ′ =
      na-~ t~t′ na , ℓ′ , (n , p′) , Lcl Lℓ ℓ~ℓ′

    -- T5: a main leaf of a `~`-transported skip tree comes from a
    -- `~`-related main leaf of the original tree.
    hml-bisim :
      ∀ {γ δ ξ m} {Γ : Vec Sort γ} {Δ Δ′ : Vec (State G) δ}
        {Ξ Ξ′ : Vec (State G) ξ} {P} {Pr : Proc γ δ} {H H′ ℓ′}
      → (D : Γ & Δ & Ξ ⊢skip[ m ] P ◂ Pr ∶ H)
      → (Δ~ : Δ ~ᵛ Δ′) (Ξ~ : Ξ ~ᵛ Ξ′) (H~ : H ~ H′)
      → HasMainLeaf (SK.skip-td/bisim Δ~ Ξ~ H~ D) ℓ′
      → ∃[ ℓ ] HasMainLeaf D ℓ × ℓ ~ ℓ′
    hml-bisim (skip/main leaf) Δ~ Ξ~ H~ (hml/main _) =
      _ , hml/main leaf , H~
    hml-bisim (skip/step gr na ktd prf) Δ~ Ξ~ H~ (hml/step gr″ inner)
      with hml-bisim (ktd (~R→ H~ gr″) .proj₂) Δ~ (~ᵛ/∷ H~ Ξ~)
             (~R→~ H~ gr″) inner
    ... | ℓ , inner₀ , ℓ~ℓ′ = ℓ , hml/step (~R→ H~ gr″) inner₀ , ℓ~ℓ′
    hml-bisim (skip/cycle eq) Δ~ Ξ~ H~ ()

    -- T6: weaken the visited vector by a whole prefix, by iterating
    -- `Safety.Skip`'s single-front-insertion lemma.  `dropSuc X Ξ` is the
    -- tail of `Ξ` strictly after position `X`.
    dropSuc : ∀ {A : Set} {n} (X : Fin n) → Vec A n → Vec A (n ∸ suc (F.toℕ X))
    dropSuc F.zero    (y ∷ Ξ′) = Ξ′
    dropSuc (F.suc X) (y ∷ Ξ′) = dropSuc X Ξ′

    weakenTo :
      ∀ {γ δ ξ m} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {P} {Pr : Proc γ δ} {H}
      → (X : Fin ξ) (Ξ : Vec (State G) ξ)
      → Γ & Δ & dropSuc X Ξ ⊢skip[ m ] P ◂ Pr ∶ H
      → Γ & Δ & Ξ           ⊢skip[ m ] P ◂ Pr ∶ H
    weakenTo F.zero    (y ∷ Ξ′) D = SK.skip/weaken-visited {Ξ′ = []} D
    weakenTo (F.suc X) (y ∷ Ξ′) D =
      SK.skip/weaken-visited {Ξ′ = []} (weakenTo X Ξ′ D)

    -- `skip/weaken-visited` preserves main leaves (it maps `skip/main td ↦
    -- skip/main td` and recurses structurally through `skip/step`), so a main
    -- leaf of the front-inserted tree comes from the same-state main leaf of
    -- the original.  General over the prefix `Ξ′` because the recursion grows
    -- it.
    hml-wv :
      ∀ {γ δ ξ ξ′ m} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {P} {Pr : Proc γ δ} {t₀} {w : State G} {ℓ}
        {Ξ : Vec (State G) ξ} {Ξ′ : Vec (State G) ξ′}
        (D : Γ & Δ & (Ξ′ ++ Ξ) ⊢skip[ m ] P ◂ Pr ∶ t₀)
      → HasMainLeaf (SK.skip/weaken-visited {H = w} {Ξ = Ξ} {Ξ′ = Ξ′} D) ℓ
      → HasMainLeaf D ℓ
    hml-wv (skip/main leaf) (hml/main _) = hml/main leaf
    hml-wv {Ξ′ = Ξ′} (skip/step gr na ktd prf) (hml/step gr″ inner) =
      hml/step gr″ (hml-wv {Ξ′ = _ ∷ Ξ′} (ktd gr″ .proj₂) inner)
    hml-wv (skip/cycle eq) ()

    -- iterate `hml-wv` over the whole prefix that `weakenTo` inserts
    hml-weakenTo :
      ∀ {γ δ ξ m} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {P} {Pr : Proc γ δ} {H} {ℓ}
        (X : Fin ξ) (Ξ : Vec (State G) ξ)
        (D : Γ & Δ & dropSuc X Ξ ⊢skip[ m ] P ◂ Pr ∶ H)
      → HasMainLeaf (weakenTo X Ξ D) ℓ → HasMainLeaf D ℓ
    hml-weakenTo F.zero    (y ∷ Ξ′) D hml = hml-wv {Ξ′ = []} D hml
    hml-weakenTo (F.suc X) (y ∷ Ξ′) D hml =
      hml-weakenTo X Ξ′ D (hml-wv {Ξ′ = []} (weakenTo X Ξ′ D) hml)

    -- positional lookup into the `AncL` invariant
    ancLookup :
      ∀ {γ δ ξ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {P} {Pr : Proc γ δ} {L : State G → Set}
        {Ξ : Vec (State G) ξ}
      → AncL Γ Δ P Pr L Ξ → (X : Fin ξ)
      → Σ[ D ∈ Γ & Δ & dropSuc X Ξ ⊢skip[ prod ] P ◂ Pr ∶ lookup Ξ X ]
          (∀ {ℓ} → HasMainLeaf D ℓ → L ℓ)
    ancLookup {Ξ = r ∷ Ξ} (DL , _)   F.zero    = DL
    ancLookup {Ξ = r ∷ Ξ} (_  , anc) (F.suc X) = ancLookup anc X

    -- ── §3.5 Theorem A: the walk ──
    --
    --  Structural induction on the `PathViaP` argument: the path shrinks at
    --  every step; the current `prod` skip tree `D` is carried DATA (a
    --  `skip/cycle` back-edge is discharged by replacing `D` with a
    --  transported ancestor, never by recursing on a bigger tree).  Abstract
    --  in the leaf set `L` (only assumed `~`-closed via `Lcl`); Phase C
    --  instantiates it.
    walk :
      ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part) (Pr : Proc γ δ)
        (L : State G → Set)
        (Lcl : ∀ {u u′} → L u → u ~ u′ → L u′)
        {ξ} {Ξ : Vec (State G) ξ} {r}
        (D : Γ & Δ & Ξ ⊢skip[ prod ] P ◂ Pr ∶ r)
        (anc : AncL Γ Δ P Pr L Ξ)
        (lc : ∀ {ℓ} → HasMainLeaf D ℓ → L ℓ)
        {t} (path : PathViaP G (λ u → ¬ L u) r t) (¬Lt : ¬ L t)
      → (P not-active-in t) × ReachLP L t
    walk Γ Δ P Pr L Lcl (skip/main leaf) anc lc pathP/nil ¬Lt =
      ⊥-elim (¬Lt (lc (hml/main leaf)))
    walk Γ Δ P Pr L Lcl (skip/step gr na ktd prf) anc lc pathP/nil ¬Lt
      with spine (skip/step gr na ktd prf)
    ... | ℓ , (n , p) , hml = na , ℓ , (n , p) , lc hml
    walk Γ Δ P Pr L Lcl (skip/main leaf) anc lc (pathP/cons ¬Lr gr_β rest) ¬Lt =
      ⊥-elim (¬Lr (lc (hml/main leaf)))
    walk Γ Δ P Pr L Lcl {Ξ = Ξ} {r = r} (skip/step gr na ktd prf) anc lc
         {t = t} (pathP/cons {u = u} ¬Lr gr_β rest) ¬Lt =
      go (ktd gr_β) refl
      where
        anc′ : AncL Γ Δ P Pr L (r ∷ Ξ)
        anc′ = (skip/step gr na ktd prf , lc) , anc
        go : (kg : ∃[ m ] Γ & Δ & (r ∷ Ξ) ⊢skip[ m ] P ◂ Pr ∶ u)
           → ktd gr_β ≡ kg
           → (P not-active-in t) × ReachLP L t
        go (prod , child) eq =
          walk Γ Δ P Pr L Lcl child anc′
            (λ {ℓ} hml →
               lc (hml/step gr_β
                     (subst (λ z → HasMainLeaf (proj₂ z) ℓ) (sym eq) hml)))
            rest ¬Lt
        go (nonprod , skip/cycle {X = X} cyc-eq) eq =
          walk Γ Δ P Pr L Lcl D_u anc′ lc_u rest ¬Lt
          where
            aL   = ancLookup anc′ X
            D_a  = proj₁ aL
            lc_a = proj₂ aL
            D_w  = weakenTo X (r ∷ Ξ) D_a
            D_u  = SK.skip-td/bisim ~ᵛ-refl ~ᵛ-refl cyc-eq D_w
            lc_u : ∀ {ℓ} → HasMainLeaf D_u ℓ → L ℓ
            lc_u hml′ =
              Lcl (lc_a (hml-weakenTo X (r ∷ Ξ) D_a (proj₁ (proj₂ hb))))
                  (proj₂ (proj₂ hb))
              where hb = hml-bisim D_w ~ᵛ-refl ~ᵛ-refl cyc-eq hml′

    -- Theorem A: a `prod` skip tree whose main leaves lie in a `~`-closed `L`
    -- witnesses the semantic-skip predicate `SemSkipP L P s`.
    theoremA :
      ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P} {Pr : Proc γ δ} {s}
        (L : State G → Set)
        (Lcl : ∀ {u u′} → L u → u ~ u′ → L u′)
        (std : Γ & Δ & [] ⊢skip[ prod ] P ◂ Pr ∶ s)
      → (∀ {ℓ} → HasMainLeaf std ℓ → L ℓ)
      → SemSkipP L P s
    theoremA L Lcl std lc t (path , ¬Lt) =
      walk _ _ _ _ L Lcl std tt lc path ¬Lt

    -- ════════════════════════════════════════════════════════════════
    --  Phase C:  completeness up to `~`
    --
    --  `complete` mirrors `td/bisim` (`Safety/Skip.agda`) constructor by
    --  constructor, but lands in the *algorithmic* judgment `Alg (F Pr)`
    --  rather than a declarative one.  Quantifying over `~` (the `Δ~`/`s~`
    --  arguments) means the induction hypothesis already covers every
    --  `~`-image, so the `t/skip` leaf set `L t = ∃ ℓ. HasMainLeaf std ℓ × ℓ~t`
    --  is `~`-closed by `~trans`.  Every case injects `Alg (suc (F Pr))`-shaped
    --  data and re-compresses with `sat` (Phase S); per-case fuel is never
    --  tracked beyond the mechanical `F`-subterm bounds below.
    -- ════════════════════════════════════════════════════════════════

    -- `F` of a subterm is ≤ `F` of the compound process (RHS is the normal
    -- form of `F` of the relevant constructor).
    F-suc : ∀ {γ δ} (Pr : Proc γ δ)
          → F Pr ≤ suc (size G) * suc (processFuel Pr)
    F-suc Pr = *-monoʳ-≤ (suc (size G)) (n≤1+n (processFuel Pr))

    F-if₁ : ∀ {γ δ} (Pr₁ Pr₂ : Proc γ δ)
          → F Pr₁ ≤ suc (size G) * suc (processFuel Pr₁ + processFuel Pr₂)
    F-if₁ Pr₁ Pr₂ =
      *-monoʳ-≤ (suc (size G))
        (≤-trans (m≤m+n (processFuel Pr₁) (processFuel Pr₂)) (n≤1+n _))

    F-if₂ : ∀ {γ δ} (Pr₁ Pr₂ : Proc γ δ)
          → F Pr₂ ≤ suc (size G) * suc (processFuel Pr₁ + processFuel Pr₂)
    F-if₂ Pr₁ Pr₂ =
      *-monoʳ-≤ (suc (size G))
        (≤-trans (m≤n+m (processFuel Pr₂) (processFuel Pr₁)) (n≤1+n _))

    F-recv : ∀ {γ δ I} (Br : Vec (Proc (suc γ) δ) (suc I)) (j : Fin (suc I))
           → F (lookup Br j) ≤ suc (size G) * suc (branchesFuel Br)
    F-recv Br j =
      *-monoʳ-≤ (suc (size G)) (≤-trans (branchFuel-lb Br j) (n≤1+n _))

    -- one saturation step: `Alg (suc (F Pr)) ⊆ Alg (F Pr)`.  `Pr` is explicit
    -- because for the `v`/`∅`/`rec`/… cases the injected value does not mention
    -- the leaf predicate, so `Pr` is not otherwise recoverable from it.
    intoF :
      ∀ {γ δ} {Γ : Vec Sort γ} {Δ′ : Vec (State G) δ} {P} (Pr : Proc γ δ) {s′}
      → Alg (suc (F Pr)) Γ Δ′ P Pr s′ → Alg (F Pr) Γ Δ′ P Pr s′
    intoF Pr x = sat _ _ _ Pr _ (suc (F Pr)) x

    -- fold a `-[¬ P ]->*` trace into a chain of `Alg` unskip steps, saturating
    -- after each so no fuel arithmetic ever appears
    pred-fold :
      ∀ {γ δ} {Γ : Vec Sort γ} {Δ′ : Vec (State G) δ} {P} {Pr : Proc γ δ} {a b}
      → a -[¬ P ]->* b
      → Alg (F Pr) Γ Δ′ P Pr a → Alg (F Pr) Γ Δ′ P Pr b
    pred-fold skip/refl                      alg = alg
    pred-fold {Pr = PP} (skip/step gr P∉ tr) alg =
      pred-fold tr
        (intoF PP (inj₂ (inj₁ (_ , (_ , step⇒listed {G = G} gr , P∉) , alg))))

    mutual
      complete :
        ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P} {Pr : Proc γ δ} {s}
        → (D : Γ & Δ ⊢p P ◂ Pr ∶ s)
        → ∀ {Δ′ : Vec (State G) δ} {s′} → Δ ~ᵛ Δ′ → s ~ s′
        → Alg (F Pr) Γ Δ′ P Pr s′
      complete {Pr = PP} (t/send gr etd td) Δ~Δ′ s~s′ =
        intoF PP (inj₁ ( _ , _ , etd , ~L→ s~s′ gr
                       , alg-mono (F-suc _) (complete td Δ~Δ′ (~L→~ s~s′ gr))))
      complete {Pr = PP} (t/recv {Br = Br} gr conts) Δ~Δ′ s~s′ =
        intoF PP (inj₁
          ( (_ , _ , _ , step⇒listed {G = G} (~L→ s~s′ gr))
          , All.tabulate (λ {e} mem {j} {U} eq →
              let gr′ = subst (λ β → BTheory._-<_>->_ (graphTheory G) _ β _)
                              eq (listed⇒step {G = G} mem)
              in alg-mono (F-recv Br j)
                   (complete (conts (~R→ s~s′ gr′)) Δ~Δ′ (~R→~ s~s′ gr′)))))
      complete {Pr = PP} (t/skip std) Δ~Δ′ s~s′ =
        intoF PP (inj₂ (inj₂
          (semSkipP-mono
            (λ { (ℓ , hml , ℓ~u) → completeLeaf std hml Δ~Δ′ ℓ~u })
            (semSkipP-bisim Lcl s~s′ (theoremA _ Lcl std lc)))))
        where
          Lcl : ∀ {u u′}
              → (∃[ ℓ ] HasMainLeaf std ℓ × ℓ ~ u) → u ~ u′
              → ∃[ ℓ ] HasMainLeaf std ℓ × ℓ ~ u′
          Lcl (ℓ , hml , ℓ~u) u~u′ = ℓ , hml , ~trans ℓ~u u~u′
          lc : ∀ {ℓ} → HasMainLeaf std ℓ → ∃[ ℓ₀ ] HasMainLeaf std ℓ₀ × ℓ₀ ~ ℓ
          lc {ℓ} hml = ℓ , hml , ~refl
      complete (t/unskip tr td) Δ~Δ′ s~s′
        with SK.skip/bisim s~s′ tr
      ... | H₀ , G~H₀ , tr′ = pred-fold tr′ (complete td Δ~Δ′ G~H₀)
      complete {Pr = PP} (t/if etd ttd ftd) Δ~Δ′ s~s′ =
        intoF PP (inj₁ ( etd
                       , alg-mono (F-if₁ _ _) (complete ttd Δ~Δ′ s~s′)
                       , alg-mono (F-if₂ _ _) (complete ftd Δ~Δ′ s~s′)))
      complete {Pr = PP} (t/rec mg td) Δ~Δ′ s~s′ =
        intoF PP (inj₁ ( mg
                       , alg-mono (F-suc _)
                           (complete td (~ᵛ/∷ s~s′ Δ~Δ′) s~s′)))
      complete {Pr = PP} (t/var eq) Δ~Δ′ s~s′ =
        intoF PP (inj₁ (~trans (lookup/~ᵛ Δ~Δ′ _ eq) s~s′))
      complete {Pr = PP} (t/end done) Δ~Δ′ s~s′ =
        intoF PP (inj₁ (λ P∈ → done (∈~ (~sym s~s′) P∈)))

      -- extract-and-complete a main leaf, up to `~`
      completeLeaf :
        ∀ {γ δ ξ m} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
          {Ξ : Vec (State G) ξ} {P} {Pr : Proc γ δ} {r}
        → (D : Γ & Δ & Ξ ⊢skip[ m ] P ◂ Pr ∶ r)
        → ∀ {ℓ} → HasMainLeaf D ℓ
        → ∀ {Δ′ : Vec (State G) δ} {t} → Δ ~ᵛ Δ′ → ℓ ~ t
        → Alg (F Pr) Γ Δ′ P Pr t
      completeLeaf (skip/main leaf) (hml/main _) Δ~Δ′ ℓ~t =
        complete leaf Δ~Δ′ ℓ~t
      completeLeaf (skip/step gr na ktd prf) (hml/step gr′ hml′) Δ~Δ′ ℓ~t =
        completeLeaf (ktd gr′ .proj₂) hml′ Δ~Δ′ ℓ~t
      completeLeaf (skip/cycle eq) ()

    complete₀ :
      ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P} {Pr : Proc γ δ} {s}
      → (D : Γ & Δ ⊢p P ◂ Pr ∶ s) → Alg (F Pr) Γ Δ P Pr s
    complete₀ D = complete D ~ᵛ-refl ~refl

    -- ── Phase F, step 1: the process decision procedure ──
    --
    --  Soundness (`alg-sound`) and completeness (`complete₀`) close the loop:
    --  `Alg (F Pr)` is decidable (`checkWithFuelD`), it *implies* the judgment
    --  (yes-branch), and — by saturation to fuel `F Pr` — it is *implied by* the
    --  judgment (no-branch, `complete₀`).  Hence the judgment is decidable.
    checkD :
      ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
        (P : Common.Part) (Pr : Syntax.Proc γ δ) (s : State G)
      → Dec (Γ & Δ ⊢p P ◂ Pr ∶ s)
    checkD Γ Δ P Pr s with checkWithFuelD (F Pr) Γ Δ P Pr s
    ... | yes a = yes (alg-sound (F Pr) a)
    ... | no ¬a = no (λ td → ¬a (complete₀ td))

    checkClosedD :
      ∀ {γ} (Γ : Vec Sort γ) (P : Common.Part) (Pr : Syntax.Proc γ 0)
        (s : State G)
      → Dec (Γ & [] ⊢p P ◂ Pr ∶ s)
    checkClosedD Γ P Pr s = checkD Γ [] P Pr s

    -- ── Phase F, step 2: the session decision procedure ──
    --
    --  `⊢s M ∶ s` is a finite conjunction over the participants `Fin N`, so it
    --  is decided by deciding each projection and combining with `allDec`.
    private
      allDec :
        ∀ {n} {A : Fin n → Set}
        → (∀ i → Dec (A i)) → Dec (∀ i → A i)
      allDec {zero}  d = yes (λ ())
      allDec {suc n} d with d F.zero | allDec (λ i → d (F.suc i))
      ... | yes a  | yes rest = yes λ { F.zero → a ; (F.suc i) → rest i }
      ... | no ¬a  | _        = no  λ f → ¬a (f F.zero)
      ... | _      | no ¬rest = no  λ f → ¬rest (λ i → f (F.suc i))

    checkSessionD : (M : Syntax.Session) (s : State G) → Dec (⊢s M ∶ s)
    checkSessionD M s = allDec (λ P → checkClosedD [] P (Syntax._[_]s M P) s)

  -- ── Phase F, step 3a: `WellBehaved`-irrelevance of the typing judgment ──
  --
  --  The typing and skip judgments never inspect the `WellBehaved` witness —
  --  every premise lives at the `BTheory` level.  So a derivation under one
  --  witness re-wraps, constructor for constructor, into one under any other.
  --  This lets the bundled `CheckedProcess`/`CheckedSession` (whose witness is
  --  an existential field) be *decided* from the witness `wellBehaved?` picks.
  module WbIrr
    (G : Graph)
    (wb wb′ : WellBehaved (graphTheory G))
    where
    open Typing.MPST wb hiding (_,_)
    private module Td = Typing.MPST wb′

    -- `Mode`/`MessageGuarded` are `MPST`-parameterised, so the two witnesses
    -- give distinct (but constructor-identical) copies.
    mode-conv : Mode → Td.Mode
    mode-conv prod    = Td.prod
    mode-conv nonprod = Td.nonprod

    mg-conv : ∀ {γ δ} {Pr : Proc γ δ} → MessageGuarded Pr → Td.MessageGuarded Pr
    mg-conv mg/send        = Td.mg/send
    mg-conv mg/recv        = Td.mg/recv
    mg-conv (mg/if mgt mgf) = Td.mg/if (mg-conv mgt) (mg-conv mgf)

    mutual
      typing-wb-irrelevant :
        ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {PPr} {s}
        → Γ & Δ ⊢p PPr ∶ s → Td._&_⊢p_∶_ Γ Δ PPr s
      typing-wb-irrelevant (t/send gr etd td) =
        Td.t/send gr etd (typing-wb-irrelevant td)
      typing-wb-irrelevant (t/recv gr conts) =
        Td.t/recv gr (λ gr′ → typing-wb-irrelevant (conts gr′))
      typing-wb-irrelevant (t/skip std) =
        Td.t/skip (skip-wb-irrelevant std)
      typing-wb-irrelevant (t/unskip tr td) =
        Td.t/unskip tr (typing-wb-irrelevant td)
      typing-wb-irrelevant (t/if etd ttd ftd) =
        Td.t/if etd (typing-wb-irrelevant ttd) (typing-wb-irrelevant ftd)
      typing-wb-irrelevant (t/rec mg td) =
        Td.t/rec (mg-conv mg) (typing-wb-irrelevant td)
      typing-wb-irrelevant (t/var eq)   = Td.t/var eq
      typing-wb-irrelevant (t/end done) = Td.t/end done

      skip-wb-irrelevant :
        ∀ {γ δ ξ m} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
          {Ξ : Vec (State G) ξ} {PPr} {sG}
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip[ m ] PPr ∶ sG
        → Td._&_&_⊢skip[_]_∶_ Γ Δ Ξ (mode-conv m) PPr sG
      skip-wb-irrelevant (skip/main leaf) =
        Td.skip/main (typing-wb-irrelevant leaf)
      skip-wb-irrelevant (skip/step gr na ktd prf) =
        Td.skip/step gr na
          (λ gr′ → _ , skip-wb-irrelevant (ktd gr′ .proj₂)) (cong mode-conv prf)
      skip-wb-irrelevant (skip/cycle eq) = Td.skip/cycle eq

  -- ── Phase F, step 3b: the bundled decision procedures ──
  checkProcessD :
    ∀ {γ}
    → (G : Graph) (Γ : Vec Sort γ) (P : Common.Part)
      (Pr : Syntax.Proc γ 0) (s : State G)
    → Dec (CheckedProcess G Γ P Pr s)
  checkProcessD G Γ P Pr s with wellBehaved? G
  ... | no ¬wb = no λ { (checkedProcess wb _) → ¬wb wb }
  ... | yes wb with GraphComplete.checkD G wb Γ [] P Pr s
  ...   | yes td = yes (checkedProcess wb td)
  ...   | no ¬td =
            no λ { (checkedProcess wb′ td′) →
                     ¬td (WbIrr.typing-wb-irrelevant G wb′ wb td′) }

  checkRootedProcessD :
    ∀ {γ}
    → (R : RootedGraph) (Γ : Vec Sort γ) (P : Common.Part)
      (Pr : Syntax.Proc γ 0)
    → Dec (CheckedProcess (underlying R) Γ P Pr (initial R))
  checkRootedProcessD R Γ P Pr =
    checkProcessD (underlying R) Γ P Pr (initial R)

  checkSessionWD :
    (G : Graph) (M : Syntax.Session) (s : State G)
    → Dec (CheckedSession G M s)
  checkSessionWD G M s with wellBehaved? G
  ... | no ¬wb = no λ { (checkedSession wb _) → ¬wb wb }
  ... | yes wb with GraphComplete.checkSessionD G wb M s
  ...   | yes d = yes (checkedSession wb d)
  ...   | no ¬d =
            no λ { (checkedSession wb′ d′) →
                     ¬d (λ P → WbIrr.typing-wb-irrelevant G wb′ wb (d′ P)) }

  checkRootedSessionD :
    (R : RootedGraph) (M : Syntax.Session)
    → Dec (CheckedSession (underlying R) M (initial R))
  checkRootedSessionD R M =
    checkSessionWD (underlying R) M (initial R)
