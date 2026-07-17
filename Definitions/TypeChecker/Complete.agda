{-# OPTIONS --guardedness #-}

-- Theorem A: a `prod` skip tree whose main leaves lie in a `~`-closed set
-- `L` witnesses the semantic-skip predicate `SemSkipP L P s` — the
-- tree-to-semantics direction of the skip characterisation, together with
-- its `~`-transport pack (T1–T6).  Used by the completeness proof in
-- `Definitions/TypeChecker/Completeness.agda` (its converse, semantics-to-
-- tree, is `SkipSem.theoremB` in `Core.agda`, used by soundness).
--
-- This module imports `Definitions.TypeChecker.Core` and `Safety.Skip`/
-- `Safety.Head` (for the `~`-transport / main-leaf machinery Theorem A
-- needs).  It is kept as its own file, separate from `Core`, purely for
-- that reason: `Safety.Skip`/`Safety.Head` only import the narrow
-- `Definitions.Typing`, not the `Definitions` aggregator, so there is no
-- cycle.

open import Data.Bool using (true; T)
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
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Definitions.Behav using (BTheory; WellBehaved)
open import Definitions.Expr using (Sort)
open import Definitions.TypeChecker.Core
import Definitions.Typing as Typing

import Safety.Skip
import Safety.Head

module Definitions.TypeChecker.Complete (N : ℕ) where

  open Processes N
  open import LTS.Core N
  open import LTS.Action N
  open import LTS.Reachability N
    using (PathVia; path/nil; path/cons; PathViaP; pathP/nil; pathP/cons)
  open import LTS.Decision N using (wellBehaved?)
  open import LTS.Algebra N
    using (RootedGraph; underlying; initial; OpenGraph; compile)

  module GraphComplete
    (G : Graph)
    (wb : WellBehaved (graphTheory G))
    where

    open GraphChecker G wb
    open Typing.MPST wb hiding (_,_)
    module SK = Safety.Skip {N} {graphTheory G} wb
    module SH = Safety.Head {N} {graphTheory G} wb

    -- ── §3.5 Theorem A, part 1: main leaves + the spine lemma (S1) ──
    --
    --  `Definitions.Typing.MainLeaf td D` (already in scope via `open
    --  Typing.MPST wb`) witnesses that the skip tree `D` contains a
    --  `skip/main` leaf typed by the derivation `td`.  Unlike a hand-rolled
    --  state-only witness, this already carries the leaf's typing derivation,
    --  so `completeLeaf` (Phase C, below) needs no second walk to recover it.

    --  A `prod` skip tree reaches a `skip/main` leaf: following each
    --  `skip/step`'s chosen `prod` child strictly descends the finite tree.
    --  Returns the leaf state ℓ, its typing derivation, an (unfiltered) path
    --  `s → ℓ`, and a `MainLeaf` witness.  (`skip/cycle` cannot occur: it is
    --  `nonprod`.)  The `with … in eq` recovers `ktd gr ≡ (prod , d)`, which
    --  the plain `with` drops, so the child `d` can be re-attached to `ktd gr`.
    spine :
      ∀ {γ δ ξ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {Ξ : Vec (State G) ξ} {P} {Pr : Proc γ δ} {s}
      → (D : Γ & Δ & Ξ ⊢skip[ prod ] P ◂ Pr ∶ s)
      → ∃[ ℓ ] Σ[ td ∈ Γ & Δ ⊢p P ◂ Pr ∶ ℓ ]
          (∃[ n ] PathVia G (λ _ → true) s ℓ n) × MainLeaf td D
    spine (skip/main {G = ℓ} leaf) = ℓ , leaf , (zero , path/nil) , main/here
    spine {Γ = Γ} {Δ} {Ξ} {P} {Pr} {s}
          (skip/step {G' = s'} gr na ktd prf) = go (ktd gr) refl
      where
        go : (kg : ∃[ m ] Γ & Δ & (s ∷ Ξ) ⊢skip[ m ] P ◂ Pr ∶ s')
           → ktd gr ≡ kg
           → ∃[ ℓ ] Σ[ td ∈ Γ & Δ ⊢p P ◂ Pr ∶ ℓ ]
               (∃[ n ] PathVia G (λ _ → true) s ℓ n)
             × MainLeaf td (skip/step gr na ktd prf)
        go (prod , d) eq =
          let ℓ , td , (n , path′) , hml = spine d
          in ℓ , td , (suc n , path/cons _ gr path′)
               , main/step gr (subst (λ z → MainLeaf td (proj₂ z)) (sym eq) hml)
        go (nonprod , d) eq with trans (sym prf) (cong proj₁ eq)
        ... | ()

    -- ── §3.5 Theorem A, part 2: the AncL invariant + inactivity ──
    --
    --  `AncL L Ξ` records, for every visited state `lookup Ξ X`, a `prod` skip
    --  tree for it over the shorter tail `dropSuc X Ξ`, TOGETHER WITH a proof
    --  that all its main leaves land in `L`.  The walk maintains this so a
    --  `skip/cycle` back-edge to `lookup Ξ X` is discharged by transporting
    --  that ancestor's derivation — and its leaf coverage — to the cycle
    --  target (via `weakenTo` + `skip-td/bisim` + `mainLeaf-bisim`).
    AncL :
      ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
        (P : Part) (Pr : Proc γ δ) (L : State G → Set)
      → ∀ {ξ} → Vec (State G) ξ → Set
    AncL Γ Δ P Pr L []       = ⊤
    AncL Γ Δ P Pr L (r ∷ Ξ) =
      (Σ[ D ∈ Γ & Δ & Ξ ⊢skip[ prod ] P ◂ Pr ∶ r ]
         (∀ {ℓ} {td : Γ & Δ ⊢p P ◂ Pr ∶ ℓ} → MainLeaf td D → L ℓ))
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
    -- `~`-related main leaf of the original tree; `MainLeaf` already carries
    -- the leaf's typing derivation, so we recover it (`td`) directly rather
    -- than only the state it types.
    mainLeaf-bisim :
      ∀ {γ δ ξ m} {Γ : Vec Sort γ} {Δ Δ′ : Vec (State G) δ}
        {Ξ Ξ′ : Vec (State G) ξ} {P} {Pr : Proc γ δ} {H H′}
        {G′ : State G} {td′ : Γ & Δ′ ⊢p P ◂ Pr ∶ G′}
      → (D : Γ & Δ & Ξ ⊢skip[ m ] P ◂ Pr ∶ H)
      → (Δ~ : Δ ~ᵛ Δ′) (Ξ~ : Ξ ~ᵛ Ξ′) (H~ : H ~ H′)
      → MainLeaf td′ (SK.skip-td/bisim Δ~ Ξ~ H~ D)
      → ∃[ ℓ ] Σ[ td ∈ Γ & Δ ⊢p P ◂ Pr ∶ ℓ ] MainLeaf td D × ℓ ~ G′
    mainLeaf-bisim (skip/main leaf) Δ~ Ξ~ H~ main/here =
      _ , leaf , main/here , H~
    mainLeaf-bisim (skip/step gr na ktd prf) Δ~ Ξ~ H~ (main/step gr″ inner)
      with mainLeaf-bisim (ktd (~R→ H~ gr″) .proj₂) Δ~ (~ᵛ/∷ H~ Ξ~)
             (~R→~ H~ gr″) inner
    ... | ℓ , td , inner₀ , ℓ~ℓ′ =
      ℓ , td , main/step (~R→ H~ gr″) inner₀ , ℓ~ℓ′
    mainLeaf-bisim (skip/cycle eq) Δ~ Ξ~ H~ ()

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

    -- `Safety.Head.mainLeaf/weaken-visited` already proves that
    -- `skip/weaken-visited` preserves main leaves (it maps `skip/main td ↦
    -- skip/main td` and recurses structurally through `skip/step`; its Δ was
    -- generalised from `[]` to arbitrary, since the proof never used Δ), so a
    -- main leaf of the front-inserted tree comes from the same derivation's
    -- main leaf of the original — no need to re-derive that here.  This just
    -- iterates it over the whole prefix that `weakenTo` inserts.
    hml-weakenTo :
      ∀ {γ δ ξ m} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {P} {Pr : Proc γ δ} {H} {ℓ} {td : Γ & Δ ⊢p P ◂ Pr ∶ ℓ}
        (X : Fin ξ) (Ξ : Vec (State G) ξ)
        (D : Γ & Δ & dropSuc X Ξ ⊢skip[ m ] P ◂ Pr ∶ H)
      → MainLeaf td (weakenTo X Ξ D) → MainLeaf td D
    hml-weakenTo F.zero    (y ∷ Ξ′) D hml =
      SH.mainLeaf/weaken-visited {Ξ′ = []} D hml
    hml-weakenTo (F.suc X) (y ∷ Ξ′) D hml =
      hml-weakenTo X Ξ′ D
        (SH.mainLeaf/weaken-visited {Ξ′ = []} (weakenTo X Ξ′ D) hml)

    -- positional lookup into the `AncL` invariant
    ancLookup :
      ∀ {γ δ ξ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {P} {Pr : Proc γ δ} {L : State G → Set}
        {Ξ : Vec (State G) ξ}
      → AncL Γ Δ P Pr L Ξ → (X : Fin ξ)
      → Σ[ D ∈ Γ & Δ & dropSuc X Ξ ⊢skip[ prod ] P ◂ Pr ∶ lookup Ξ X ]
          (∀ {ℓ} {td : Γ & Δ ⊢p P ◂ Pr ∶ ℓ} → MainLeaf td D → L ℓ)
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
        (lc : ∀ {ℓ} {td : Γ & Δ ⊢p P ◂ Pr ∶ ℓ} → MainLeaf td D → L ℓ)
        {t} (path : PathViaP G (λ u → ¬ L u) r t) (¬Lt : ¬ L t)
      → (P not-active-in t) × ReachLP L t
    walk Γ Δ P Pr L Lcl (skip/main leaf) anc lc pathP/nil ¬Lt =
      ⊥-elim (¬Lt (lc main/here))
    walk Γ Δ P Pr L Lcl (skip/step gr na ktd prf) anc lc pathP/nil ¬Lt
      with spine (skip/step gr na ktd prf)
    ... | ℓ , td , (n , p) , hml = na , ℓ , (n , p) , lc hml
    walk Γ Δ P Pr L Lcl (skip/main leaf) anc lc (pathP/cons ¬Lr gr_β rest) ¬Lt =
      ⊥-elim (¬Lr (lc main/here))
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
            (λ {ℓ} {td} hml →
               lc (main/step gr_β
                     (subst (λ z → MainLeaf td (proj₂ z)) (sym eq) hml)))
            rest ¬Lt
        go (nonprod , skip/cycle {X = X} cyc-eq) eq =
          walk Γ Δ P Pr L Lcl D_u anc′ lc_u rest ¬Lt
          where
            aL   = ancLookup anc′ X
            D_a  = proj₁ aL
            lc_a = proj₂ aL
            D_w  = weakenTo X (r ∷ Ξ) D_a
            D_u  = SK.skip-td/bisim ~ᵛ-refl ~ᵛ-refl cyc-eq D_w
            lc_u : ∀ {ℓ} {td : Γ & Δ ⊢p P ◂ Pr ∶ ℓ} → MainLeaf td D_u → L ℓ
            lc_u hml′ =
              Lcl (lc_a (hml-weakenTo X (r ∷ Ξ) D_a
                           (proj₁ (proj₂ (proj₂ hb)))))
                  (proj₂ (proj₂ (proj₂ hb)))
              where hb = mainLeaf-bisim D_w ~ᵛ-refl ~ᵛ-refl cyc-eq hml′

    -- Theorem A: a `prod` skip tree whose main leaves lie in a `~`-closed `L`
    -- witnesses the semantic-skip predicate `SemSkipP L P s`.
    theoremA :
      ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ} {P} {Pr : Proc γ δ} {s}
        (L : State G → Set)
        (Lcl : ∀ {u u′} → L u → u ~ u′ → L u′)
        (std : Γ & Δ & [] ⊢skip[ prod ] P ◂ Pr ∶ s)
      → (∀ {ℓ} {td : Γ & Δ ⊢p P ◂ Pr ∶ ℓ} → MainLeaf td std → L ℓ)
      → SemSkipP L P s
    theoremA L Lcl std lc t (path , ¬Lt) =
      walk _ _ _ _ L Lcl std tt lc path ¬Lt
