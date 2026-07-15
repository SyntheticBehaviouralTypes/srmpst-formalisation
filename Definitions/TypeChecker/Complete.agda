{-# OPTIONS --guardedness #-}

-- §5, §3.5, §6 of decidable.md: the cost measure, Theorem A (necessity of the
-- semantic skip characterisation), and the completeness theorem that turns the
-- fuelled algorithmic judgment `Alg` into a genuine `Dec` of the declarative
-- typing judgment.
--
-- This module imports `Definitions.TypeChecker.Core` (for `Alg`/`alg-sound`/…)
-- and `Safety.Skip`/`Safety.Head` (for the `~`-transport / main-leaf machinery
-- Theorem A needs). It is kept as its own file, separate from `Core`, purely
-- for that reason: `Safety.Skip`/`Safety.Head` only import the narrow
-- `Definitions.Typing`, not the `Definitions` aggregator, so there is no cycle
-- — `Definitions/TypeChecker.agda` re-exports this module's two entry points
-- (`typecheck`/`typecheckSession`, plus the `WBGraph` subtype and its smart
-- constructor `buildG`) via an anonymous parameterised module, so the
-- participant count `N` surfaces as an ordinary implicit argument rather
-- than a module parameter the caller has to apply.

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
import Definitions.TypeChecker.Saturate

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
    open Definitions.TypeChecker.Saturate.GraphSaturate N G wb
      using (F; sat; branchFuel-lb)

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

    -- ════════════════════════════════════════════════════════════════
    --  Phase C:  completeness up to `~`
    --
    --  `complete` mirrors `td/bisim` (`Safety/Skip.agda`) constructor by
    --  constructor, but lands in the *algorithmic* judgment `Alg (F Pr)`
    --  rather than a declarative one.  Quantifying over `~` (the `Δ~`/`s~`
    --  arguments) means the induction hypothesis already covers every
    --  `~`-image, so the `t/skip` leaf set
    --  `L t = ∃ ℓ. Σ[ td ] MainLeaf td std × ℓ~t` is `~`-closed by `~trans`.
    --  Every case injects `Alg (suc (F Pr))`-shaped
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
            (λ { (ℓ , td , hml , ℓ~u) → completeLeaf std hml Δ~Δ′ ℓ~u })
            (semSkipP-bisim Lcl s~s′ (theoremA _ Lcl std lc)))))
        where
          Lcl : ∀ {u u′}
              → (∃[ ℓ ] Σ[ td ∈ _ ] MainLeaf td std × ℓ ~ u)
              → u ~ u′
              → ∃[ ℓ ] Σ[ td ∈ _ ] MainLeaf td std × ℓ ~ u′
          Lcl (ℓ , td , hml , ℓ~u) u~u′ = ℓ , td , hml , ~trans ℓ~u u~u′
          lc : ∀ {ℓ} {td} → MainLeaf {G′ = ℓ} td std
             → ∃[ ℓ₀ ] Σ[ td₀ ∈ _ ] MainLeaf td₀ std × ℓ₀ ~ ℓ
          lc {ℓ} {td} hml = ℓ , td , hml , ~refl
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

      -- extract-and-complete a main leaf, up to `~`.  Recurses on the same
      -- `D`/`MainLeaf` shape `spine` uses (structural on the `MainLeaf`
      -- witness) rather than short-circuiting straight to the leaf's own
      -- derivation `td`, since that's what the termination checker needs to
      -- see: `td` itself isn't a syntactic subterm of `D`, but `hml′` is a
      -- subterm of `hml` at every step.
      completeLeaf :
        ∀ {γ δ ξ m} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
          {Ξ : Vec (State G) ξ} {P} {Pr : Proc γ δ} {r}
        → (D : Γ & Δ & Ξ ⊢skip[ m ] P ◂ Pr ∶ r)
        → ∀ {ℓ} {td : Γ & Δ ⊢p P ◂ Pr ∶ ℓ} → MainLeaf td D
        → ∀ {Δ′ : Vec (State G) δ} {t} → Δ ~ᵛ Δ′ → ℓ ~ t
        → Alg (F Pr) Γ Δ′ P Pr t
      completeLeaf (skip/main leaf) main/here Δ~Δ′ ℓ~t =
        complete leaf Δ~Δ′ ℓ~t
      completeLeaf (skip/step gr na ktd prf) (main/step gr′ hml′) Δ~Δ′ ℓ~t =
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

  -- ── The public interface ──
  --
  --  `WBGraph`: a *predicate subtype* of well-behaved rooted graphs, built on
  --  the decision procedure `wellBehaved?` via the standard `T ⌊ _ ⌋` idiom
  --  (irrelevant Boolean-reflected proof) rather than bundling a `WellBehaved`
  --  witness as data — `wb-of` recovers the witness with `toWitness`. Since
  --  every caller now supplies a `WBGraph`, there is no longer a second
  --  "graph of unknown behaviour" witness floating around to reconcile, so
  --  the earlier `WellBehaved`-irrelevance machinery (`WbIrr`) is unneeded.
  --
  --  `buildG`: the smart constructor — compiling an `OpenGraph 0` (the
  --  ergonomic graph-description DSL of `LTS.Algebra`) and pairing the
  --  result with the well-behavedness proof is all `WBGraph` asks for, and
  --  for a concrete/closed graph Agda solves that proof on its own
  --  (`T ⌊ _ ⌋` at a `yes` reduces to `⊤`, whose unique inhabitant `tt` is
  --  filled in by unification), so callers can just write `buildG OG`.
  --
  --  `typecheck` / `typecheckSession`: mirror `Γ & Δ ⊢p P ◂ Pr ∶ G`
  --  (`Γ = Δ = []`, `G` supplied by the rooted graph's `initial` state;
  --  participant before process, matching `P ◂ Pr`). `typecheckSession` has
  --  no participant argument — a session already covers every participant,
  --  `⊢s M ∶ G`.

  WBGraph : Set
  WBGraph = Σ[ R ∈ RootedGraph ] T ⌊ wellBehaved? (underlying R) ⌋

  wb-of : (WR : WBGraph) → WellBehaved (graphTheory (underlying (proj₁ WR)))
  wb-of WR = toWitness (proj₂ WR)

  buildG :
    (OG : OpenGraph 0) → {p : T ⌊ wellBehaved? (underlying (compile OG)) ⌋}
    → WBGraph
  buildG OG {p} = compile OG , p

  typecheck :
    (WR : WBGraph) (P : Common.Part) (Pr : Syntax.Proc 0 0)
    → Dec (ProcessTyping (underlying (proj₁ WR)) (wb-of WR) [] P Pr
             (initial (proj₁ WR)))
  typecheck WR P Pr =
    GraphComplete.checkClosedD (underlying (proj₁ WR)) (wb-of WR) [] P Pr
      (initial (proj₁ WR))

  typecheckSession :
    (WR : WBGraph) (M : Syntax.Session)
    → Dec (SessionTyping (underlying (proj₁ WR)) (wb-of WR) M
             (initial (proj₁ WR)))
  typecheckSession WR M =
    GraphComplete.checkSessionD (underlying (proj₁ WR)) (wb-of WR) M
      (initial (proj₁ WR))
