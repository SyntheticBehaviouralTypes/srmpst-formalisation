{-# OPTIONS --guardedness #-}

-- TODO.md §7 step 4/4b.  This file was the COUNTEREXAMPLE that killed the
-- ν-based `Wait`; it is now the REGRESSION TEST that the μ-based one is right.
--
-- A concrete `BTheory` with all eight `WellBehaved` axioms discharged, in
-- which no `⊢skip` derivation exists at `g 0`.  The old `Wait` (a ν over
-- `Pred Behav`) held at `g 0` anyway, which made `Wait ⟹ ⊢skip`, hence
-- `⊢a ⟹ ⊢p`, false.  `WaitV`'s visited set fixes that, and `ce/no-wait`
-- below is the check: `Wait` now fails at `g 0` too.
--
-- Keep this file.  It is the only thing in the tree that would catch a
-- "simplification" of `WaitV` back to a fixpoint over states alone.
--
-- The theory is an infinite chain
--
--     g 0 --a 0--> g 1 --a 1--> g 2 --a 2--> ⋯          (all Q⟶R, P-free)
--      |            |            |
--     b 0          b 1          b 2                     (all Q⟶R, P-free)
--      v            v            v
--      e -----------p----------> z                      (P⟶Q: where P acts)
--
-- `𝒮` is "`P` is immediately active", so `e ∈ 𝒮` and no `g i ∈ 𝒮`.  It is
-- `~`-closed (`𝒮/closed`), so this is not an artefact of dropping §5.2.
--
-- No finite `⊢skip` tree exists at `g 0`: `skip/main` needs `𝒮 (g i)`, false;
-- `skip/cycle` needs a bisimilar ancestor, and the `g i` are pairwise
-- NON-bisimilar; so `skip/step` would have to descend forever.  The old `Wait`
-- accepted it coinductively — every `g i` steps, the `e` branch is an
-- `𝒮`-leaf, and the `g (suc i)` branch was a guard leaf, justified by
-- `P ∈T (g i)` via `b i` then `p`.  That is deferring forever on a promise the
-- environment never has to keep.
--
-- What makes them non-bisimilar is the ARITY: at `g i` the branching is over
-- `Fin (suc (suc i))`, so `a i` and `a j` are different actions for `i ≢ j`.
-- Both steps out of `g i` share that arity, which is what `step-arity-det`
-- demands, and both share the comm `Q⟶R`, which is what `recv-overlap`
-- demands and what makes `step-diamond` vacuous.

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (<-trans; n<1+n; <-irrefl; suc-injective)

open import Data.Fin using (Fin; zero; suc; toℕ)

open import Data.Vec using (Vec; []; _∷_) renaming (lookup to lu)

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Empty using (⊥; ⊥-elim)

open import Data.List using (List; []; _∷_)

open import Data.List.Relation.Unary.Any using (Any; here; there)

open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Definitions.Typing

module Tests.WaitNotSkip where

  N : ℕ
  N = 3

  open import Definitions.Common N
  open import Definitions.Actions N
  open import Definitions.Proc N using (Proc; ∅; NProc; _◂_)
  open import Definitions.Expr using (Sort; s/unit)
  open import Data.Fin.Subset using (⁅_⁆)
  open import Data.Maybe using (maybe; just)

  P Q R : Part
  P = zero
  Q = suc zero
  R = suc (suc zero)

  ---------------------------------------------------------------------------
  -- States and actions
  ---------------------------------------------------------------------------

  data St : Set where
    g : ℕ → St
    e : St
    z : St

  -- Arity `suc i` at `g i`; label 0 continues the chain, label 1 exits to `e`.
  -- `N` is concrete, so `ev` of these actions computes.
  aA : ℕ → Action
  aA i = Q ⟶ ⁅ R ⁆ # (zero {suc i} < s/unit >)

  bA : ℕ → Action
  bA i = Q ⟶ ⁅ R ⁆ # (suc (zero {i}) < s/unit >)

  pA : Action
  pA = P ⟶ ⁅ Q ⁆ # (zero {0} < s/unit >)

  data _⇒_⇒_ : St → Action → St → Set where
    sA : ∀ i → g i ⇒ aA i ⇒ g (suc i)
    sB : ∀ i → g i ⇒ bA i ⇒ e
    sP : e ⇒ pA ⇒ z

  -- Inversion without index unification, so nothing below depends on Agda
  -- inverting the defined functions `aA`/`bA`.
  stepInv :
    ∀ {X α Y}
    → X ⇒ α ⇒ Y
    → (∃[ i ] (X ≡ g i) × (α ≡ aA i) × (Y ≡ g (suc i)))
    ⊎ (∃[ i ] (X ≡ g i) × (α ≡ bA i) × (Y ≡ e))
    ⊎ ((X ≡ e) × (α ≡ pA) × (Y ≡ z))
  stepInv (sA i) = inj₁ (i , refl , refl , refl)
  stepInv (sB i) = inj₂ (inj₁ (i , refl , refl , refl))
  stepInv sP     = inj₂ (inj₂ (refl , refl , refl))

  -- Action separation, via first-order projections only (no heterogeneous
  -- equality): `Q`'s arity, `Q`'s label-as-ℕ, and whether `P` acts.

  aA-inj : ∀ {i j} → aA i ≡ aA j → i ≡ j
  aA-inj eq = suc-injective (cong (λ α → maybe nchoices 0 (ev α Q)) eq)

  aA≢bA : ∀ {i j} → aA i ≡ bA j → ⊥
  aA≢bA eq with cong (λ α → maybe (λ e → toℕ (label e)) 0 (ev α Q)) eq
  ... | ()

  aA≢pA : ∀ {i} → aA i ≡ pA → ⊥
  aA≢pA eq with cong (λ α → ev α P) eq
  ... | ()

  bA≢pA : ∀ {i} → bA i ≡ pA → ⊥
  bA≢pA eq with cong (λ α → ev α P) eq
  ... | ()

  ---------------------------------------------------------------------------
  -- The theory
  ---------------------------------------------------------------------------

  theory : BTheory N
  theory = record { Behav = St ; _-<_>->_ = _⇒_⇒_ }

  open BTheory theory

  -- Bisimilarity on this theory is equality.  Everything bisimulation-shaped
  -- below reduces to this.
  ~⇒≡ : ∀ {X Y} → X ~ Y → X ≡ Y

  ~⇒≡ {g i} X~Y with ~L X~Y (sA i)
  ... | _ , st , _ with stepInv st
  ...   | inj₁ (j , refl , eq , _)        = cong g (aA-inj eq)
  ...   | inj₂ (inj₁ (_ , _ , eq , _))    = ⊥-elim (aA≢bA eq)
  ...   | inj₂ (inj₂ (_ , eq , _))        = ⊥-elim (aA≢pA eq)

  ~⇒≡ {e} X~Y with ~L X~Y sP
  ... | _ , st , _ with stepInv st
  ...   | inj₁ (_ , _ , eq , _)           = ⊥-elim (aA≢pA (sym eq))
  ...   | inj₂ (inj₁ (_ , _ , eq , _))    = ⊥-elim (bA≢pA (sym eq))
  ...   | inj₂ (inj₂ (refl , _ , _))      = refl

  ~⇒≡ {z} {g j} X~Y with ~R X~Y (sA j)
  ... | _ , st , _ with stepInv st
  ...   | inj₁ (_ , () , _ , _)
  ...   | inj₂ (inj₁ (_ , () , _ , _))
  ...   | inj₂ (inj₂ (() , _ , _))

  ~⇒≡ {z} {e} X~Y with ~R X~Y sP
  ... | _ , st , _ with stepInv st
  ...   | inj₁ (_ , () , _ , _)
  ...   | inj₂ (inj₁ (_ , () , _ , _))
  ...   | inj₂ (inj₂ (() , _ , _))

  ~⇒≡ {z} {z} _ = refl

  ---------------------------------------------------------------------------
  -- Well-behavedness: all eight axioms
  ---------------------------------------------------------------------------

  wb : WellBehaved theory
  wb = record
    { recv-overlap           = rovl
    ; step-deterministic     = det
    ; step-sort-det          = sortDet
    ; step-arity-det         = arityDet
    ; no-new-branch/step     = nnb
    ; stepback/~             = sback
    ; step-diamond           = diam
    }
    where
      -- Every pair of steps out of a state shares the comm `Q⟶R` (at `g i`) or
      -- is a single step (at `e`), so this is `refl` throughout: `comm`
      -- computes, and forgets the label.
      rovl :
        ∀ {G α α′ G′ G″ X}
        → G ⇒ α  ⇒ G′
        → G ⇒ α′ ⇒ G″
        → Recv α X
        → X ∈α α′
        → comm α ≡ comm α′
      rovl (sA _) (sA _) _ _ = refl
      rovl (sA _) (sB _) _ _ = refl
      rovl (sB _) (sA _) _ _ = refl
      rovl (sB _) (sB _) _ _ = refl
      rovl sP     sP     _ _ = refl

      det : ∀ {G α G′ G″} → G ⇒ α ⇒ G′ → G ⇒ α ⇒ G″ → G′ ≡ G″
      det (sA _) (sA _) = refl
      det (sB _) (sB _) = refl
      det sP     sP     = refl

      -- Two receive events of the SAME action are the same event.
      same : ∀ {Y c c′} → just ((？ Y) # c) ≡ just ((？ Y) # c′) → c ≡ c′
      same refl = refl

      -- Across `aA`/`bA`, only `R` receives; there the labels differ (sort)
      -- and the arities agree (arity).
      sortDet :
        ∀ {G G′ G″ α α′ Y X I S T}{i : Fin (suc I)}
        → G ⇒ α ⇒ G′
        → G ⇒ α′ ⇒ G″
        → ev α X ≡ just ((？ Y) # i < S >)
        → ev α′ X ≡ just ((？ Y) # i < T >)
        → S ≡ T
      sortDet (sA _) (sA _) eq eq′ =
        cong Choice.sort (same (trans (sym eq) eq′))
      sortDet (sB _) (sB _) eq eq′ =
        cong Choice.sort (same (trans (sym eq) eq′))
      sortDet sP     sP     eq eq′ =
        cong Choice.sort (same (trans (sym eq) eq′))
      sortDet {X = zero}              (sA _) (sB _) () _
      sortDet {X = suc zero}          (sA _) (sB _) () _
      sortDet {X = suc (suc zero)}    (sA _) (sB _) refl ()
      sortDet {X = zero}              (sB _) (sA _) () _
      sortDet {X = suc zero}          (sB _) (sA _) () _
      sortDet {X = suc (suc zero)}    (sB _) (sA _) refl ()

      arityDet :
        ∀ {G G′ G″ α α′ Y X I J S T}{i : Fin (suc I)}{j : Fin (suc J)}
        → G ⇒ α ⇒ G′
        → G ⇒ α′ ⇒ G″
        → ev α X ≡ just ((？ Y) # i < S >)
        → ev α′ X ≡ just ((？ Y) # j < T >)
        → I ≡ J
      arityDet (sA _) (sA _) eq eq′ =
        cong Choice.nchoices (same (trans (sym eq) eq′))
      arityDet (sB _) (sB _) eq eq′ =
        cong Choice.nchoices (same (trans (sym eq) eq′))
      arityDet sP     sP     eq eq′ =
        cong Choice.nchoices (same (trans (sym eq) eq′))
      arityDet {X = zero}             (sA _) (sB _) () _
      arityDet {X = suc zero}         (sA _) (sB _) () _
      arityDet {X = suc (suc zero)}   (sA _) (sB _) refl refl = refl
      arityDet {X = zero}             (sB _) (sA _) () _
      arityDet {X = suc zero}         (sB _) (sA _) () _
      arityDet {X = suc (suc zero)}   (sB _) (sA _) refl refl = refl

      -- Vacuous: `R` receives in every step out of `g i`, so the premise
      -- "`γ`'s receivers are idle in `β`" fails; and `z` has no steps.
      nnb :
        ∀ {G G′ Gᵢ Gⱼ′ β γ γ′}
        → G ⇒ β ⇒ G′
        → (∀ X → Recv γ X → X ∉α β)
        → G  ⇒ γ  ⇒ Gᵢ
        → G′ ⇒ γ′ ⇒ Gⱼ′
        → comm γ′ ≡ comm γ
        → ∃[ Gⱼ ] G ⇒ γ′ ⇒ Gⱼ
      nnb (sA _) idle (sA _) _ _ with idle R (Q , _ , refl)
      ... | ()
      nnb (sA _) idle (sB _) _ _ with idle R (Q , _ , refl)
      ... | ()
      nnb (sB _) idle (sA _) _ _ with idle R (Q , _ , refl)
      ... | ()
      nnb (sB _) idle (sB _) _ _ with idle R (Q , _ , refl)
      ... | ()
      nnb sP     idle sP     () _

      sback :
        ∀ {α G₀ G₁ G₁′}
        → G₁ ~ G₁′
        → G₀ ⇒ α ⇒ G₁
        → ∃[ G₀′ ] (G₀ ~ G₀′) × (G₀′ ⇒ α ⇒ G₁′)
      sback {G₀ = G₀} G₁~ st with ~⇒≡ G₁~
      ... | refl = G₀ , ~refl , st

      -- Vacuous: any two steps out of one state share a receiver, so they are
      -- never independent.
      diam :
        ∀ {G α G₁ α′ G₂}
        → G ⇒ α  ⇒ G₁
        → G ⇒ α′ ⇒ G₂
        → α ⋄ α′
        → ∃[ G′ ] (G₁ ⇒ α′ ⇒ G′) × (G₂ ⇒ α ⇒ G′)
      diam (sA _) (sA _) (_ , d , _) with d R (Q , _ , refl)
      ... | ()
      diam (sA _) (sB _) (_ , d , _) with d R (Q , _ , refl)
      ... | ()
      diam (sB _) (sA _) (_ , d , _) with d R (Q , _ , refl)
      ... | ()
      diam (sB _) (sB _) (_ , d , _) with d R (Q , _ , refl)
      ... | ()
      diam sP     sP     (α≢α , _) = ⊥-elim (α≢α refl)

  open import Definitions.Typing.Alg wb
  open import Definitions.Typing.AlgEquiv wb using (wait⇒skip)
  open MPST wb using (_&_⊢skip_∶_; skip/main; skip/step; skip/cycle)

  ---------------------------------------------------------------------------
  -- The leaf family: "P is immediately active".  `~`-closed.
  ---------------------------------------------------------------------------

  𝒮 : Behavs
  𝒮 s = ∃[ α ] ∃[ t ] (s ⇒ α ⇒ t) × P ∈α α

  𝒮/closed : Closed 𝒮
  𝒮/closed G~H (α , _ , gr , px) =
    α , _ , ~L→ G~H gr , px

  e∈𝒮 : 𝒮 e
  e∈𝒮 = pA , z , sP , (_ , refl)

  g∉𝒮 : ∀ {i} → ¬ 𝒮 (g i)
  g∉𝒮 (_ , _ , sA _ , (_ , ()))
  g∉𝒮 (_ , _ , sB _ , (_ , ()))

  P/na : ∀ {i} → P not-active-in (g i)
  P/na (sA _) = refl
  P/na (sB _) = refl

  P∈T/g : ∀ i → P ∈T (g i)
  P∈T/g i =
    bA i ∷ pA ∷ [] , z , tr/step (sB i) (tr/step sP tr/refl)
    , there (here (_ , refl))

  ---------------------------------------------------------------------------
  -- No `⊢skip` derivation at `g 0`
  ---------------------------------------------------------------------------

  Lf : NProc 0 0 → St → Set
  Lf _ s = 𝒮 s

  Pr : Proc 0 0
  Pr = ∅

  -- The invariant: every visited state is some `g j` with `j` strictly below
  -- the current index.  That is what rules out `skip/cycle`, since `~` is `≡`
  -- here and the chain never repeats.
  Below : ∀ {ξ} → ℕ → Vec St ξ → Set
  Below i Ξ = ∀ X → ∃[ j ] (lu Ξ X ≡ g j) × (j < i)

  below/cons : ∀ {ξ}{Ξ : Vec St ξ}{i} → Below i Ξ → Below (suc i) (g i ∷ Ξ)
  below/cons {i = i} bel zero    = i , refl , n<1+n i
  below/cons {i = i} bel (suc X) with bel X
  ... | j , eq , j<i = j , eq , <-trans j<i (n<1+n i)

  noSkip :
    ∀ {ξ}{Ξ : Vec St ξ}{i}
    → Below i Ξ
    → Lf & Ξ ⊢skip P ◂ Pr ∶ g i
    → ⊥

  noSkip bel (skip/main leaf) =
    g∉𝒮 leaf

  noSkip {i = i} bel (skip/step _ _ ktd) =
    noSkip (below/cons bel) (ktd (sA i))

  noSkip {i = i} bel (skip/cycle {X = X} eq _) with bel X
  ... | j , luEq , j<i =
    <-irrefl (gInj (subst (_~ g i) luEq eq)) j<i
    where
      gInj : ∀ {m n} → g m ~ g n → m ≡ n
      gInj b with ~⇒≡ b
      ... | refl = refl

  ---------------------------------------------------------------------------
  -- The regression test
  ---------------------------------------------------------------------------

  -- No `⊢skip` derivation at `g 0`: the `g i` are pairwise non-bisimilar, so
  -- `skip/cycle` can never fire and `skip/step` would have to descend forever.
  ce/no-skip : ¬ (Lf & [] ⊢skip P ◂ Pr ∶ g 0)
  ce/no-skip = noSkip (λ ())

  -- … and `Wait` agrees.  This is the statement that the OLD, ν-based `Wait`
  -- got wrong: it held at `g 0` (by `force w = r/step⁺ P/na (sA i) …`,
  -- deferring forever on the strength of `P ∈T (g i)`), which made
  -- `Wait ⟹ ⊢skip` — hence `⊢a ⟹ ⊢p` — false.  `WaitV`'s visited set fixes
  -- it: a cycle must point at a state actually on the path, and here there is
  -- never one.
  ce/no-wait : ¬ WaitV P 𝒮 (λ _ → ⊥) (g 0)
  ce/no-wait w = ce/no-skip (wait⇒skip P Pr 𝒮 w)
