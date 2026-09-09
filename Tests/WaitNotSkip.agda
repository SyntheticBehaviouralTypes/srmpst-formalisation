{-# OPTIONS --guardedness #-}

-- TODO.md §7 step 4: `Wait ⟹ ⊢skip` is FALSE at the abstract level.
--
-- This is the counterexample, mechanized: a concrete `BTheory` with all ten
-- `WellBehaved` axioms discharged, a state `g 0` with `Wait P 𝒮 (g 0)`, and a
-- proof that NO `⊢skip` derivation exists at `g 0`.
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
-- `Wait P 𝒮 (g 0)` holds coinductively: every `g i` steps, the `e` branch is an
-- `𝒮`-leaf, and the `g (suc i)` branch is a guard leaf (`P ∈T (g i)` via
-- `b i` then `p`).  But no finite `⊢skip` tree exists: `skip/main` needs
-- `𝒮 (g i)`, false; `skip/cycle` needs a bisimilar ancestor, and the `g i` are
-- pairwise NON-bisimilar; so `skip/step` must descend forever.
--
-- What makes them non-bisimilar is the ARITY: at `g i` the branching is over
-- `Fin (suc (suc i))`, so `a i` and `a j` are different actions for `i ≢ j`.
-- Both steps out of `g i` share that arity, which is what `step-arity-deterministic`
-- demands, and both share the comm `Q⟶R`, which is what `recv-overlap⇒same-comm`
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
  using (_≡_; refl; sym; cong; subst)

open import Definitions.Typing

module Tests.WaitNotSkip where

  N : ℕ
  N = 3

  open import Definitions.Common N
  open import Definitions.Actions N
  open import Definitions.Proc N using (Proc; ∅; NProc; _◂_)
  open import Definitions.Expr using (Sort; s/unit)

  P Q R : Part
  P = zero
  Q = suc zero
  R = suc (suc zero)

  qr : Comm
  qr = Q ⟶ R

  pq : Comm
  pq = P ⟶ Q

  ---------------------------------------------------------------------------
  -- States and actions
  ---------------------------------------------------------------------------

  data St : Set where
    g : ℕ → St
    e : St
    z : St

  -- Arity `suc i` at `g i`; label 0 continues the chain, label 1 exits to `e`.
  aA : ℕ → Action
  aA i = qr # (zero {suc i} < s/unit >)

  bA : ℕ → Action
  bA i = qr # (suc (zero {i}) < s/unit >)

  pA : Action
  pA = pq # (zero {0} < s/unit >)

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
  -- equality): the arity, the label-as-ℕ, and the sender.

  aA-inj : ∀ {i j} → aA i ≡ aA j → i ≡ j
  aA-inj eq = suc-injective (cong nchoices eq)

  aA≢bA : ∀ {i j} → aA i ≡ bA j → ⊥
  aA≢bA eq with cong (λ α → toℕ (label α)) eq
  ... | ()

  aA≢pA : ∀ {i} → aA i ≡ pA → ⊥
  aA≢pA eq with cong sender eq
  ... | ()

  bA≢pA : ∀ {i} → bA i ≡ pA → ⊥
  bA≢pA eq with cong sender eq
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
  -- Well-behavedness: all ten axioms
  ---------------------------------------------------------------------------

  wb : WellBehaved theory
  wb = record
    { recv-overlap⇒same-comm = rovl
    ; sender≢receiver        = s≢r
    ; step-deterministic     = det
    ; step-sort-deterministic = sortDet
    ; step-arity-deterministic = arityDet
    ; step-is-prop           = isProp
    ; no-new-branch/step     = nnb
    ; no-new-comm/step       = nnc
    ; stepback/~             = sback
    ; step-diamond           = diam
    }
    where
      -- Every pair of steps out of a state shares the comm `Q⟶R` (at `g i`) or
      -- is a single step (at `e`), so this is `refl` throughout.
      rovl :
        ∀ {G α α′ G′ G″}
        → G ⇒ α  ⇒ G′
        → G ⇒ α′ ⇒ G″
        → receiver α ∈α α′
        → Action.comm α ≡ Action.comm α′
      rovl (sA _) (sA _) _ = refl
      rovl (sA _) (sB _) _ = refl
      rovl (sB _) (sA _) _ = refl
      rovl (sB _) (sB _) _ = refl
      rovl sP     sP     _ = refl

      s≢r : ∀ {G G′ α} → G ⇒ α ⇒ G′ → sender α ≡ receiver α → ⊥
      s≢r (sA _) ()
      s≢r (sB _) ()
      s≢r sP     ()

      det : ∀ {G α G′ G″} → G ⇒ α ⇒ G′ → G ⇒ α ⇒ G″ → G′ ≡ G″
      det (sA _) (sA _) = refl
      det (sB _) (sB _) = refl
      det sP     sP     = refl

      sortDet :
        ∀ {G G′ G″ α I S T}{i : Fin (suc I)}
        → G ⇒ α # i < S > ⇒ G′
        → G ⇒ α # i < T > ⇒ G″
        → S ≡ T
      sortDet (sA _) (sA _) = refl
      sortDet (sB _) (sB _) = refl
      sortDet sP     sP     = refl

      arityDet :
        ∀ {G G′ G″ α I J S T}{i : Fin (suc I)}{j : Fin (suc J)}
        → G ⇒ α # i < S > ⇒ G′
        → G ⇒ α # j < T > ⇒ G″
        → I ≡ J
      arityDet (sA _) (sA _) = refl
      arityDet (sA _) (sB _) = refl
      arityDet (sB _) (sA _) = refl
      arityDet (sB _) (sB _) = refl
      arityDet sP     sP     = refl

      isProp : ∀ {G β G′} → (gr₁ gr₂ : G ⇒ β ⇒ G′) → gr₁ ≡ gr₂
      isProp (sA _) (sA _) = refl
      isProp (sB _) (sB _) = refl
      isProp sP     sP     = refl

      -- Vacuous: whenever `G′` offers `γ`, the premise `… ∉α β` fails, because
      -- every action in the theory involves `Q`.
      nnb :
        ∀ {G G′ Gᵢ Gⱼ′ β γ cᵢ cⱼ}
        → G ⇒ β ⇒ G′
        → Comm.receiver γ ∉α β
        → G  ⇒ γ # cᵢ ⇒ Gᵢ
        → G′ ⇒ γ # cⱼ ⇒ Gⱼ′
        → ∃[ Gⱼ ] G ⇒ γ # cⱼ ⇒ Gⱼ
      nnb (sA _) r∉ (sA _) (sA _) = ⊥-elim (_∉c_.∉R r∉ refl)
      nnb (sA _) r∉ (sA _) (sB _) = ⊥-elim (_∉c_.∉R r∉ refl)
      nnb (sA _) r∉ (sB _) (sA _) = ⊥-elim (_∉c_.∉R r∉ refl)
      nnb (sA _) r∉ (sB _) (sB _) = ⊥-elim (_∉c_.∉R r∉ refl)

      nnc :
        ∀ {G G′ Gγ β γ}
        → G ⇒ β ⇒ G′
        → sender γ ∉α β
        → receiver γ ∉α β
        → G′ ⇒ γ ⇒ Gγ
        → ∃[ Gγ′ ] G ⇒ γ ⇒ Gγ′
      nnc (sA _) s∉ _  (sA _) = ⊥-elim (_∉c_.∉S s∉ refl)
      nnc (sA _) s∉ _  (sB _) = ⊥-elim (_∉c_.∉S s∉ refl)
      nnc (sB _) _  r∉ sP     = ⊥-elim (_∉c_.∉S r∉ refl)

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
      diam (sA _) (sA _) d = ⊥-elim (_∉c_.∉R (proj₁ d) refl)
      diam (sA _) (sB _) d = ⊥-elim (_∉c_.∉R (proj₁ d) refl)
      diam (sB _) (sA _) d = ⊥-elim (_∉c_.∉R (proj₁ d) refl)
      diam (sB _) (sB _) d = ⊥-elim (_∉c_.∉R (proj₁ d) refl)
      diam sP     sP     d = ⊥-elim (_∉c_.∉R (proj₁ d) refl)

  open import Definitions.Typing.Sets wb
  open MPST wb using (_&_⊢skip_∶_; skip/main; skip/step; skip/cycle)

  ---------------------------------------------------------------------------
  -- The leaf family: "P is immediately active".  `~`-closed.
  ---------------------------------------------------------------------------

  𝒮 : Pred
  𝒮 s = ∃[ α ] ∃[ t ] (s ⇒ α ⇒ t) × P ∈α α

  𝒮/closed : Closed 𝒮
  𝒮/closed G~H (α , _ , gr , px) =
    α , _ , ~L→ G~H gr , px

  e∈𝒮 : 𝒮 e
  e∈𝒮 = pA , z , sP , ∈S refl

  g∉𝒮 : ∀ {i} → ¬ 𝒮 (g i)
  g∉𝒮 (_ , _ , sA _ , ∈S ())
  g∉𝒮 (_ , _ , sA _ , ∈R ())
  g∉𝒮 (_ , _ , sB _ , ∈S ())
  g∉𝒮 (_ , _ , sB _ , ∈R ())

  P/na : ∀ {i} → P not-active-in (g i)
  P/na (sA _) = (λ ()) , (λ ())
  P/na (sB _) = (λ ()) , (λ ())

  P∈T/g : ∀ i → P ∈T (g i)
  P∈T/g i =
    bA i ∷ pA ∷ [] , z , tr/step (sB i) (tr/step sP tr/refl) , there (here (∈S refl))

  ---------------------------------------------------------------------------
  -- `Wait P 𝒮 (g 0)` holds
  ---------------------------------------------------------------------------

  mutual

    waitG : ∀ i → Wait P 𝒮 (g i)
    force (waitG i) = r/step⁺ P/na (sA i) (contG i)

    contG :
      ∀ i {u β}
      → g i ⇒ β ⇒ u
      → Reach∀ P (λ v → 𝒮 v ⊎ (P ∈T v × Wait P 𝒮 v)) u
    contG i (sA .i) = r/leaf (inj₂ (P∈T/g (suc i) , waitG (suc i)))
    contG i (sB .i) = r/leaf (inj₁ e∈𝒮)

  wait/g0 : Wait P 𝒮 (g 0)
  wait/g0 = waitG 0

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
  -- The counterexample
  ---------------------------------------------------------------------------

  -- `Wait` holds at `g 0` …
  ce/wait : Wait P 𝒮 (g 0)
  ce/wait = wait/g0

  -- … while no `⊢skip` derivation does.  So `Wait ⟹ ⊢skip` is false, and no
  -- amount of care in the RULES can recover it: the two objects genuinely
  -- differ on this theory.
  ce/no-skip : ¬ (Lf & [] ⊢skip P ◂ Pr ∶ g 0)
  ce/no-skip = noSkip (λ ())
