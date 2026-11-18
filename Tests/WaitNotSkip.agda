{-# OPTIONS --guardedness #-}

-- A well-behaved theory where neither a skip tree (`SkipT`, the shape of the
-- paper's skipping judgement) nor `Wait` holds at `g 0`,
-- although every `g i` can reach a state where `P` acts.  A `Wait` defined
-- as a fixpoint over states alone would hold there.
--
-- The theory is an infinite chain
--
--     g 0 --a 0--> g 1 --a 1--> g 2 --a 2--> ⋯          (all Q⟶R, P-free)
--      |            |            |
--     b 0          b 1          b 2                     (all Q⟶R, P-free)
--      v            v            v
--      e -----------p----------> z                      (P⟶Q: where P acts)
--
-- `𝒮` ("`P` is immediately active") holds at `e`, at no `g i`.  The `g i`
-- are pairwise non-bisimilar (their `continue` labels differ), so no cycle
-- closes and no finite tree exists.

open import Definitions.Expr.Syntax
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (<-trans; n<1+n; <-irrefl; suc-injective)

open import Data.Fin using (Fin; zero; suc; toℕ)

open import Data.Vec using (Vec; []; _∷_) renaming (lookup to lu)

open import Data.Product using (∃-syntax; _,_; _×_)

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Empty using (⊥; ⊥-elim)

open import Data.List using ([]; _∷_)

open import Relation.Unary using () renaming (∅ to ∅S)
open import Data.List.Relation.Unary.Any using (here; there)

open import Relation.Nullary using (¬_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Definitions.Typing.Declarative

module Tests.WaitNotSkip where

  N : ℕ
  N = 3

  open import Definitions.Common N
  open import Definitions.Actions N
  open import Definitions.Expr using (s/unit)
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

  -- At `g i`, `Q` chooses: `continue i` goes on along the chain, `exit i`
  -- leaves it for `e`.  `continue i` names its `i`.
  continue exit : ℕ → ℕ
  continue i = suc i
  exit     i = zero

  -- `P`'s one message, at `e`
  poke : ℕ
  poke = zero

  aA : ℕ → Action
  aA i = Q ⟶ ⁅ R ⁆ # continue i < s/unit >

  bA : ℕ → Action
  bA i = Q ⟶ ⁅ R ⁆ # exit i < s/unit >

  pA : Action
  pA = P ⟶ ⁅ Q ⁆ # poke < s/unit >

  data _⇒_⇒_ : St → Action → St → Set where
    sA : ∀ i → g i ⇒ aA i ⇒ g (suc i)
    sB : ∀ i → g i ⇒ bA i ⇒ e
    sP : e ⇒ pA ⇒ z

  -- Inversion without unifying through `aA`/`bA`.
  stepInv :
    ∀ {X α Y}
    → X ⇒ α ⇒ Y
    → (∃[ i ] (X ≡ g i) × (α ≡ aA i) × (Y ≡ g (suc i)))
    ⊎ (∃[ i ] (X ≡ g i) × (α ≡ bA i) × (Y ≡ e))
    ⊎ ((X ≡ e) × (α ≡ pA) × (Y ≡ z))
  stepInv (sA i) = inj₁ (i , refl , refl , refl)
  stepInv (sB i) = inj₂ (inj₁ (i , refl , refl , refl))
  stepInv sP     = inj₂ (inj₂ (refl , refl , refl))

  -- Distinct actions, told apart by `Q`'s label, and `P`.

  label/Q : Action → ℕ
  label/Q α = maybe (λ e → Choice.label (Event.choice e)) 0 (ev α Q)

  aA-inj : ∀ {i j} → aA i ≡ aA j → i ≡ j
  aA-inj eq = suc-injective (cong label/Q eq)

  aA≢bA : ∀ {i j} → aA i ≡ bA j → ⊥
  aA≢bA eq with cong label/Q eq
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

  -- Bisimilarity on this theory is equality.
  ~⇒≡ : ∀ {X Y} → X ~ Y → X ≡ Y

  ~⇒≡ {g i} X~Y with ~L X~Y (sA i)
  ... | _ , st , _ with stepInv st
  ...   | inj₁ (j , refl , eq , _)        = cong g (aA-inj eq)
  ...   | inj₂ (inj₁ (j , _ , eq , _))    = ⊥-elim (aA≢bA {j = j} eq)
  ...   | inj₂ (inj₂ (_ , eq , _))        = ⊥-elim (aA≢pA eq)

  ~⇒≡ {e} X~Y with ~L X~Y sP
  ... | _ , st , _ with stepInv st
  ...   | inj₁ (_ , _ , eq , _)           = ⊥-elim (aA≢pA (sym eq))
  ...   | inj₂ (inj₁ (j , _ , eq , _))    = ⊥-elim (bA≢pA {i = j} (sym eq))
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
  -- Well-behavedness: all five axioms
  ---------------------------------------------------------------------------

  wb : WellBehaved theory
  wb = record
    { recv-overlap           = rovl
    ; step-deterministic     = det
    ; step-sort-det          = sortDet
    ; no-new-branch/step     = nnb
    ; step-diamond           = diam
    }
    where
      -- Steps out of one state share the comm `Q⟶R`, or are one step.
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

      det : ∀ {G α G′ G″} → G ⇒ α ⇒ G′ → G ⇒ α ⇒ G″ → G′ ~ G″
      det (sA _) s with stepInv s
      ... | inj₁ (_ , refl , _ , refl)          = ~refl
      ... | inj₂ (inj₁ (j , refl , eq , _))     = ⊥-elim (aA≢bA {j = j} eq)
      ... | inj₂ (inj₂ (() , _))
      det (sB i) s with stepInv s
      ... | inj₁ (_ , refl , eq , _)            = ⊥-elim (aA≢bA {j = i} (sym eq))
      ... | inj₂ (inj₁ (_ , refl , _ , refl))   = ~refl
      ... | inj₂ (inj₂ (() , _))
      det sP s with stepInv s
      ... | inj₁ (_ , () , _)
      ... | inj₂ (inj₁ (_ , () , _))
      ... | inj₂ (inj₂ (_ , _ , refl))          = ~refl

      -- Two receive events of the SAME action are the same event.
      same : ∀ {Y c c′} → just ((？ Y) # c) ≡ just ((？ Y) # c′) → c ≡ c′
      same {c = c} = cong (maybe Event.choice c)

      -- Across `aA`/`bA`, only `R` receives; there the labels differ.
      sortDet :
        ∀ {G G′ G″ α α′ Y X ℓ S T}
        → G ⇒ α ⇒ G′
        → G ⇒ α′ ⇒ G″
        → ev α X ≡ just ((？ Y) # ℓ < S >)
        → ev α′ X ≡ just ((？ Y) # ℓ < T >)
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
      nnb (sA _) idle (sA _) _ _ = ⊥-elim (idle R (Q , _ , refl) (_ , refl))
      nnb (sA _) idle (sB _) _ _ = ⊥-elim (idle R (Q , _ , refl) (_ , refl))
      nnb (sB _) idle (sA _) _ _ = ⊥-elim (idle R (Q , _ , refl) (_ , refl))
      nnb (sB _) idle (sB _) _ _ = ⊥-elim (idle R (Q , _ , refl) (_ , refl))
      nnb sP     idle sP     () _

      -- Vacuous: steps out of one state share a receiver.
      diam :
        ∀ {G α G₁ α′ G₂}
        → G ⇒ α  ⇒ G₁
        → G ⇒ α′ ⇒ G₂
        → α ⋄ α′
        → ∃[ X ] ∃[ Y ] (G₁ ⇒ α′ ⇒ X) × (G₂ ⇒ α ⇒ Y) × X ~ Y
      diam (sA _) (sA _) (_ , d , _) = ⊥-elim (d R (Q , _ , refl) (_ , refl))
      diam (sA _) (sB _) (_ , d , _) = ⊥-elim (d R (Q , _ , refl) (_ , refl))
      diam (sB _) (sA _) (_ , d , _) = ⊥-elim (d R (Q , _ , refl) (_ , refl))
      diam (sB _) (sB _) (_ , d , _) = ⊥-elim (d R (Q , _ , refl) (_ , refl))
      diam sP     sP     (α≢α , _) = ⊥-elim (α≢α refl)

  open import Definitions.Typing.Alg wb
  open import Definitions.Typing.AlgEquiv wb
    using (SkipT; st/main; st/step; st/cycle; wait⇒skip)

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

  P/na : ∀ {i} → ¬ g i -⟨ ⁅ P ⁆ ⟩->
  P/na (_ , _ , sA i , own) =
    ∉α→∉αˢ⁅⁆ {P} {aA i} (≡nothing→∉α {P} {aA i} refl) own
  P/na (_ , _ , sB i , own) =
    ∉α→∉αˢ⁅⁆ {P} {bA i} (≡nothing→∉α {P} {bA i} refl) own

  P∈T/g : ∀ i → ⁅ P ⁆ ∈T (g i)
  P∈T/g i =
    _ , (bA i , sB i) ◅ ε , (z , pA , sP , ∈α→∈αˢ⁅⁆ {P} {pA} (_ , refl))

  ---------------------------------------------------------------------------
  -- No skip tree at `g 0`
  ---------------------------------------------------------------------------

  -- Every visited state is some `g j` below the current index, which rules
  -- out `st/cycle`.
  Below : ∀ {ξ} → ℕ → Vec St ξ → Set
  Below i Ξ = ∀ X → ∃[ j ] (lu Ξ X ≡ g j) × (j < i)

  below/cons : ∀ {ξ}{Ξ : Vec St ξ}{i} → Below i Ξ → Below (suc i) (g i ∷ Ξ)
  below/cons {i = i} bel zero    = i , refl , n<1+n i
  below/cons {i = i} bel (suc X) with bel X
  ... | j , eq , j<i = j , eq , <-trans j<i (n<1+n i)

  noSkip :
    ∀ {ξ}{Ξ : Vec St ξ}{i}
    → Below i Ξ
    → SkipT ⁅ P ⁆ 𝒮 Ξ (g i)
    → ⊥

  noSkip bel (st/main leaf) =
    g∉𝒮 leaf

  noSkip {i = i} bel (st/step _ _ ktd) =
    noSkip (below/cons bel) (ktd (sA i))

  noSkip {i = i} bel (st/cycle {X = X} eq _) with bel X
  ... | j , luEq , j<i =
    <-irrefl (gInj (subst (_~ g i) luEq eq)) j<i
    where
      gInj : ∀ {m n} → g m ~ g n → m ≡ n
      gInj b with ~⇒≡ b
      ... | refl = refl

  ---------------------------------------------------------------------------
  -- The regression test
  ---------------------------------------------------------------------------

  -- No skip tree at `g 0`.
  ce/no-skip : ¬ SkipT ⁅ P ⁆ 𝒮 [] (g 0)
  ce/no-skip = noSkip (λ ())

  -- … and no `Wait` either.
  ce/no-wait : ¬ WaitV ⁅ P ⁆ 𝒮 ∅S (g 0)
  ce/no-wait w = ce/no-skip (wait⇒skip ⁅ P ⁆ 𝒮 w)
