{-# OPTIONS --guardedness #-}

-- Bisimilarity classes (the paper's Fig. 3):
--
--   [G]∼ = { G′ | G′ ∼ G }        [G] —α→ [G′] ⟺ ∃ G″ ∼ G′ . G —α→ G″
--
-- `B/∼` is the MLTS whose states they are; the typing rules are stated on
-- it.  A class is given by a representative, as the paper writes `[G]`;
-- two classes are equal (`_≐_`) when their representatives are bisimilar.
-- The rest of this module moves steps, runs and the derived notions
-- between a class and its representatives.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; map) renaming (lookup to lu)
open import Data.Vec.Relation.Unary.Any using (Any)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)

open import Definitions.Behav using (BTheory; WellBehaved; Synchronous)

module Definitions.Classes {N : ℕ} (B : BTheory N) where

  open import Definitions.Common N
  open import Definitions.Actions N
  open BTheory B

  -- ══════════════════════════════════════════════════════════════════
  --  Classes
  -- ══════════════════════════════════════════════════════════════════

  record Cls : Set where
    constructor [_]
    field rep : Behav

  open Cls public

  infix 4 _∈ᶜ_ _≐_

  -- `[ G ]` as a set of states.
  _∈ᶜ_ : Behav → Cls → Set
  H ∈ᶜ G = H ~ rep G

  -- Equality of classes.
  _≐_ : Cls → Cls → Set
  G ≐ H = rep G ~ rep H

  ≐-refl : ∀ {G} → G ≐ G
  ≐-refl = ~refl

  ≐-sym : ∀ {G H} → G ≐ H → H ≐ G
  ≐-sym = ~sym

  ≐-trans : ∀ {G H K} → G ≐ H → H ≐ K → G ≐ K
  ≐-trans = ~trans

  -- [G] —α→ [G′] ⟺ ∃ G″ ∼ G′ . G —α→ G″
  _-<_>->ᶜ_ : Cls → Action → Cls → Set
  G -< α >->ᶜ G′ = ∃[ G″ ] G″ ~ rep G′ × rep G -< α >-> G″

  -- The MLTS of classes.
  B/∼ : BTheory N
  B/∼ = record { Behav = Cls ; _-<_>->_ = _-<_>->ᶜ_ }

  module C = BTheory B/∼

  -- A vector of states, as classes.
  classes : ∀ {n} → Vec Behav n → Vec Cls n
  classes ws = map [_] ws

  -- Contexts of classes: `X ∶ G ∈ Δ` and `G ∈ᵛ Ξ`, up to `≐`.
  infix 4 _∶_∈_ _∈ᵛ_

  _∶_∈_ : ∀ {δ} → Fin δ → Cls → Vec Cls δ → Set
  X ∶ G ∈ Δ = lu Δ X ≐ G

  _∈ᵛ_ : ∀ {ξ} → Cls → Vec Cls ξ → Set
  G ∈ᵛ Ξ = Any (_≐ G) Ξ

  -- ══════════════════════════════════════════════════════════════════
  --  Classes and representatives
  -- ══════════════════════════════════════════════════════════════════

  step⇒ᶜ : ∀ {G α G′} → G -< α >-> G′ → [ G ] C.-< α >-> [ G′ ]
  step⇒ᶜ gr = _ , ~refl , gr

  stepᶜ⇒ :
    ∀ {G α G′} → G C.-< α >-> G′ → ∃[ G″ ] rep G -< α >-> G″ × G″ ~ rep G′
  stepᶜ⇒ (G″ , G″~ , gr) = G″ , gr , G″~

  -- A class step out of any member of the source.
  stepᶜ⇒~ :
    ∀ {G H α G′} → H ~ rep G → G C.-< α >-> G′
    → ∃[ H′ ] H -< α >-> H′ × H′ ~ rep G′
  stepᶜ⇒~ H~ (G″ , G″~ , gr) =
    let H′ , gr′ , H′~G″ = ~R H~ gr
    in H′ , gr′ , ~trans H′~G″ G″~

  -- Runs, and runs free of `R`.
  stepsᶜ⇒ : ∀ {G G′} → G C.-→* G′ → ∃[ H ] rep G -→* H × H ~ rep G′
  stepsᶜ⇒ ε = _ , ε , ~refl
  stepsᶜ⇒ ((α , (G₁ , G₁~ , gr)) ◅ run) =
    let H , run′ , H~ = stepsᶜ⇒ run
        H′ , run″ , H~H′ = steps/~ (~sym G₁~) run′
    in H′ , (α , gr) ◅ run″ , ~trans (~sym H~H′) H~

  steps⇒ᶜ : ∀ {G G′} → G -→* G′ → [ G ] C.-→* [ G′ ]
  steps⇒ᶜ ε                = ε
  steps⇒ᶜ ((α , gr) ◅ run) = (α , step⇒ᶜ gr) ◅ steps⇒ᶜ run

  runᶜ⇒ :
    ∀ {R G G′} → G C.-[¬ R ]->* G′ → ∃[ H ] rep G -[¬ R ]->* H × H ~ rep G′
  runᶜ⇒ ε = _ , ε , ~refl
  runᶜ⇒ ((α , (G₁ , G₁~ , gr) , R∉) ◅ run) =
    let H , run′ , H~ = runᶜ⇒ run
        H′ , run″ , H~H′ = run/~ (~sym G₁~) run′
    in H′ , (α , gr , R∉) ◅ run″ , ~trans (~sym H~H′) H~

  run⇒ᶜ : ∀ {R G G′} → G -[¬ R ]->* G′ → [ G ] C.-[¬ R ]->* [ G′ ]
  run⇒ᶜ ε                      = ε
  run⇒ᶜ ((α , gr , R∉) ◅ run) = (α , step⇒ᶜ gr , R∉) ◅ run⇒ᶜ run

  -- `G —R→`
  actᶜ⇒ : ∀ {R G} → G C.-⟨ R ⟩-> → rep G -⟨ R ⟩->
  actᶜ⇒ (_ , _ , st , own) = let _ , gr , _ = stepᶜ⇒ st in _ , _ , gr , own

  act⇒ᶜ : ∀ {R G} → G -⟨ R ⟩-> → [ G ] C.-⟨ R ⟩->
  act⇒ᶜ (_ , _ , gr , own) = _ , _ , step⇒ᶜ gr , own

  -- `R ∈ G`
  ∈Tᶜ⇒ : ∀ {R G} → R C.∈T G → R ∈T rep G
  ∈Tᶜ⇒ (_ , run , (_ , _ , st , own)) =
    let H , run′ , H~ = stepsᶜ⇒ run
        _ , gr , _ = stepᶜ⇒~ H~ st
    in H , run′ , (_ , _ , gr , own)

  ∈T⇒ᶜ : ∀ {R G} → R ∈T G → R C.∈T [ G ]
  ∈T⇒ᶜ (_ , run , act) = _ , steps⇒ᶜ run , act⇒ᶜ act

  -- `r first-in (R , G)`
  first-inᶜ⇒ : ∀ {r R G} → r C.first-in (R , [ G ]) → r first-in (R , G)
  first-inᶜ⇒ (r∈ , f) = r∈ , λ run gr own → f (run⇒ᶜ run) (step⇒ᶜ gr) own

  first-in⇒ᶜ : ∀ {r R G} → r first-in (R , rep G) → r C.first-in (R , G)
  first-in⇒ᶜ (r∈ , f) = r∈ , λ run gr own →
    let H , run′ , H~ = runᶜ⇒ run
        _ , gr′ , _ = stepᶜ⇒~ H~ gr
    in f run′ gr′ own

  -- A step with a given event at `P`.
  evᶜ⇒ :
    ∀ {G P e G′} → G C.-<[ P ↦ e ]>-> G′
    → ∃[ G″ ] rep G -<[ P ↦ e ]>-> G″ × G″ ~ rep G′
  evᶜ⇒ (α , eq , st) = let G″ , gr , G″~ = stepᶜ⇒ st in G″ , (α , eq , gr) , G″~

  ev⇒ᶜ : ∀ {G P e G′} → G -<[ P ↦ e ]>-> G′ → [ G ] C.-<[ P ↦ e ]>-> [ G′ ]
  ev⇒ᶜ (α , eq , gr) = α , eq , step⇒ᶜ gr

  -- ══════════════════════════════════════════════════════════════════
  --  B/∼ is well-behaved when B is
  -- ══════════════════════════════════════════════════════════════════

  -- The paper's lemma on classes.  Its condition 6, no new
  -- communications, is `Synchronous`'s `no-new-comm/step` here, hence two
  -- statements.

  ≐⇒~ᶜ : ∀ {G H} → G ≐ H → G C.~ H
  ≐⇒~ᶜ G≐H .C._~_.sym = ≐⇒~ᶜ (~sym G≐H)
  ≐⇒~ᶜ G≐H .C._~_.step (_ , G″~ , gr) =
    let H″ , gr′ , G″~H″ = ~L G≐H gr
    in [ H″ ] , (H″ , ~refl , gr′) , ≐⇒~ᶜ (~trans (~sym G″~) G″~H″)

  wellBehaved/∼ : WellBehaved B → WellBehaved B/∼
  wellBehaved/∼ wb = record
    { recv-overlap = λ { (_ , _ , gr₀) (_ , _ , gr₁) →
        W.recv-overlap gr₀ gr₁ }
    ; step-deterministic = λ { (_ , G₀~ , gr₀) (_ , G₁~ , gr₁) →
        ≐⇒~ᶜ (~trans (~sym G₀~)
          (~trans (W.step-deterministic gr₀ gr₁) G₁~)) }
    ; step-sort-det = λ { (_ , _ , gr₀) (_ , _ , gr₁) →
        W.step-sort-det gr₀ gr₁ }
    ; no-new-branch/step = λ { (_ , H~ , gr) idle (_ , _ , gr₀) st eq →
        let _ , gr₁ , _ = stepᶜ⇒~ H~ st
            G′ , gr′ = W.no-new-branch/step gr idle gr₀ gr₁ eq
        in [ G′ ] , (G′ , ~refl , gr′) }
    ; step-diamond = λ { (_ , H₁~ , gr₁) (_ , H₂~ , gr₂) ind →
        let X , Y , grX , grY , X~Y = W.step-diamond gr₁ gr₂ ind
            X′ , grX′ , X~X′ = ~L H₁~ grX
            Y′ , grY′ , Y~Y′ = ~L H₂~ grY
        in [ X ] , [ Y ] , (X′ , ~sym X~X′ , grX′)
         , (Y′ , ~sym Y~Y′ , grY′) , ≐⇒~ᶜ X~Y }
    }
    where module W = WellBehaved wb

  synchronous/∼ : Synchronous B → Synchronous B/∼
  synchronous/∼ sync = record
    { balanced = λ { (_ , _ , gr) → S.balanced gr }
    ; no-new-comm/step = λ { (_ , H~ , gr) idle st →
        let _ , gr₀ , _ = stepᶜ⇒~ H~ st
            G′ , gr′ = S.no-new-comm/step gr idle gr₀
        in [ G′ ] , (G′ , ~refl , gr′) }
    }
    where module S = Synchronous sync
