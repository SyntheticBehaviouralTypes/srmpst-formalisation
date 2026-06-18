{-# OPTIONS --guardedness #-}

-- Views of a theory, with a block's internal steps hidden.  A view has the
-- theory's states and labels.
--
--   * Local view of block `Ps`: what a process owning `Ps` is typed against.
--   * Global view of an assignment: every block's internal steps hidden.
--
-- Hiding is lazy: an own step may follow any run of internal steps.

open import Data.Nat using (ℕ)
open import Data.List using (List)
import Data.Fin.Properties as FinP
open import Data.Fin.Subset using (_∈_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star)
open import Data.Vec using () renaming (lookup to lu)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Nullary.Decidable using (_→-dec_)

open import Definitions.Behav using (BTheory; Balanced)

module Definitions.View {N : ℕ} (B : BTheory N) where

  open import Definitions.Common N
  open import Definitions.Actions N
  open import Definitions.Proc N using (Assignment)
  open BTheory B

  -- ══════════════════════════════════════════════════════════════════
  --  One block
  -- ══════════════════════════════════════════════════════════════════

  module Block (Ps : PartSet) where

    -- Every participant is a role of `Ps`: the process talks to itself.
    Internal : Action → Set
    Internal α = ∀ X → X ∈α α → X ∈ Ps

    internal? : ∀ α → Dec (Internal α)
    internal? α = FinP.all? λ X → (X ∈α? α) →-dec (X ∈? Ps)

    infix 4 _-τ->_

    _-τ->_ : Behav → Behav → Set
    G -τ-> G′ = ∃[ γ ] G -< γ >-> G′ × Internal γ

  open Block public

  -- ══════════════════════════════════════════════════════════════════
  --  The local view of a block
  -- ══════════════════════════════════════════════════════════════════

  module Local (Ps : PartSet) where

    Idle : Action → Set
    Idle α = Ps ∉αˢ α

    infix 4 _-<_>->ᵛ_

    -- An outsider's step, or an own step after own internal steps.
    _-<_>->ᵛ_ : Behav → Action → Behav → Set
    G -< α >->ᵛ G″ =
        (Idle α × G -< α >-> G″)
      ⊎ ( ¬ Internal Ps α × Ps ∈αˢ α
        × ∃[ G₁ ] Star (_-τ->_ Ps) G G₁ × G₁ -< α >-> G″ )

    view : BTheory N
    view = record { Behav = Behav ; _-<_>->_ = _-<_>->ᵛ_ }

    -- A view step is a step of `B` with the same label.
    balanced/view : Balanced B → Balanced view
    balanced/view bal = record
      { balanced = λ { (inj₁ (_ , gr)) → Balanced.balanced bal gr
                     ; (inj₂ (_ , _ , _ , _ , gr)) → Balanced.balanced bal gr } }

  open Local public

  -- ══════════════════════════════════════════════════════════════════
  --  The global view of an assignment
  -- ══════════════════════════════════════════════════════════════════

  -- Not opened: every use has one assignment, `open Global Ρ`.

  module Global {K : ℕ} (Ρ : Assignment K) where

    open Assignment Ρ

    block : Part → PartSet
    block X = lu roles (owner X)

    -- Internal to the block of a participant of `α`: hidden before `α`.
    τ⟨_⟩ : Action → Behav → Behav → Set
    τ⟨ α ⟩ G G′ =
      ∃[ γ ] G -< γ >-> G′ × ∃[ X ] X ∈α α × Internal (block X) γ

    -- Internal to the block of one of its participants, hence to a block.
    Hidden : Action → Set
    Hidden α = ∃[ X ] X ∈α α × Internal (block X) α

    infix 4 _-<_>->ᵍ_

    _-<_>->ᵍ_ : Behav → Action → Behav → Set
    G -< α >->ᵍ G″ =
      ¬ Hidden α × ∃[ G₁ ] Star τ⟨ α ⟩ G G₁ × G₁ -< α >-> G″

    global : BTheory N
    global = record { Behav = Behav ; _-<_>->_ = _-<_>->ᵍ_ }

    -- Runs of the global view.
    infix 4 _-[_]->ᵍ_

    _-[_]->ᵍ_ : Behav → List Action → Behav → Set
    _-[_]->ᵍ_ = BTheory._-[_]->_ global
