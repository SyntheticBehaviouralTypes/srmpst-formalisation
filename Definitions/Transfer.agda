{-# OPTIONS --guardedness #-}

-- Two theories with equivalent steps agree on bisimilarity, `WellBehaved`,
-- `Balanced` and typing.

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Vec using (Vec)
open import Relation.Nullary using (¬_)

open import Definitions.Behav using (BTheory; WellBehaved; Balanced)
open import Definitions.Typing.Declarative using (module MPST)
import Definitions.Actions as Actions

module Definitions.Transfer
  {N : ℕ} {X : Set}
  (_⟶₁_ _⟶₂_ : X → Actions.Action N → X → Set)
  (to   : ∀ {G α G′} → _⟶₁_ G α G′ → _⟶₂_ G α G′)
  (from : ∀ {G α G′} → _⟶₂_ G α G′ → _⟶₁_ G α G′)
  where

  open import Definitions.Common N
  open import Definitions.Actions N
  open import Definitions.Proc N using (NProc)

  T₁ T₂ : BTheory N
  T₁ = record { Behav = X ; _-<_>->_ = _⟶₁_ }
  T₂ = record { Behav = X ; _-<_>->_ = _⟶₂_ }

  module B₁ = BTheory T₁
  module B₂ = BTheory T₂

  -- ══════════════════════════════════════════════════════════════════
  --  Runs and participation
  -- ══════════════════════════════════════════════════════════════════

  run⇒ : ∀ {G αs H} → G B₁.-[ αs ]-> H → G B₂.-[ αs ]-> H
  run⇒ B₁.tr/refl        = B₂.tr/refl
  run⇒ (B₁.tr/step gr tr) = B₂.tr/step (to gr) (run⇒ tr)

  run⇐ : ∀ {G αs H} → G B₂.-[ αs ]-> H → G B₁.-[ αs ]-> H
  run⇐ B₂.tr/refl        = B₁.tr/refl
  run⇐ (B₂.tr/step gr tr) = B₁.tr/step (from gr) (run⇐ tr)

  skip⇒ : ∀ {G P H} → G B₁.-[¬ P ]->* H → G B₂.-[¬ P ]->* H
  skip⇒ (αs , tr , all) = αs , run⇒ tr , all

  skip⇐ : ∀ {G P H} → G B₂.-[¬ P ]->* H → G B₁.-[¬ P ]->* H
  skip⇐ (αs , tr , all) = αs , run⇐ tr , all

  ∈T⇒ : ∀ {P G} → P B₁.∈T G → P B₂.∈T G
  ∈T⇒ (αs , H , tr , mem) = αs , H , run⇒ tr , mem

  ∈T⇐ : ∀ {P G} → P B₂.∈T G → P B₁.∈T G
  ∈T⇐ (αs , H , tr , mem) = αs , H , run⇐ tr , mem

  na⇒ : ∀ {P G} → P B₁.not-active-in G → P B₂.not-active-in G
  na⇒ na gr = na (from gr)

  focus⇒ : ∀ {P Y G} → B₁.Focus P Y G → B₂.Focus P Y G
  focus⇒ f tr gr own = f (skip⇐ tr) (from gr) own

  -- ══════════════════════════════════════════════════════════════════
  --  Bisimilarity
  -- ══════════════════════════════════════════════════════════════════

  mutual
    ≲⇒ : ∀ {G H} → G B₁.~ H → G B₂.≲ H
    ≲⇒ G~H .B₂._≲_.simulate gr =
      let _ , gr′ , b = B₁.~L G~H (from gr) in _ , to gr′ , ~⇒ b

    ~⇒ : ∀ {G H} → G B₁.~ H → G B₂.~ H
    ~⇒ G~H = ≲⇒ G~H , ≲⇒ (B₁.~sym G~H)

  -- ══════════════════════════════════════════════════════════════════
  --  The axioms
  -- ══════════════════════════════════════════════════════════════════

  wb⇒ : WellBehaved T₁ → WellBehaved T₂
  wb⇒ wb = record
    { recv-overlap       = λ g g′ → recv-overlap (from g) (from g′)
    ; step-deterministic = λ g g′ → ~⇒ (step-deterministic (from g) (from g′))
    ; step-sort-det      = λ g g′ → step-sort-det (from g) (from g′)
    ; step-arity-det     = λ g g′ → step-arity-det (from g) (from g′)
    ; no-new-branch/step = λ gβ apart gγ gγ′ ceq →
        let _ , g = no-new-branch/step (from gβ) apart (from gγ) (from gγ′) ceq
        in _ , to g
    ; step-diamond = λ g g′ ind →
        let _ , _ , gX , gY , X~Y = step-diamond (from g) (from g′) ind
        in _ , _ , to gX , to gY , ~⇒ X~Y
    }
    where open WellBehaved wb

  bal⇒ : Balanced T₁ → Balanced T₂
  bal⇒ bal = record { balanced = λ g → Balanced.balanced bal (from g) }

  -- ══════════════════════════════════════════════════════════════════
  --  Typing
  -- ══════════════════════════════════════════════════════════════════

  module Typing (wb₁ : WellBehaved T₁) (wb₂ : WellBehaved T₂) where

    private
      module M₁ = MPST wb₁
      module M₂ = MPST wb₂

    mutual
      typing⇒ :
        ∀ {γ δ} {Γ : Vec _ γ} {Δ : Vec X δ} {PPr : NProc γ δ} {G}
        → M₁._&_⊢p_∶_ Γ Δ PPr G → M₂._&_⊢p_∶_ Γ Δ PPr G
      typing⇒ (M₁.t/send Q∈ foc (α , eq , gr) etd td) =
        M₂.t/send Q∈ (focus⇒ foc) (α , eq , to gr) etd (typing⇒ td)
      typing⇒ (M₁.t/recv R∈ foc (α , eq , gr , fr) conts) =
        M₂.t/recv R∈ (focus⇒ foc) (α , eq , to gr , fr)
          λ { (α′ , eq′ , gr′ , fr′) → typing⇒ (conts (α′ , eq′ , from gr′ , fr′)) }
      typing⇒ (M₁.t/skip std) = M₂.t/skip (skip/typing⇒ std)
      typing⇒ (M₁.t/unskip tr eq td) =
        M₂.t/unskip (skip⇒ tr) (~⇒ eq) (typing⇒ td)
      typing⇒ (M₁.t/if etd ttd ftd) = M₂.t/if etd (typing⇒ ttd) (typing⇒ ftd)
      typing⇒ (M₁.t/rec mg td)     = M₂.t/rec mg (typing⇒ td)
      typing⇒ (M₁.t/var eq)        = M₂.t/var (~⇒ eq)
      typing⇒ (M₁.t/end done)      = M₂.t/end λ inT → done (∈T⇐ inT)

      skip/typing⇒ :
        ∀ {γ δ ξ} {Γ : Vec _ γ} {Δ : Vec X δ} {Ξ : Vec X ξ}
          {PPr : NProc γ δ} {G}
        → M₁._&_&_⊢skip_∶_ Γ Δ Ξ PPr G → M₂._&_&_⊢skip_∶_ Γ Δ Ξ PPr G
      skip/typing⇒ (M₁.skip/main td) = M₂.skip/main (typing⇒ td)
      skip/typing⇒ (M₁.skip/step gr na ktd) =
        M₂.skip/step (to gr) (na⇒ na) λ gr′ → skip/typing⇒ (ktd (from gr′))
      skip/typing⇒ (M₁.skip/cycle eq inT) =
        M₂.skip/cycle (~⇒ eq) (∈T⇒ inT)
