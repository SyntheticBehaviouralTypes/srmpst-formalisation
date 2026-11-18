{-# OPTIONS --guardedness #-}

-- Two theories with equivalent steps agree on bisimilarity, `WellBehaved`,
-- `Balanced` and typing.

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Properties using (lookup-map)
open import Data.Vec.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import Relation.Nullary using (¬_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)

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
  open import Definitions.Proc N using (Proc)

  T₁ T₂ : BTheory N
  T₁ = record { Behav = X ; _-<_>->_ = _⟶₁_ }
  T₂ = record { Behav = X ; _-<_>->_ = _⟶₂_ }

  module B₁ = BTheory T₁
  module B₂ = BTheory T₂

  -- ══════════════════════════════════════════════════════════════════
  --  Runs and participation
  -- ══════════════════════════════════════════════════════════════════

  steps⇒ : ∀ {G H} → G B₁.-→* H → G B₂.-→* H
  steps⇒ ε                = ε
  steps⇒ ((α , gr) ◅ run) = (α , to gr) ◅ steps⇒ run

  steps⇐ : ∀ {G H} → G B₂.-→* H → G B₁.-→* H
  steps⇐ ε                = ε
  steps⇐ ((α , gr) ◅ run) = (α , from gr) ◅ steps⇐ run

  skip⇒ : ∀ {G P H} → G B₁.-[¬ P ]->* H → G B₂.-[¬ P ]->* H
  skip⇒ ε                      = ε
  skip⇒ ((α , gr , P∉) ◅ run) = (α , to gr , P∉) ◅ skip⇒ run

  skip⇐ : ∀ {G P H} → G B₂.-[¬ P ]->* H → G B₁.-[¬ P ]->* H
  skip⇐ ε                      = ε
  skip⇐ ((α , gr , P∉) ◅ run) = (α , from gr , P∉) ◅ skip⇐ run

  ∈T⇒ : ∀ {P G} → P B₁.∈T G → P B₂.∈T G
  ∈T⇒ (H , run , (_ , _ , gr , own)) = H , steps⇒ run , (_ , _ , to gr , own)

  ∈T⇐ : ∀ {P G} → P B₂.∈T G → P B₁.∈T G
  ∈T⇐ (H , run , (_ , _ , gr , own)) = H , steps⇐ run , (_ , _ , from gr , own)

  first-inᴮ⇒ : ∀ {r R G} → r B₁.first-in (R , G) → r B₂.first-in (R , G)
  first-inᴮ⇒ (r∈ , f) = r∈ , λ run gr own → f (skip⇐ run) (from gr) own

  -- ══════════════════════════════════════════════════════════════════
  --  Bisimilarity
  -- ══════════════════════════════════════════════════════════════════

  ~⇒ : ∀ {G H} → G B₁.~ H → G B₂.~ H
  ~⇒ G~H .B₂._~_.sym = ~⇒ (B₁.~sym G~H)
  ~⇒ G~H .B₂._~_.step gr =
    let _ , gr′ , b = B₁.~L G~H (from gr) in _ , to gr′ , ~⇒ b

  -- ══════════════════════════════════════════════════════════════════
  --  The axioms
  -- ══════════════════════════════════════════════════════════════════

  wb⇒ : WellBehaved T₁ → WellBehaved T₂
  wb⇒ wb = record
    { recv-overlap       = λ g g′ → recv-overlap (from g) (from g′)
    ; step-deterministic = λ g g′ → ~⇒ (step-deterministic (from g) (from g′))
    ; step-sort-det      = λ g g′ → step-sort-det (from g) (from g′)
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

  ~⇐ : ∀ {G H} → G B₂.~ H → G B₁.~ H
  ~⇐ G~H .B₁._~_.sym = ~⇐ (B₂.~sym G~H)
  ~⇐ G~H .B₁._~_.step gr =
    let _ , gr′ , b = B₂.~L G~H (to gr) in _ , from gr′ , ~⇐ b

  module Typing (wb₁ : WellBehaved T₁) (wb₂ : WellBehaved T₂) where

    private
      module M₁ = MPST wb₁
      module M₂ = MPST wb₂

    -- A class of `T₁` as one of `T₂`.
    ⟦_⟧ : M₁.Cls → M₂.Cls
    ⟦ G ⟧ = M₂.[ M₁.rep G ]

    ⟦_⟧ᵛ : ∀ {n} → Vec M₁.Cls n → Vec M₂.Cls n
    ⟦ Δ ⟧ᵛ = map ⟦_⟧ Δ

    step⇒ : ∀ {G α H} → G M₁.C.-< α >-> H → ⟦ G ⟧ M₂.C.-< α >-> ⟦ H ⟧
    step⇒ (H″ , H″~ , gr) = H″ , ~⇒ H″~ , to gr

    step⇐ : ∀ {G α H} → ⟦ G ⟧ M₂.C.-< α >-> H → G M₁.C.-< α >-> M₁.[ M₂.rep H ]
    step⇐ (H″ , H″~ , gr) = H″ , ~⇐ H″~ , from gr

    ev⇒ : ∀ {G P e H} → G M₁.C.-<[ P ↦ e ]>-> H → ⟦ G ⟧ M₂.C.-<[ P ↦ e ]>-> ⟦ H ⟧
    ev⇒ (α , eq , st) = α , eq , step⇒ st

    ev⇐ : ∀ {G P e H} → ⟦ G ⟧ M₂.C.-<[ P ↦ e ]>-> H → G M₁.C.-<[ P ↦ e ]>-> M₁.[ M₂.rep H ]
    ev⇐ (α , eq , st) = α , eq , step⇐ st

    skipᶜ⇒ : ∀ {R G H} → G M₁.C.-[¬ R ]->* H → ⟦ G ⟧ M₂.C.-[¬ R ]->* ⟦ H ⟧
    skipᶜ⇒ ε                      = ε
    skipᶜ⇒ ((α , st , R∉) ◅ run) = (α , step⇒ st , R∉) ◅ skipᶜ⇒ run

    first-in⇒ :
      ∀ {r R G} → r M₁.C.first-in (R , G) → r M₂.C.first-in (R , ⟦ G ⟧)
    first-in⇒ fi = M₂.first-in⇒ᶜ (first-inᴮ⇒ (M₁.first-inᶜ⇒ fi))

    ∈ᵛ⇒ : ∀ {n}{Ξ : Vec M₁.Cls n}{G} → G M₁.∈ᵛ Ξ → ⟦ G ⟧ M₂.∈ᵛ ⟦ Ξ ⟧ᵛ
    ∈ᵛ⇒ {Ξ = _ ∷ _} (here e)  = here (~⇒ e)
    ∈ᵛ⇒ {Ξ = _ ∷ _} (there a) = there (∈ᵛ⇒ a)

    mutual
      typing⇒ :
        ∀ {γ δ} {Γ : Vec _ γ} {Δ : Vec M₁.Cls δ} {R} {P : Proc γ δ} {G}
        → Γ M₁.& Δ ⊢[ R ] P ∶ G → Γ M₂.& ⟦ Δ ⟧ᵛ ⊢[ R ] P ∶ ⟦ G ⟧
      typing⇒ (M₁.send fi gr etd td) =
        M₂.send (first-in⇒ fi) (ev⇒ gr) etd (typing⇒ td)
      typing⇒ (M₁.recv fi p∉ (c , H , ex) conts) =
        M₂.recv (first-in⇒ fi) p∉ (c , ⟦ H ⟧ , ev⇒ ex)
          λ gr′ →
            let Pr , br , td = conts (ev⇐ gr′)
            in Pr , br , typing⇒ td
      typing⇒ (M₁.skip std) = M₂.skip (skip/typing⇒ std)
      typing⇒ (M₁.forward td run) = M₂.forward (typing⇒ td) (skipᶜ⇒ run)
      typing⇒ (M₁.if etd ttd ftd) = M₂.if etd (typing⇒ ttd) (typing⇒ ftd)
      typing⇒ (M₁.rec td mg)      = M₂.rec (typing⇒ td) mg
      typing⇒ {Δ = Δ} (M₁.var {X = X} eq) =
        M₂.var (subst (M₂._≐ _) (sym (lookup-map X ⟦_⟧ Δ)) (~⇒ eq))
      typing⇒ (M₁.end out) =
        M₂.end λ inT →
          out (M₁.∈T⇒ᶜ (∈T⇐ (M₂.∈Tᶜ⇒ inT)))

      skip/typing⇒ :
        ∀ {γ δ ξ} {Γ : Vec _ γ} {Δ : Vec M₁.Cls δ} {Ξ : Vec M₁.Cls ξ}
          {R} {P : Proc γ δ} {G}
        → Γ M₁.& Δ & Ξ ⊢[ R ] P ∶ G → Γ M₂.& ⟦ Δ ⟧ᵛ & ⟦ Ξ ⟧ᵛ ⊢[ R ] P ∶ ⟦ G ⟧
      skip/typing⇒ (M₁.skip-main td) = M₂.skip-main (typing⇒ td)
      skip/typing⇒ (M₁.skip-step (α , H , st) ¬act k) =
        M₂.skip-step (α , ⟦ H ⟧ , step⇒ st)
          (λ { (H′ , β , st′ , own) → ¬act (_ , β , step⇐ st′ , own) })
          λ st′ → skip/typing⇒ (k (step⇐ st′))
      skip/typing⇒ (M₁.skip-cycle mem inT) =
        M₂.skip-cycle (∈ᵛ⇒ mem)
          (M₂.∈T⇒ᶜ (∈T⇒ (M₁.∈Tᶜ⇒ inT)))
