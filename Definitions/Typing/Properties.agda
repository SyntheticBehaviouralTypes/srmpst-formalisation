{-# OPTIONS --guardedness #-}

-- Typing at a class depends on the class only: both judgements are
-- invariant under `_≐_`, in the state and pointwise in the contexts.

open import Data.List using (List; [])
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_) renaming (lookup to lu)
import Data.Vec.Relation.Binary.Pointwise.Inductive as Pointwise
open Pointwise using (Pointwise; []; _∷_)
open import Data.Vec.Relation.Unary.Any using (Any; here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)
open import Definitions.Typing

module Definitions.Typing.Properties {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  open MPST wb

  -- ══════════════════════════════════════════════════════════════════
  --  Contexts, pointwise
  -- ══════════════════════════════════════════════════════════════════

  infix 4 _≐ᵛ_

  _≐ᵛ_ : ∀ {n} → Vec Cls n → Vec Cls n → Set
  _≐ᵛ_ = Pointwise _≐_

  ≐ᵛ-refl : ∀ {n}{Δ : Vec Cls n} → Δ ≐ᵛ Δ
  ≐ᵛ-refl = Pointwise.refl ≐-refl

  ∈ᵛ/≐ :
    ∀ {n}{Ξ Ξ′ : Vec Cls n}{G G′}
    → Ξ ≐ᵛ Ξ′ → G ≐ G′ → G ∈ᵛ Ξ → G′ ∈ᵛ Ξ′
  ∈ᵛ/≐ (e ∷ _)  G≐ (here x)  = here (≐-trans (≐-sym e) (≐-trans x G≐))
  ∈ᵛ/≐ (_ ∷ es) G≐ (there a) = there (∈ᵛ/≐ es G≐ a)

  -- ══════════════════════════════════════════════════════════════════
  --  Class steps and runs, along `≐`
  -- ══════════════════════════════════════════════════════════════════

  -- A step out of `G` is one out of every `G′ ≐ G`, to the same class.
  stepᶜ/≐ : ∀ {G G′ α H} → G ≐ G′ → G C.-< α >-> H → G′ C.-< α >-> H
  stepᶜ/≐ G≐ (H″ , H″~ , gr) =
    let K , gr′ , H″~K = ~L G≐ gr
    in K , ~trans (~sym H″~K) H″~ , gr′

  evᶜ/≐ :
    ∀ {G G′ P e H} → G ≐ G′ → G C.-<[ P ↦ e ]>-> H → G′ C.-<[ P ↦ e ]>-> H
  evᶜ/≐ G≐ (α , eq , st) = α , eq , stepᶜ/≐ G≐ st

  first-in/≐ :
    ∀ {r R G G′} → G ≐ G′ → r C.first-in (R , G) → r C.first-in (R , G′)
  first-in/≐ G≐ fi = first-in⇒ᶜ (first-in/~ G≐ (first-inᶜ⇒ fi))

  ∈Tᶜ/≐ : ∀ {R G G′} → G ≐ G′ → R C.∈T G → R C.∈T G′
  ∈Tᶜ/≐ G≐ inT = ∈T⇒ᶜ (∈~ G≐ (∈Tᶜ⇒ inT))

  -- A run ending at `G` ends at every `G′ ≐ G`, unless it is empty.
  run/≐ :
    ∀ {R G₀ G G′}
    → G₀ C.-[¬ R ]->* G → G ≐ G′
    → G₀ ≐ G′ ⊎ G₀ C.-[¬ R ]->* G′
  run/≐ ε e = inj₁ e
  run/≐ ((α , (H″ , H″~ , gr) , R∉) ◅ run) e with run/≐ run e
  ... | inj₁ e′   = inj₂ ((α , (H″ , ~trans H″~ e′ , gr) , R∉) ◅ ε)
  ... | inj₂ run′ = inj₂ ((α , (H″ , H″~ , gr) , R∉) ◅ run′)

  -- ══════════════════════════════════════════════════════════════════
  --  `≐`-invariance
  -- ══════════════════════════════════════════════════════════════════

  mutual

    skip-td/≐ :
      ∀ {γ δ ξ R P G G′}
        {Γ : Vec Sort γ}
        {Δ Δ′ : Vec Cls δ}
        {Ξ Ξ′ : Vec Cls ξ}
      → Δ ≐ᵛ Δ′ → Ξ ≐ᵛ Ξ′ → G ≐ G′
      → Γ & Δ  & Ξ  ⊢[ R ] P ∶ G
      → Γ & Δ′ & Ξ′ ⊢[ R ] P ∶ G′

    skip-td/≐ Δ~ Ξ~ G≐ (skip-main td) =
      skip-main (td/≐ Δ~ G≐ td)

    skip-td/≐ Δ~ Ξ~ G≐ (skip-cycle mem inT) =
      skip-cycle (∈ᵛ/≐ Ξ~ G≐ mem) (∈Tᶜ/≐ G≐ inT)

    skip-td/≐ Δ~ Ξ~ G≐ (skip-step (α , H , st) ¬act k) =
      skip-step
        (α , H , stepᶜ/≐ G≐ st)
        (λ { (H′ , β , st′ , own) →
             ¬act (H′ , β , stepᶜ/≐ (≐-sym G≐) st′ , own) })
        (λ st′ →
          skip-td/≐ Δ~ (G≐ ∷ Ξ~) ≐-refl (k (stepᶜ/≐ (≐-sym G≐) st′)))

    td/≐ :
      ∀ {γ δ R P G G′}
        {Γ : Vec Sort γ}
        {Δ Δ′ : Vec Cls δ}
      → Δ ≐ᵛ Δ′ → G ≐ G′
      → Γ & Δ  ⊢[ R ] P ∶ G
      → Γ & Δ′ ⊢[ R ] P ∶ G′

    td/≐ Δ~ G≐ (send fi gr etd td) =
      send (first-in/≐ G≐ fi) (evᶜ/≐ G≐ gr) etd (td/≐ Δ~ ≐-refl td)

    td/≐ Δ~ G≐ (recv fi p∉ (c , H , ex) conts) =
      recv (first-in/≐ G≐ fi) p∉ (c , H , evᶜ/≐ G≐ ex)
        λ gr′ →
          let Pℓ , br , td = conts (evᶜ/≐ (≐-sym G≐) gr′)
          in Pℓ , br , td/≐ Δ~ ≐-refl td

    td/≐ Δ~ G≐ (skip std) =
      skip (skip-td/≐ Δ~ [] G≐ std)

    td/≐ Δ~ G≐ (forward td run) with run/≐ run G≐
    ... | inj₁ G₀≐  = td/≐ Δ~ G₀≐ td
    ... | inj₂ run′ = forward (td/≐ Δ~ ≐-refl td) run′

    td/≐ Δ~ G≐ (let′ etd td) =
      let′ etd (td/≐ Δ~ G≐ td)

    td/≐ Δ~ G≐ (if etd ttd ftd) =
      if etd (td/≐ Δ~ G≐ ttd) (td/≐ Δ~ G≐ ftd)

    td/≐ Δ~ G≐ (end out) =
      end λ inT → out (∈Tᶜ/≐ (≐-sym G≐) inT)

    td/≐ Δ~ G≐ (rec td mg) =
      rec (td/≐ (G≐ ∷ Δ~) G≐ td) mg

    td/≐ Δ~ G≐ (var {X = X} eq) =
      var (≐-trans (≐-sym (Pointwise.lookup Δ~ X)) (≐-trans eq G≐))
