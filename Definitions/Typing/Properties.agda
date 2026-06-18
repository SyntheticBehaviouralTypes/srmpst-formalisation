{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
open import Data.Product using (_,_)
open import Function using (_∘_)
open import Definitions.Typing

module Definitions.Typing.Properties {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  open MPST wb

  mutual

    skip-td/bisim :
      ∀ {γ δ ξ G G′ P Pr}
        {Γ : Vec Sort γ}
        {Δ Δ′ : Vec Behav δ}
        {Ξ Ξ′ : Vec Behav ξ}
      → Δ ~ᵛ Δ′
      → Ξ ~ᵛ Ξ′
      → G ~ G′
      → Γ & Δ  & Ξ  ⊢skip P ◂ Pr ∶ G
      → Γ & Δ′ & Ξ′ ⊢skip P ◂ Pr ∶ G′

    skip-td/bisim Δ~Δ′ Ξ~Ξ′ G~G′ (skip/main td) =
      skip/main (td/bisim Δ~Δ′ G~G′ td)

    skip-td/bisim Δ~Δ′ Ξ~Ξ′ G~G′ (skip/step gr na ktd) =
      skip/step
        (~L→ G~G′ gr)
        (na ∘ ~R→ G~G′)
        (λ gr′ →
          skip-td/bisim
            Δ~Δ′
            (~ᵛ/∷ G~G′ Ξ~Ξ′)
            (~R→~ G~G′ gr′)
            (ktd (~R→ G~G′ gr′)))

    skip-td/bisim Δ~Δ′ Ξ~Ξ′ G~G′ (skip/cycle eq inT) =
      skip/cycle (~trans (lookup/~ᵛ Ξ~Ξ′ _ eq) G~G′) (∈~ G~G′ inT)

    td/bisim :
      ∀ {γ δ G G′ P Pr}
        {Γ : Vec Sort γ}
        {Δ Δ′ : Vec Behav δ}
      → Δ ~ᵛ Δ′
      → G ~ G′
      → Γ & Δ  ⊢p P ◂ Pr ∶ G
      → Γ & Δ′ ⊢p P ◂ Pr ∶ G′

    td/bisim Δ~Δ′ G~G′ (t/send Q∈ foc (α , eq , gr) etd ptd) =
      t/send Q∈
        (focus/~ G~G′ foc)
        (α , eq , ~L→ G~G′ gr)
        etd
        (td/bisim Δ~Δ′ (~L→~ G~G′ gr) ptd)

    td/bisim Δ~Δ′ G~G′ (t/recv R∈ foc (α , eq , gr , fr) conts) =
      t/recv R∈
        (focus/~ G~G′ foc)
        (α , eq , ~L→ G~G′ gr , fr)
        (λ { (α′ , eq′ , gr′ , fr′) →
          td/bisim
            Δ~Δ′
            (~R→~ G~G′ gr′)
            (conts (α′ , eq′ , ~R→ G~G′ gr′ , fr′)) })

    td/bisim Δ~Δ′ G~G′ (t/skip std) =
      t/skip (skip-td/bisim Δ~Δ′ ~ᵛ/[] G~G′ std)

    td/bisim Δ~Δ′ G~G′ (t/unskip tr eq ptd) =
      t/unskip tr (~trans eq G~G′) (td/bisim Δ~Δ′ ~refl ptd)

    td/bisim Δ~Δ′ G~G′ (t/if etd ttd ftd) =
      t/if
        etd
        (td/bisim Δ~Δ′ G~G′ ttd)
        (td/bisim Δ~Δ′ G~G′ ftd)

    td/bisim Δ~Δ′ G~G′ (t/rec guarded td) =
      t/rec guarded (td/bisim (~ᵛ/∷ G~G′ Δ~Δ′) G~G′ td)

    td/bisim Δ~Δ′ G~G′ (t/var eq) =
      t/var (~trans (lookup/~ᵛ Δ~Δ′ _ eq) G~G′)

    td/bisim Δ~Δ′ G~G′ (t/end done) =
      t/end (done ∘ ∈~ (~sym G~G′))

  -- Rewriting a `⊢skip` tree's leaf family, needed only at `PPr`.
  skip/map :
    ∀ {γ δ ξ}{L₁ L₂ : NProc γ δ → Behav → Set}
      {Ξ : Vec Behav ξ}{PPr G}
    → (∀ {H} → L₁ PPr H → L₂ PPr H)
    → L₁ & Ξ ⊢skip PPr ∶ G
    → L₂ & Ξ ⊢skip PPr ∶ G

  skip/map f (skip/main x) =
    skip/main (f x)

  skip/map f (skip/step gr na ktd) =
    skip/step gr na (λ gr′ → skip/map f (ktd gr′))

  skip/map f (skip/cycle eq inT) =
    skip/cycle eq inT
