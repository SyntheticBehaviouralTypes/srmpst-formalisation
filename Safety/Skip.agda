{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (zero; suc)
open import Data.Vec
  using (Vec; []; _∷_; _++_)
  renaming (lookup to lu)
open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; cong)
open import Definitions.Typing

module Safety.Skip {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  open module M = MPST(wb)
  open M
  open M.Subst

  private
    variable
      γ δ ξ ξ′ : ℕ

  lookup/insert :
    ∀ {G H}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → ∃[ X ] lu (Ξ′ ++ (H ∷ Ξ)) X ~ G
    → H ~ G ⊎ ∃[ X′ ] lu (Ξ′ ++ Ξ) X′ ~ G

  lookup/insert {Ξ′ = []} (zero , eq) =
    inj₁ eq

  lookup/insert {Ξ′ = []} (suc X , eq) =
    inj₂ (X , eq)

  lookup/insert {Ξ′ = _ ∷ Ξ′} (zero , eq) =
    inj₂ (zero , eq)

  lookup/insert {Ξ′ = _ ∷ Ξ′} (suc X , eq)
    with lookup/insert {Ξ′ = Ξ′} (X , eq)
  ... | inj₁ eq′ =
    inj₁ eq′
  ... | inj₂ (X′ , eq′) =
    inj₂ (suc X′ , eq′)

  lookup/weaken-visited :
    ∀ {G H}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → ∃[ X ] lu (Ξ′ ++ Ξ) X ~ G
    → ∃[ X′ ] lu (Ξ′ ++ (H ∷ Ξ)) X′ ~ G

  lookup/weaken-visited {Ξ′ = []} (X , eq) =
    suc X , eq

  lookup/weaken-visited {Ξ′ = _ ∷ Ξ′} (zero , eq) =
    zero , eq

  lookup/weaken-visited {Ξ′ = _ ∷ Ξ′} (suc X , eq)
    with lookup/weaken-visited {Ξ′ = Ξ′} (X , eq)
  ... | X′ , eq′ =
    suc X′ , eq′

  skip/weaken-visited :
    ∀ {m G H PPr}
      {Leaf : NProc γ δ → Behav → Set}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → Leaf & Ξ′ ++ Ξ ⊢skip[ m ] PPr ∶ G
    → Leaf & Ξ′ ++ (H ∷ Ξ) ⊢skip[ m ] PPr ∶ G

  skip/weaken-visited (skip/main td) =
    skip/main td

  skip/weaken-visited {Ξ′ = Ξ′} (skip/step gr na ktd prod-gr) =
    skip/step gr na
      (λ gr′ → _ , skip/weaken-visited {Ξ′ = _ ∷ Ξ′} (ktd gr′ .proj₂))
      prod-gr

  skip/weaken-visited {H = H} {Ξ = Ξ} {Ξ′ = Ξ′} (skip/cycle eq) =
    skip/cycle
      (proj₂ (lookup/weaken-visited {H = H} {Ξ = Ξ} {Ξ′ = Ξ′} (_ , eq)))

  skip/bisim :
    ∀ {G G′ H P}
    → G′ ~ H
    → G -[¬ P ]->* G′
    → ∃[ H₀ ] (G ~ H₀) × (H₀ -[¬ P ]->* H)
  skip/bisim G~H skip/refl =
    _ , G~H , skip/refl
  skip/bisim G′~H (skip/step gr P∉α tr) =
    let _ , G₁~H₁ , H₁↝H = skip/bisim G′~H tr
        _ , G~H₀  , H₀↝H₁ = stepback/~ G₁~H₁ gr
    in _ , G~H₀ , skip/step H₀↝H₁ P∉α H₁↝H

  mode/transport :
    ∀ {G G′ G″ α}
    → (eq : G′ ≡ G″)
    → (mode : ∀ {H β} → G -< β >-> H → Mode)
    → (gr : G -< α >-> G′)
    → mode (subst (G -< α >->_) eq gr) ≡ mode gr
  mode/transport refl mode gr =
    refl

  selected-step-mode :
    ∀ {G G′ G″ α}
    → (mode : ∀ {H β} → G -< β >-> H → Mode)
    → (G~G′ : G ~ G′)
    → (gr : G -< α >-> G″)
    → mode gr ≡ mode (~R→ G~G′ (~L→ G~G′ gr))
  selected-step-mode {G = G} {α = α} mode G~G′ gr =
    trans
      (cong mode (~R-L/id′ G~G′ gr))
      (mode/transport
        (step-deterministic (~R→ G~G′ (~L→ G~G′ gr)) gr)
        mode
        (~R→ G~G′ (~L→ G~G′ gr)))

  mutual

    skip-td/bisim :
      ∀ {γ δ ξ m G G′ P Pr}
        {Γ : Vec Sort γ}
        {Δ Δ′ : Vec Behav δ}
        {Ξ Ξ′ : Vec Behav ξ}
      → Δ ~ᵛ Δ′
      → Ξ ~ᵛ Ξ′
      → G ~ G′
      → Γ & Δ  & Ξ  ⊢skip[ m ] P ◂ Pr ∶ G
      → Γ & Δ′ & Ξ′ ⊢skip[ m ] P ◂ Pr ∶ G′

    skip-td/bisim Δ~Δ′ Ξ~Ξ′ G~G′ (skip/main td) =
      skip/main (td/bisim Δ~Δ′ G~G′ td)

    skip-td/bisim Δ~Δ′ Ξ~Ξ′ G~G′ (skip/step gr na ktd prod-gr) =
      skip/step
        (~L→ G~G′ gr)
        (na ∘ ~R→ G~G′)
        (λ gr′ →
          _ ,
          skip-td/bisim
            Δ~Δ′
            (~ᵛ/∷ G~G′ Ξ~Ξ′)
            (~R→~ G~G′ gr′)
            (ktd (~R→ G~G′ gr′) .proj₂))
        (subst (_≡ prod) (selected-step-mode (proj₁ ∘ ktd) G~G′ gr) prod-gr)

    skip-td/bisim Δ~Δ′ Ξ~Ξ′ G~G′ (skip/cycle eq) =
      skip/cycle (~trans (lookup/~ᵛ Ξ~Ξ′ _ eq) G~G′)

    td/bisim :
      ∀ {γ δ G G′ P Pr}
        {Γ : Vec Sort γ}
        {Δ Δ′ : Vec Behav δ}
      → Δ ~ᵛ Δ′
      → G ~ G′
      → Γ & Δ  ⊢p P ◂ Pr ∶ G
      → Γ & Δ′ ⊢p P ◂ Pr ∶ G′

    td/bisim Δ~Δ′ G~G′ (t/send gr etd ptd) =
      t/send
        (~L→ G~G′ gr)
        etd
        (td/bisim Δ~Δ′ (~L→~ G~G′ gr) ptd)

    td/bisim Δ~Δ′ G~G′ (t/recv gr conts) =
      t/recv
        (~L→ G~G′ gr)
        (λ gr′ →
          td/bisim
            Δ~Δ′
            (~R→~ G~G′ gr′)
            (conts (~R→ G~G′ gr′)))

    td/bisim Δ~Δ′ G~G′ (t/skip std) =
      t/skip (skip-td/bisim Δ~Δ′ ~ᵛ/[] G~G′ std)

    td/bisim Δ~Δ′ G~G′ (t/unskip tr ptd) =
      let _ , H~G′ , tr′ = skip/bisim G~G′ tr
      in t/unskip tr′ (td/bisim Δ~Δ′ H~G′ ptd)

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

  skip-leaf/bisim :
    ∀ {γ δ ξ m G G′ PPr}
      {Leaf : NProc γ δ → Behav → Set}
      {Ξ Ξ′ : Vec Behav ξ}
    → (∀ {PPr G G′} → G ~ G′ → Leaf PPr G → Leaf PPr G′)
    → Ξ ~ᵛ Ξ′
    → G ~ G′
    → Leaf & Ξ ⊢skip[ m ] PPr ∶ G
    → Leaf & Ξ′ ⊢skip[ m ] PPr ∶ G′

  skip-leaf/bisim leaf/bisim _ G~G′ (skip/main td) =
    skip/main (leaf/bisim G~G′ td)

  skip-leaf/bisim leaf/bisim Ξ~Ξ′ G~G′ (skip/step gr na ktd prod-gr) =
    skip/step
      (~L→ G~G′ gr)
      (na ∘ ~R→ G~G′)
      (λ gr′ →
        _ ,
        skip-leaf/bisim
          leaf/bisim
          (~ᵛ/∷ G~G′ Ξ~Ξ′)
          (~R→~ G~G′ gr′)
          (ktd (~R→ G~G′ gr′) .proj₂))
      (subst (_≡ prod) (selected-step-mode (proj₁ ∘ ktd) G~G′ gr) prod-gr)

  skip-leaf/bisim _ Ξ~Ξ′ G~G′ (skip/cycle eq) =
    skip/cycle (~trans (lookup/~ᵛ Ξ~Ξ′ _ eq) G~G′)

  skip/unfold-cycle :
    ∀ {γ δ ξ ξ′ m m′ G H PPr}
      {Leaf : NProc γ δ → Behav → Set}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → (∀ {PPr G G′} → G ~ G′ → Leaf PPr G → Leaf PPr G′)
    → Leaf & Ξ′ ++ Ξ ⊢skip[ m ] PPr ∶ G
    → Leaf & Ξ′ ++ (G ∷ Ξ) ⊢skip[ m′ ] PPr ∶ H
    → ∃[ n ] (Leaf & Ξ′ ++ Ξ ⊢skip[ n ] PPr ∶ H)
      × (m′ ≡ prod → n ≡ prod)

  skip/unfold-cycle leaf/bisim base (skip/main td) =
    prod , skip/main td , λ _ → refl

  skip/unfold-cycle {Ξ = Ξ} {Ξ′ = Ξ′} leaf/bisim base
    (skip/step {G = H} gr na ktd prod-gr) =
    let base′ = skip/weaken-visited {H = H} {Ξ = Ξ′ ++ Ξ} {Ξ′ = []} base
        unfold =
          λ {β H′} (gr′ : H -< β >-> H′) →
            skip/unfold-cycle {Ξ′ = H ∷ Ξ′} leaf/bisim base′ (ktd gr′ .proj₂)
    in
    prod ,
    skip/step gr na
      (λ gr′ → unfold gr′ .proj₁ , unfold gr′ .proj₂ .proj₁)
      (unfold gr .proj₂ .proj₂ prod-gr) ,
    λ _ → refl

  skip/unfold-cycle {Ξ = Ξ} {Ξ′ = Ξ′} leaf/bisim base (skip/cycle {X = X} eq)
    with lookup/insert {Ξ = Ξ} {Ξ′ = Ξ′} (X , eq)
  ... | inj₁ G~H =
    _ ,
    skip-leaf/bisim leaf/bisim ~ᵛ-refl G~H base ,
    λ ()
  ... | inj₂ (_ , eq′) =
    nonprod ,
    skip/cycle eq′ ,
    λ ()
