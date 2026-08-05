{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (zero; suc)
open import Data.Vec
  using (Vec; []; _∷_; _++_)
  renaming (lookup to lu)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; subst)
open import Definitions.Typing

module Definitions.Typing.Properties {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
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
    ∀ {G H PPr}
      {Leaf : NProc γ δ → Behav → Set}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → Leaf & Ξ′ ++ Ξ ⊢skip PPr ∶ G
    → Leaf & Ξ′ ++ (H ∷ Ξ) ⊢skip PPr ∶ G

  skip/weaken-visited (skip/main td) =
    skip/main td

  skip/weaken-visited {Ξ′ = Ξ′} (skip/step gr na ktd) =
    skip/step gr na
      (λ gr′ → skip/weaken-visited {Ξ′ = _ ∷ Ξ′} (ktd gr′))

  skip/weaken-visited {H = H} {Ξ = Ξ} {Ξ′ = Ξ′} (skip/cycle eq inT) =
    skip/cycle
      (proj₂ (lookup/weaken-visited {H = H} {Ξ = Ξ} {Ξ′ = Ξ′} (_ , eq)))
      inT

  ~mainLeaf/weaken-visited :
    ∀ {G H PPr PPr′ G′}
      {Leaf : NProc γ δ → Behav → Set}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
      {leaf : Leaf PPr′ G′}
    → (std : Leaf & Ξ′ ++ Ξ ⊢skip PPr ∶ G)
    → MainLeaf leaf (skip/weaken-visited {H = H} {Ξ = Ξ} {Ξ′ = Ξ′} std)
    → MainLeaf leaf std
  ~mainLeaf/weaken-visited (skip/main td) main/here =
    main/here
  ~mainLeaf/weaken-visited (skip/step gr na ktd) (main/step gr′ leaf) =
    main/step gr′ (~mainLeaf/weaken-visited (ktd gr′) leaf)
  ~mainLeaf/weaken-visited (skip/cycle _ _) ()

  -- Backward transport: relates the trace's *target* to `H` and must
  -- produce a new source bisimilar to `G`, so this calls `stepback/~*`
  -- (generalizing `stepback/~` from a step to a run) rather than
  -- `tr-transport`. `allP` rides along unchanged either way — it's a fact
  -- about the trace's labels alone.
  skip/bisim :
    ∀ {G G′ H P}
    → G′ ~ H
    → G -[¬ P ]->* G′
    → ∃[ H₀ ] (G ~ H₀) × (H₀ -[¬ P ]->* H)
  skip/bisim G′~H (αs , tr , allP) =
    let H₀ , G~H₀ , tr′ = stepback/~* G′~H tr
    in H₀ , G~H₀ , (αs , tr′ , allP)

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

  -- Backward companion to `skip/bisim`: transport a trace along a `~` on
  -- its *source*.  (Moved here from `Normalise.agda`, where it sat only
  -- because that is where it was first needed — it mentions neither
  -- `⊢head` nor `⊢p`.)
  skip/bisim-back :
    ∀ {G G′ H′ P}
    → G ~ G′
    → G′ -[¬ P ]->* H′
    → ∃[ H ] (G -[¬ P ]->* H) × (H ~ H′)
  skip/bisim-back G~G′ (αs , tr , allP) =
    let H , tr′ , H′~H = tr-transport (~sym G~G′) tr
    in H , (αs , tr′ , allP) , ~sym H′~H

  skip-leaf/bisim :
    ∀ {γ δ ξ G G′ PPr}
      {Leaf : NProc γ δ → Behav → Set}
      {Ξ Ξ′ : Vec Behav ξ}
    → (∀ {PPr G G′} → G ~ G′ → Leaf PPr G → Leaf PPr G′)
    → Ξ ~ᵛ Ξ′
    → G ~ G′
    → Leaf & Ξ ⊢skip PPr ∶ G
    → Leaf & Ξ′ ⊢skip PPr ∶ G′

  skip-leaf/bisim leaf/bisim _ G~G′ (skip/main td) =
    skip/main (leaf/bisim G~G′ td)

  skip-leaf/bisim leaf/bisim Ξ~Ξ′ G~G′ (skip/step gr na ktd) =
    skip/step
      (~L→ G~G′ gr)
      (na ∘ ~R→ G~G′)
      (λ gr′ →
        skip-leaf/bisim
          leaf/bisim
          (~ᵛ/∷ G~G′ Ξ~Ξ′)
          (~R→~ G~G′ gr′)
          (ktd (~R→ G~G′ gr′)))

  skip-leaf/bisim _ Ξ~Ξ′ G~G′ (skip/cycle eq inT) =
    skip/cycle (~trans (lookup/~ᵛ Ξ~Ξ′ _ eq) G~G′) (∈~ G~G′ inT)

  record ~Leaf
    {γ δ}
    (Leaf : NProc γ δ → Behav → Set)
    (PPr : NProc γ δ)
    (H : Behav)
    : Set
    where

    constructor ~leaf

    field
      {G}  : Behav
      leaf : Leaf PPr G
      G~H  : G ~ H

  ~MainLeaf :
    ∀ {γ δ ξ}
      {Leaf : NProc γ δ → Behav → Set}
      {Ξ : Vec Behav ξ}
      {PPr G PPr′ G′}
    → Leaf PPr′ G′
    → (~Leaf Leaf) & Ξ ⊢skip PPr ∶ G
    → Set
  ~MainLeaf {G′ = G′} leaf std =
    ∃[ H ] ∃[ G′~H ] MainLeaf (~leaf {H = H} leaf G′~H) std

  skip/remember-leaves :
    ∀ {γ δ ξ G PPr}
      {Leaf : NProc γ δ → Behav → Set}
      {Ξ : Vec Behav ξ}
    → Leaf & Ξ ⊢skip PPr ∶ G
    → ~Leaf Leaf & Ξ ⊢skip PPr ∶ G

  skip/remember-leaves (skip/main leaf) =
    skip/main (~leaf leaf ~refl)

  skip/remember-leaves (skip/step gr na ktd) =
    skip/step gr na
      (skip/remember-leaves ∘ ktd)

  skip/remember-leaves (skip/cycle eq inT) =
    skip/cycle eq inT

  ~leaf/trans :
    ∀ {γ δ}
      {Leaf : NProc γ δ → Behav → Set}
      {PPr G H}
    → G ~ H
    → ~Leaf Leaf PPr G
    → ~Leaf Leaf PPr H
  ~leaf/trans G~H (~leaf leaf K~G) =
    ~leaf leaf (~trans K~G G~H)

  unfold-skip-cycle :
    ∀ {γ δ ξ ξ′ G H PPr}
      {Leaf : NProc γ δ → Behav → Set}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → ~Leaf Leaf & Ξ′ ++ Ξ ⊢skip PPr ∶ G
    → ~Leaf Leaf & Ξ′ ++ (G ∷ Ξ) ⊢skip PPr ∶ H
    → ~Leaf Leaf & Ξ′ ++ Ξ ⊢skip PPr ∶ H

  unfold-skip-cycle base (skip/main td) =
    skip/main td

  unfold-skip-cycle {Ξ = Ξ} {Ξ′ = Ξ′} base
    (skip/step {G = H} gr na ktd) =
    let base′ = skip/weaken-visited {H = H} {Ξ = Ξ′ ++ Ξ} {Ξ′ = []} base
    in
    skip/step gr na
      (λ gr′ → unfold-skip-cycle {Ξ′ = H ∷ Ξ′} base′ (ktd gr′))

  unfold-skip-cycle {Ξ = Ξ} {Ξ′ = Ξ′} base
    (skip/cycle {X = X} eq inT)
    with lookup/insert {Ξ = Ξ} {Ξ′ = Ξ′} (X , eq)
  ... | inj₁ G~H =
    skip-leaf/bisim ~leaf/trans ~ᵛ-refl G~H base
  ... | inj₂ (_ , eq′) =
    skip/cycle eq′ inT

  skip/transport-leaf~ :
    ∀ {γ δ ξ G PPr}
      {Leaf : NProc γ δ → Behav → Set}
      {Ξ : Vec Behav ξ}
    → (∀ {PPr G G′} → G ~ G′ → Leaf PPr G → Leaf PPr G′)
    → ~Leaf Leaf & Ξ ⊢skip PPr ∶ G
    → Leaf & Ξ ⊢skip PPr ∶ G
  skip/transport-leaf~ f (skip/main (~leaf td G~H)) = skip/main (f G~H td)
  skip/transport-leaf~ f (skip/step gr na ktd) =
    skip/step gr na (skip/transport-leaf~ f ∘ ktd)
  skip/transport-leaf~ f (skip/cycle lu P∈G) = skip/cycle lu P∈G

  -- `skip/transport-leaf~` only resolves the bisim at the eventual
  -- `skip/main` leaf (`f G~H td`); it never inspects `td` further, so any
  -- `MainLeaf` of its output corresponds to a `~MainLeaf` of the input at
  -- the very same underlying `td` — existential in the found leaf, since
  -- (unlike `skip/weaken-visited`/`skip-leaf/bisim`) the leaf's own *type*
  -- changes (`~Leaf Leaf` to plain `Leaf`), so there's nothing to keep
  -- literally fixed across the two directions the way `leaf` is fixed in
  -- `~mainLeaf/bisim-back`/`-intro`.
  -- `skip/weaken-visited` (only touches `Ξ`) and `skip/transport-leaf~`
  -- (only touches leaves) operate on disjoint aspects of a `⊢skip` tree,
  -- so they commute up to `MainLeaf` — same style as
  -- `mainLeaf/remember-leaves/weaken-visited` above, just for
  -- `transport-leaf~` instead of `remember-leaves`.
  mainLeaf/transport-leaf~/weaken-visited :
    ∀ {γ δ ξ ξ′ G H PPr K}
      {Leaf : NProc γ δ → Behav → Set}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
      {td : Leaf PPr K}
    → (f : ∀ {PPr G G′} → G ~ G′ → Leaf PPr G → Leaf PPr G′)
    → (std : ~Leaf Leaf & Ξ′ ++ Ξ ⊢skip PPr ∶ G)
    → MainLeaf td (skip/transport-leaf~ f (skip/weaken-visited {H = H} {Ξ = Ξ} {Ξ′ = Ξ′} std))
    → MainLeaf td (skip/weaken-visited {H = H} {Ξ = Ξ} {Ξ′ = Ξ′} (skip/transport-leaf~ f std))
  mainLeaf/transport-leaf~/weaken-visited f (skip/main x) main/here =
    main/here
  mainLeaf/transport-leaf~/weaken-visited {Ξ′ = Ξ′} f (skip/step gr na ktd) (main/step gr′ leaf) =
    main/step gr′ (mainLeaf/transport-leaf~/weaken-visited {Ξ′ = _ ∷ Ξ′} f (ktd gr′) leaf)
  mainLeaf/transport-leaf~/weaken-visited f (skip/cycle _ _) ()

  skip/unfold-cycle :
    ∀ {γ δ ξ ξ′ G H PPr}
      {Leaf : NProc γ δ → Behav → Set}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → (∀ {PPr G G′} → G ~ G′ → Leaf PPr G → Leaf PPr G′)
    → Leaf & Ξ′ ++ Ξ ⊢skip PPr ∶ G
    → Leaf & Ξ′ ++ (G ∷ Ξ) ⊢skip PPr ∶ H
    → Leaf & Ξ′ ++ Ξ ⊢skip PPr ∶ H
  skip/unfold-cycle leaf/bisim base td =
    skip/transport-leaf~ leaf/bisim
      (unfold-skip-cycle
        (skip/remember-leaves base)
        (skip/remember-leaves td))

