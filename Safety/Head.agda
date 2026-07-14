{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup)
open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; sym)
open import Definitions

module Safety.Head {N : ℕ}{B : BTheory N}(BP : BT-Prop B) where
  private
    module M = Definitions.MPST BP
  open M
  open M.Subst
  open import Safety.Skip BP
  open import Typing.Substitution BP

  mutual

    t/if/inv :
      ∀ {G P E Pr Pr′ Pr″}
      → Pr ≡ ifp E then Pr′ else Pr″
      → [] & [] ⊢p P ◂ Pr ∶ G
      → ([] ⊢e E ∶ s/bool)
      × ([] & [] ⊢p P ◂ Pr′ ∶ G)
      × ([] & [] ⊢p P ◂ Pr″ ∶ G)

    t/if/inv refl (t/if e ptd′ ptd″) =
      e , ptd′ , ptd″

    t/if/inv refl (t/skip std) =
      proj₁ (skip/if/inv std) refl ,
      t/skip (proj₁ (proj₂ (skip/if/inv std))) ,
      t/skip (proj₂ (proj₂ (skip/if/inv std)))

    t/if/inv refl (t/unskip tr td)
      with t/if/inv refl td
    ... | e , ptd′ , ptd″ =
      e ,
      t/unskip tr ptd′ ,
      t/unskip tr ptd″

    skip/if/inv :
      ∀ {ξ m}
        {Ξ : Vec Behav ξ}
        {G P E Pr Pr′}
      → [] & [] & Ξ ⊢skip[ m ] P ◂ ifp E then Pr else Pr′ ∶ G
      → (m ≡ prod → [] ⊢e E ∶ s/bool)
      × ([] & [] & Ξ ⊢skip[ m ] P ◂ Pr ∶ G)
      × ([] & [] & Ξ ⊢skip[ m ] P ◂ Pr′ ∶ G)
    skip/if/inv (skip/main td) =
      (λ _ → proj₁ (t/if/inv refl td)) ,
      skip/main (proj₁ (proj₂ (t/if/inv refl td))) ,
      skip/main (proj₂ (proj₂ (t/if/inv refl td)))
    skip/if/inv (skip/step gr na ktd prod-gr) =
      (λ _ → proj₁ (skip/if/inv (proj₂ (ktd gr))) prod-gr) ,
      skip/step gr na
        (λ gr′ → proj₁ (ktd gr′) ,
          proj₁ (proj₂ (skip/if/inv (proj₂ (ktd gr′)))))
        prod-gr ,
      skip/step gr na
        (λ gr′ → proj₁ (ktd gr′) ,
          proj₂ (proj₂ (skip/if/inv (proj₂ (ktd gr′)))))
        prod-gr
    skip/if/inv (skip/cycle eq) =
      (λ ()) ,
      skip/cycle eq ,
      skip/cycle eq

  mutual

    t/rec/unfold :
      ∀ {G P Pr}
      → [] & [] ⊢p P ◂ rec Pr ∶ G
      → [] & [] ⊢p P ◂ unfold/proc Pr ∶ G

    t/rec/unfold (t/rec mmg ptd) =
      typing/subst-proc (t/rec mmg ptd) ptd

    t/rec/unfold (t/skip std) =
      t/skip (skip/rec/unfold std)

    t/rec/unfold (t/unskip tr td) =
      t/unskip tr (t/rec/unfold td)

    skip/rec/unfold :
      ∀ {ξ m}
        {Ξ : Vec Behav ξ}
        {G P Pr}
      → [] & [] & Ξ ⊢skip[ m ] P ◂ rec Pr ∶ G
      → [] & [] & Ξ ⊢skip[ m ] P ◂ unfold/proc Pr ∶ G
    skip/rec/unfold (skip/main td) =
      skip/main (t/rec/unfold td)
    skip/rec/unfold (skip/step gr na ktd prod-gr) =
      skip/step gr na
        (λ gr′ → proj₁ (ktd gr′) , skip/rec/unfold (proj₂ (ktd gr′)))
        prod-gr
    skip/rec/unfold (skip/cycle eq) =
      skip/cycle eq

  mutual

    head/bisim :
      ∀ {γ PPr G G′}
        {Γ : Vec Sort γ}
      → G ~ G′
      → Γ ⊢head PPr ∶ G
      → Γ ⊢head PPr ∶ G′

    head/bisim G~G′ (h/send gr etd head) =
      h/send
        (~L→ G~G′ gr)
        etd
        (head/bisim (~L→~ G~G′ gr) head)

    head/bisim G~G′ (h/recv gr conts) =
      h/recv (~L→ G~G′ gr) λ gr′ →
        head/bisim
          (~R→~ G~G′ gr′)
          (conts (~R→ G~G′ gr′))

    head/bisim G~G′ (h/skip std) =
      h/skip (hskip/bisim ~ᵛ/[] G~G′ std)

    head/bisim G~G′ (h/if etd head₁ head₂) =
      h/if etd (head/bisim G~G′ head₁) (head/bisim G~G′ head₂)

    head/bisim G~G′ (h/rec tr guarded td) =
      let _ , H~H′ , tr′ = skip/bisim G~G′ tr
      in
      h/rec
        tr′
        guarded
        (td/bisim (~ᵛ/∷ H~H′ ~ᵛ/[]) H~H′ td)

    head/bisim G~G′ (h/end done) =
      h/end (done ∘ ∈~ (~sym G~G′))

    hskip/bisim :
      ∀ {γ ξ m PPr G G′}
        {Γ : Vec Sort γ}
        {Ξ Ξ′ : Vec Behav ξ}
      → Ξ ~ᵛ Ξ′
      → G ~ G′
      → Γ & Ξ ⊢hskip[ m ] PPr ∶ G
      → Γ & Ξ′ ⊢hskip[ m ] PPr ∶ G′

    hskip/bisim Ξ~Ξ′ G~G′ (skip/main head) =
      skip/main (head/bisim G~G′ head)

    hskip/bisim Ξ~Ξ′ G~G′ (skip/step gr na ktd prod-gr) =
      skip/step
        (~L→ G~G′ gr)
        (na ∘ ~R→ G~G′)
        (λ gr′ →
          _ ,
          hskip/bisim
            (~ᵛ/∷ G~G′ Ξ~Ξ′)
            (~R→~ G~G′ gr′)
            (ktd (~R→ G~G′ gr′) .proj₂))
        (subst (_≡ prod) (selected-step-mode (proj₁ ∘ ktd) G~G′ gr) prod-gr)

    hskip/bisim Ξ~Ξ′ G~G′ (skip/cycle eq) =
      skip/cycle (~trans (lookup/~ᵛ Ξ~Ξ′ _ eq) G~G′)

  hskip/unfold-cycle :
    ∀ {γ m m′ G H P Pr}
      {Γ : Vec Sort γ}
    → Γ & [] ⊢hskip[ m ] P ◂ Pr ∶ G
    → Γ & G ∷ [] ⊢hskip[ m′ ] P ◂ Pr ∶ H
    → ∃[ n ] (Γ & [] ⊢hskip[ n ] P ◂ Pr ∶ H)
      × (m′ ≡ prod → n ≡ prod)
  hskip/unfold-cycle =
    skip/unfold-cycle {Ξ = []} {Ξ′ = []} head/bisim

  ptd/bisim :
    ∀ {γ G G′ PPr}
      {Γ : Vec Sort γ}
    → G ~ G′
    → Γ & [] ⊢p PPr ∶ G
    → Γ & [] ⊢p PPr ∶ G′
  ptd/bisim {PPr = P ◂ Pr} =
    td/bisim ~ᵛ-refl

  pskip/unfold :
    ∀ {γ ξ ξ′ m m′ G H P Pr}
      {Γ : Vec Sort γ}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → Γ & [] & Ξ′ ++ Ξ ⊢skip[ m ] P ◂ Pr ∶ G
    → Γ & [] & Ξ′ ++ G ∷ Ξ ⊢skip[ m′ ] P ◂ Pr ∶ H
    → ∃[ n ]
        (Γ & [] & Ξ′ ++ Ξ ⊢skip[ n ] P ◂ Pr ∶ H)
      × (m′ ≡ prod → n ≡ prod)
  pskip/unfold {P = P} {Pr = Pr} =
    skip/unfold-cycle {PPr = P ◂ Pr} ptd/bisim

  pskip/unfold-top :
    ∀ {γ m G H P Pr}
      {Γ : Vec Sort γ}
    → Γ & [] & [] ⊢skip[ prod ] P ◂ Pr ∶ G
    → Γ & [] & G ∷ [] ⊢skip[ m ] P ◂ Pr ∶ H
    → Γ & [] & [] ⊢skip[ prod ] P ◂ Pr ∶ H
  pskip/unfold-top base inner
    with pskip/unfold {Ξ = []} {Ξ′ = []} base inner
  ... | prod , unfolded , _ =
    unfolded
  ... | nonprod , skip/cycle {X = ()} _ , _

  LeafHead :
    ∀ {γ ξ}
      {Γ : Vec Sort γ}
      {Ξ : Vec Behav ξ}
      {m : Mode}
      {P : Part}
      {Pr : Proc γ 0}
      {G : Behav}
    → Γ & [] & Ξ ⊢skip[ m ] P ◂ Pr ∶ G
    → Set
  LeafHead {Γ = Γ} {P = P} {Pr = Pr} std =
    ∀ {H H′}
      {td : Γ & [] ⊢p P ◂ Pr ∶ H}
    → MainLeaf td std
    → H -[¬ P ]->* H′
    → Γ ⊢head P ◂ Pr ∶ H′

  skip/bisim-back :
    ∀ {G G′ H′ P}
    → G ~ G′
    → G′ -[¬ P ]->* H′
    → ∃[ H ] (G -[¬ P ]->* H) × (H ~ H′)
  skip/bisim-back G~G′ skip/refl =
    _ , skip/refl , G~G′
  skip/bisim-back G~G′ (skip/step gr P∉α tr) =
    let _ , tr′ , H~H′ = skip/bisim-back (~R→~ G~G′ gr) tr
    in _ , skip/step (~R→ G~G′ gr) P∉α tr′ , H~H′

  mainLeaf/weaken-visited :
    ∀ {γ ξ ξ′ m P Pr G H K}
      {Γ : Vec Sort γ}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
      {td : Γ & [] ⊢p P ◂ Pr ∶ K}
    → (std : Γ & [] & Ξ′ ++ Ξ ⊢skip[ m ] P ◂ Pr ∶ G)
    → MainLeaf td (skip/weaken-visited {H = H} {Ξ = Ξ} {Ξ′ = Ξ′} std)
    → MainLeaf td std
  mainLeaf/weaken-visited (skip/main td) main/here =
    main/here
  mainLeaf/weaken-visited (skip/step gr na ktd ok) (main/step gr′ leaf) =
    let _ , std′ = ktd gr′
    in main/step gr′ (mainLeaf/weaken-visited std′ leaf)
  mainLeaf/weaken-visited (skip/cycle _) ()

  leafHead/bisim :
    ∀ {γ ξ m P Pr G G′}
      {Γ : Vec Sort γ}
      {Ξ Ξ′ : Vec Behav ξ}
    → (Ξ~Ξ′ : Ξ ~ᵛ Ξ′)
    → (G~G′ : G ~ G′)
    → (std : Γ & [] & Ξ ⊢skip[ m ] P ◂ Pr ∶ G)
    → LeafHead std
    → LeafHead (skip-leaf/bisim ptd/bisim Ξ~Ξ′ G~G′ std)
  leafHead/bisim Ξ~Ξ′ G~G′ (skip/main td) leafHead main/here tr =
    let _ , tr′ , H~H′ = skip/bisim-back G~G′ tr
    in head/bisim H~H′ (leafHead main/here tr′)
  leafHead/bisim Ξ~Ξ′ G~G′ (skip/step _ _ ktd _)
    leafHead (main/step gr′ leaf) tr =
    let gr″ = ~R→ G~G′ gr′
        _ , std′ = ktd gr″
    in
    leafHead/bisim
      (~ᵛ/∷ G~G′ Ξ~Ξ′)
      (~R→~ G~G′ gr′)
      std′
      (leafHead ∘ main/step gr″)
      leaf
      tr
  leafHead/bisim Ξ~Ξ′ G~G′ (skip/cycle eq) leafHead ()

  skip/head :
    ∀ {γ ξ P Pr G m}
      {Γ : Vec Sort γ}
      {Ξ : Vec Behav ξ}
    → (std : Γ & [] & Ξ ⊢skip[ m ] P ◂ Pr ∶ G)
    → LeafHead std
    → Γ & Ξ ⊢hskip[ m ] P ◂ Pr ∶ G
  skip/head (skip/main td) leafHead =
    skip/main (leafHead main/here skip/refl)
  skip/head (skip/step gr na ktd ok) leafHead =
    skip/step gr na
      (λ gr′ →
        let mode′ , std′ = ktd gr′
        in
        mode′ ,
        skip/head
          std′
          (leafHead ∘ main/step gr′))
      ok
  skip/head (skip/cycle eq) _ =
    skip/cycle eq

  leafHead/unfold :
    ∀ {γ ξ ξ′ m m′ G H P Pr}
      {Γ : Vec Sort γ}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → (base : Γ & [] & Ξ′ ++ Ξ ⊢skip[ m ] P ◂ Pr ∶ G)
    → LeafHead base
    → (inner : Γ & [] & Ξ′ ++ G ∷ Ξ ⊢skip[ m′ ] P ◂ Pr ∶ H)
    → LeafHead inner
    → let _ , unfolded , _ =
            pskip/unfold {Ξ = Ξ} {Ξ′ = Ξ′} base inner
      in
      LeafHead unfolded
  leafHead/unfold base baseHead (skip/main td) innerHead main/here =
    innerHead main/here
  leafHead/unfold {Ξ = Ξ} {Ξ′ = Ξ′}
    base baseHead
    (skip/step {G = H} gr na ktd ok)
    innerHead
    (main/step gr′ leaf)
    tr =
    let base′ = skip/weaken-visited {H = H} {Ξ = Ξ′ ++ Ξ} {Ξ′ = []} base
        base′Head : LeafHead base′
        base′Head = baseHead ∘ mainLeaf/weaken-visited base
        _ , inner′ = ktd gr′
    in
    leafHead/unfold
      {Ξ′ = H ∷ Ξ′}
      base′
      base′Head
      inner′
      (innerHead ∘ main/step gr′)
      leaf
      tr
  leafHead/unfold {Ξ = Ξ} {Ξ′ = Ξ′}
    base baseHead (skip/cycle {X = X} eq) innerHead leaf tr
    with lookup/insert {Ξ = Ξ} {Ξ′ = Ξ′} (X , eq)
  ... | inj₁ G~H =
    leafHead/bisim ~ᵛ-refl G~H base baseHead leaf tr
  ... | inj₂ (_ , eq′) with leaf
  ...   | ()

  leafHead/unfold-top :
    ∀ {γ m G H P Pr}
      {Γ : Vec Sort γ}
    → (base : Γ & [] & [] ⊢skip[ prod ] P ◂ Pr ∶ G)
    → LeafHead base
    → (inner : Γ & [] & G ∷ [] ⊢skip[ m ] P ◂ Pr ∶ H)
    → LeafHead inner
    → LeafHead (pskip/unfold-top base inner)
  leafHead/unfold-top base baseHead inner innerHead
    with pskip/unfold {Ξ = []} {Ξ′ = []} base inner
      | leafHead/unfold {Ξ = []} {Ξ′ = []}
          base
          baseHead
          inner
          innerHead
  ... | prod , unfolded , _ | unfoldedHead =
    unfoldedHead
  ... | nonprod , skip/cycle {X = ()} _ , _ | _

  cancel/unskip :
    ∀ {γ P Pr G G′}
      {Γ : Vec Sort γ}
    → G -[¬ P ]->* G′
    → (std : Γ & [] & [] ⊢skip[ prod ] P ◂ Pr ∶ G)
    → LeafHead std
    → Γ ⊢head P ◂ Pr ∶ G′

  cancel/unskip skip/refl (skip/main _) leafHead =
    leafHead main/here skip/refl
  cancel/unskip skip/refl std@(skip/step _ _ _ _) leafHead =
    h/skip (skip/head std leafHead)
  cancel/unskip tr@(skip/step _ _ _) (skip/main td) leafHead =
    leafHead main/here tr
  cancel/unskip (skip/step gr _ tr) std@(skip/step _ _ ktd _) leafHead =
    let _ , inner = ktd gr
        std′ = pskip/unfold-top std inner
        leafHead′ =
          leafHead/unfold-top std leafHead
            inner
            (leafHead ∘ main/step gr)
    in
    cancel/unskip tr std′ leafHead′

  mutual

    mainLeaf/head :
      ∀ {γ ξ m P Pr G}
        {Γ : Vec Sort γ}
        {Ξ : Vec Behav ξ}
      → (std : Γ & [] & Ξ ⊢skip[ m ] P ◂ Pr ∶ G)
      → LeafHead std

    mainLeaf/head (skip/main td) main/here tr =
      td/head td tr
    mainLeaf/head (skip/step _ _ ktd _) (main/step gr′ leaf) =
      let _ , std′ = ktd gr′
      in mainLeaf/head std′ leaf
    mainLeaf/head (skip/cycle _) ()

    td/head :
      ∀ {γ P Pr G G′}
        {Γ : Vec Sort γ}
      → Γ & [] ⊢p P ◂ Pr ∶ G
      → G -[¬ P ]->* G′
      → Γ ⊢head P ◂ Pr ∶ G′

    td/head (t/send gr etd td) tr =
      let _ , gr′ , tr′ = skip/advance tr gr (∈S refl)
      in h/send gr′ etd (td/head td tr′)
    td/head (t/recv gr conts) tr =
      let _ , gr′ , _ = skip/advance tr gr (∈R refl)
      in
      h/recv gr′ λ gr″ →
        let _ , gr₀ , tr₀ = branch/before tr gr gr″
        in td/head (conts gr₀) tr₀
    td/head (t/skip std) tr =
      cancel/unskip tr std (mainLeaf/head std)
    td/head (t/unskip tr′ td) tr =
      td/head td (skip/cat tr′ tr)
    td/head (t/if etd ttd ftd) tr =
      h/if etd (td/head ttd tr) (td/head ftd tr)
    td/head (t/rec guarded td) tr =
      h/rec tr guarded td
    td/head (t/var {X = ()} _)
    td/head (t/end done) tr =
      h/end (done ∘ skip/∈T-back tr)
