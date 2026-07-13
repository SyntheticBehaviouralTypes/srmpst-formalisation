{-# OPTIONS --guardedness #-}

open import Data.Empty using (⊥; ⊥-elim)

open import Data.Nat using (ℕ; _+_; _<_; _≤_; _⊔_; s≤s; suc)
open import Data.Nat.Induction using (<-wellFounded)

open import Data.Nat.Properties
  using
    ( +-mono-<-≤
    ; +-mono-≤
    ; +-mono-≤-<
    ; <⇒≤
    ; ≤-refl
    ; m≤n⇒m≤n⊔o
    ; m≤n⇒m≤o⊔n
    )

open import Function using (_∘_)

open import Induction.WellFounded using (Acc; acc)

open import Data.Fin
  using (Fin; zero)
  renaming (_≟_ to _≟f_; suc to fsuc)

open import Data.Vec
  using (Vec; []; _∷_; _++_; _[_]=_; _[_]≔_; lookup; tabulate)

open import Data.Vec.Properties
  using (lookup∘tabulate; lookup∘update; lookup∘update′)

open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe.Base using (Maybe; just; nothing)

open import Relation.Nullary using (¬_; yes; no)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; sym)

open import Utils.Fin using (lookup-get; reflect-lookup)
open import Definitions

import SubstitutionProperties

module Safety {N : ℕ}{B : BTheory N}(BP : BT-Prop B) where
  open module SP = SubstitutionProperties(BP)
  open SP.M
  open SP.M.Subst

  td/lookup :
    ∀ {M G P Pr}
    → ⊢s M ∶ G
    → M [ P ]= Pr
    → [] & [] ⊢p P ◂ Pr ∶ G
  td/lookup {P = P} ts luP with ts P
  ... | ptd rewrite reflect-lookup luP = ptd

  ⊢s-update :
    ∀ (M : Session) {G P Pr}
    → ⊢s M ∶ G
    → [] & [] ⊢p P ◂ Pr ∶ G
    → ⊢s M [ P ]≔ Pr ∶ G

  ⊢s-update M {P = P} {Pr = Pr} M⊢G Pr⊢G Q
    with Q ≟f P
  ... | yes refl
    rewrite lookup∘update P M Pr =
    Pr⊢G
  ... | no Q≢P
    rewrite lookup∘update′ Q≢P M Pr =
    M⊢G Q

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
      proc-subst-lemma (t/rec mmg ptd) ptd

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

  pskip/unfold/prod :
    ∀ {γ ξ ξ′ m m′ G H P Pr}
      {Γ : Vec Sort γ}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → (base : Γ & [] & Ξ′ ++ Ξ ⊢skip[ m ] P ◂ Pr ∶ G)
    → (inner : Γ & [] & Ξ′ ++ G ∷ Ξ ⊢skip[ m′ ] P ◂ Pr ∶ H)
    → m′ ≡ prod
    → let mode , _ , _ =
            pskip/unfold {Ξ = Ξ} {Ξ′ = Ξ′} base inner
      in
      mode ≡ prod
  pskip/unfold/prod base inner =
    let _ , _ , prod-preserved = pskip/unfold base inner
    in prod-preserved

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
      h/send
        (skip/advance-step tr gr (∈S refl))
        etd
        (td/head td (skip/advance-trace tr gr (∈S refl)))
    td/head (t/recv gr conts) tr =
      h/recv (skip/advance-step tr gr (∈R refl)) λ gr″ →
        td/head
          (conts (branch/before-step tr gr gr″))
          (branch/before-trace tr gr gr″)
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

  ⊢s-comm-update :
    ∀ (M : Session)
      {G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {Pr Pr′}
    → (gr : G -< P ⟶ Q # i < S > >-> G′)
    → ⊢s M ∶ G
    → [] & [] ⊢p P ◂ Pr  ∶ G′
    → [] & [] ⊢p Q ◂ Pr′ ∶ G′
    → ⊢s M [ P ]≔ Pr [ Q ]≔ Pr′ ∶ G′

  ⊢s-comm-update M {P = P} {Q = Q} {Pr = Pr} {Pr′ = Pr′} gr M⊢G Ptd Qtd R
    with R ≟f Q
  ... | yes refl
    rewrite lookup∘update Q (M [ P ]≔ Pr) Pr′ =
    Qtd
  ... | no R≢Q
    rewrite lookup∘update′ R≢Q (M [ P ]≔ Pr) Pr′
    with R ≟f P
  ...   | yes refl
    rewrite lookup∘update P M Pr =
    Ptd
  ...   | no R≢P
    rewrite lookup∘update′ R≢P M Pr =
    head/typing (td/head (M⊢G R) (skip/one gr (R≢P , R≢Q)))

  t/send/cont-branch :
    ∀ {G G′ G″ P Q I}
      {i : Fin (suc I)}
      {S T : Sort}
      {E : Exp 0}
      {Pr : Proc 0 0}
    → [] ⊢e E ∶ T
    → [] ⊢head P ◂ Pr ∶ G″
    → G -< P ⟶ Q # i < S > >-> G′
    → G -< P ⟶ Q # i < T > >-> G″
    → [] ⊢e E ∶ S × [] ⊢head P ◂ Pr ∶ G′
  t/send/cont-branch etd td gr gr₀
    with step-sort-deterministic gr gr₀
  ... | refl
    rewrite step-deterministic gr gr₀ =
    etd , td

  mutual

    t/send/cont-head :
      ∀ {G G′ P Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {E : Exp 0}
        {Pr : Proc 0 0}
      → [] ⊢head P ◂ Q ! i < E >∙ Pr ∶ G
      → G -< P ⟶ Q # i < S > >-> G′
      → [] ⊢e E ∶ S × [] & [] ⊢p P ◂ Pr ∶ G′

    t/send/cont-head (h/send gr₀ etd td′) gr =
      let etd′ , hd′ = t/send/cont-branch etd td′ gr gr₀
      in etd′ , head/typing hd′
    t/send/cont-head (h/skip std) gr =
      t/send/cont-hskip std gr

    t/send/cont-hskip :
      ∀ {G G′ P Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {E : Exp 0}
        {Pr : Proc 0 0}
      → [] & [] ⊢hskip[ prod ] P ◂ Q ! i < E >∙ Pr ∶ G
      → G -< P ⟶ Q # i < S > >-> G′
      → [] ⊢e E ∶ S × [] & [] ⊢p P ◂ Pr ∶ G′

    t/send/cont-hskip (skip/main head) gr =
      t/send/cont-head head gr
    t/send/cont-hskip (skip/step gr′ na ktd mode-gr) gr =
      ⊥-elim (∉c→¬∈c (na gr) (∈S refl))

  t/send/cont :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {E : Exp 0}
      {Pr : Proc 0 0}
    → [] & [] ⊢p P ◂ Q ! i < E >∙ Pr ∶ G
    → G -< P ⟶ Q # i < S > >-> G′
    → [] ⊢e E ∶ S × [] & [] ⊢p P ◂ Pr ∶ G′

  t/send/cont td =
    t/send/cont-head (td/head td skip/refl)

  mutual

    t/comm/ready/head :
      ∀ {G P Q I}
        {i : Fin (suc I)}
        {E : Exp 0}
        {Pr : Proc 0 0}
        {S : Vec Sort (suc I)}
        {Br : Vec (Proc 1 0) (suc I)}
      → [] ⊢head P ◂ Q ! i < E >∙ Pr ∶ G
      → [] ⊢head Q ◂ Σ P ？[ S ]· Br ∶ G
      → ∃[ T ] ∃[ G′ ] G -< P ⟶ Q # i < T > >-> G′

    t/comm/ready/head (h/send gr _ _) _ =
      _ , _ , gr

    t/comm/ready/head (h/skip stdP) headQ =
      t/comm/ready/hskip-hskip stdP refl (skip/main headQ)

    t/comm/ready/hskip-hskip :
      ∀ {ξ m m′ G P Q I}
        {Ξ : Vec Behav ξ}
        {i : Fin (suc I)}
        {E : Exp 0}
        {Pr : Proc 0 0}
        {S : Vec Sort (suc I)}
        {Br : Vec (Proc 1 0) (suc I)}
      → [] & Ξ ⊢hskip[ m′ ] P ◂ Q ! i < E >∙ Pr ∶ G
      → m′ ≡ prod
      → [] & [] ⊢hskip[ m ] Q ◂ Σ P ？[ S ]· Br ∶ G
      → ∃[ T ] ∃[ G′ ] G -< P ⟶ Q # i < T > >-> G′

    t/comm/ready/hskip-hskip (skip/main headP) refl (skip/main headQ) =
      t/comm/ready/head headP headQ

    t/comm/ready/hskip-hskip (skip/main headP) refl (skip/step gr na ktd x) =
      t/comm/ready/head headP (h/skip (skip/step gr na ktd x))

    t/comm/ready/hskip-hskip
      (skip/step gr na ktd x)
      refl
      (skip/main (h/recv x₁ x₂)) =
      ⊥-elim (_∉c_.∉S (na x₁) refl)

    t/comm/ready/hskip-hskip
      (skip/step grα P∉G headP prodP)
      refl
      (skip/main (h/skip stdQ)) =
      t/comm/ready/hskip-hskip
        (skip/step grα P∉G headP prodP)
        refl
        stdQ

    t/comm/ready/hskip-hskip
      (skip/step grα P∉G headP prodP)
      refl
      (skip/step grQ Q∉G headQ modeQ) =
      let _ , stdQ , _ =
            hskip/unfold-cycle
              (skip/main (h/skip (skip/step grQ Q∉G headQ modeQ)))
              (headQ grα .proj₂)
          T , _ , grβ =
            t/comm/ready/hskip-hskip
              (headP grα .proj₂)
              prodP
              stdQ
          G′ , gr =
            no-new-comm/step
              grα
              (P∉G grα)
              (Q∉G grα)
              grβ
      in T , G′ , gr

  t/comm/ready :
    ∀ {G P Q I}
      {i : Fin (suc I)}
      {E : Exp 0}
      {Pr : Proc 0 0}
      {S : Vec Sort (suc I)}
      {Br : Vec (Proc 1 0) (suc I)}
    → [] & [] ⊢p P ◂ Q ! i < E >∙ Pr ∶ G
    → [] & [] ⊢p Q ◂ Σ P ？[ S ]· Br ∶ G
    → ∃[ T ] ∃[ G′ ] G -< P ⟶ Q # i < T > >-> G′

  t/comm/ready ptd qtd =
    t/comm/ready/head
      (td/head ptd skip/refl)
      (td/head qtd skip/refl)


  mutual

    t/recv/cont-head :
      ∀ {G G′ P Q I}
        {i : Fin (suc I)}
        {T : Sort}
        {S : Vec Sort (suc I)}
        {Br : Vec (Proc 1 0) (suc I)}
      → [] ⊢head Q ◂ Σ P ？[ S ]· Br ∶ G
      → (gr : G -< P ⟶ Q # i < T > >-> G′)
      → (T ∷ []) & [] ⊢p Q ◂ lookup Br i ∶ G′

    t/recv/cont-head (h/recv _ conts) gr =
      head/typing (conts gr)
    t/recv/cont-head (h/skip std) gr =
      t/recv/cont-hskip std gr

    t/recv/cont-hskip :
      ∀ {G G′ P Q I}
        {i : Fin (suc I)}
        {T : Sort}
        {S : Vec Sort (suc I)}
        {Br : Vec (Proc 1 0) (suc I)}
      → [] & [] ⊢hskip[ prod ] Q ◂ Σ P ？[ S ]· Br ∶ G
      → (gr : G -< P ⟶ Q # i < T > >-> G′)
      → (T ∷ []) & [] ⊢p Q ◂ lookup Br i ∶ G′

    t/recv/cont-hskip (skip/main head) gr =
      t/recv/cont-head head gr
    t/recv/cont-hskip (skip/step gr′ na ktd mode-gr) gr =
      ⊥-elim (∉c→¬∈c (na gr) (∈R refl))

  t/recv/cont :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {T : Sort}
      {S : Vec Sort (suc I)}
      {Br : Vec (Proc 1 0) (suc I)}
    → [] & [] ⊢p Q ◂ Σ P ？[ S ]· Br ∶ G
    → (gr : G -< P ⟶ Q # i < T > >-> G′)
    → (T ∷ []) & [] ⊢p Q ◂ lookup Br i ∶ G′

  t/recv/cont td =
    t/recv/cont-head (td/head td skip/refl)


  preservation/τ :
    ∀ {G M'}
    → (M : Session)
    → ⊢s M ∶ G
    → M [ nothing ]⇒ M'
    → ⊢s M' ∶ G

  preservation/τ M M⊢G (s/if/true P Ptt e⇓true)
    with t/if/inv refl (td/lookup M⊢G Ptt)
  ... | _ , ptd-then , _ =
    ⊢s-update M M⊢G ptd-then

  preservation/τ M M⊢G (s/if/false P Ptt e⇓false)
    with t/if/inv refl (td/lookup M⊢G Ptt)
  ... | _ , _ , ptd-else =
    ⊢s-update M M⊢G ptd-else

  preservation/τ M M⊢G (s/rec P Prec) =
    ⊢s-update M M⊢G (t/rec/unfold (td/lookup M⊢G Prec))


  preservation/sync :
    ∀ (M : Session)
      {G P Q I}
      {i : Fin (suc I)}
      {S : Vec Sort (suc I)}
      {E V Pr Br}
    → ⊢s M ∶ G
    → [] & [] ⊢p P ◂ Q ! i < E >∙ Pr ∶ G
    → [] & [] ⊢p Q ◂ Σ P ？[ S ]· Br ∶ G
    → E ⇓ V
    → ∃[ G′ ]
        G -< P ⟶ Q # i < sort/value V > >-> G′
      × ⊢s M [ P ]≔ Pr [ Q ]≔ ([ val V / zero ]e lookup Br i) ∶ G′

  preservation/sync M M⊢G ptd qtd e⇓v
    with t/comm/ready ptd qtd
  ... | T , G′ , gr =
    let etd , ptd′ = t/send/cont ptd gr
        vtd = exp-pres etd e⇓v
    in
    G′ ,
    subst
      (λ U → _ -< _ ⟶ _ # _ < U > >-> _)
      (sort/value-typed vtd)
      gr ,
    ⊢s-comm-update M gr M⊢G ptd′
      (proc-subst-lemma-expr
        (te/val vtd)
        (t/recv/cont qtd gr))


  preservation/comm :
    ∀ (M : Session)
      {G M' α}
    → ⊢s M ∶ G
    → M [ just α ]⇒ M'
    → ∃[ G' ] G -< α >-> G' × ⊢s M' ∶ G'

  preservation/comm M std (s/comm P Q Psnd e⇓v Precv) =
    preservation/sync
      M
      std
      (td/lookup std Psnd)
      (td/lookup std Precv)
      e⇓v

  Step : Behav → Maybe Action → Behav → Set
  Step G (just α) G′ = G -< α >-> G′
  Step G nothing G′ = G ≡ G′

  preservation :
    ∀ {G M' α}
      (M : Session)
    → ⊢s M ∶ G
    → M [ α ]⇒ M'
    → ∃[ G' ] Step G α G' × ⊢s M' ∶ G'
  preservation {α = just x} M td sr =
    preservation/comm M td sr
  preservation {G = G} {α = nothing} M td sr =
    _ , refl , preservation/τ M td sr

  preservation/τ* :
    ∀ {G M M'}
    → ⊢s M ∶ G
    → M τ⇒ M'
    → ⊢s M' ∶ G

  preservation/τ* M⊢G s/zero =
    M⊢G
  preservation/τ* M⊢G (s/more st tr) =
    preservation/τ* (preservation/τ _ M⊢G st) tr


  message-guarded/proc-subst :
    ∀ {γ δ X}
      {Pr′ : Proc γ δ}
      {Pr : Proc γ (suc δ)}
    → MessageGuarded Pr
    → MessageGuarded ([ Pr′ / X ]pr Pr)
  message-guarded/proc-subst mg/send =
    mg/send
  message-guarded/proc-subst mg/recv =
    mg/recv
  message-guarded/proc-subst (mg/if guarded₁ guarded₂) =
    mg/if
      (message-guarded/proc-subst guarded₁)
      (message-guarded/proc-subst guarded₂)

  message-guarded/unfold :
    ∀ {γ}
      {Pr : Proc γ 1}
    → MessageGuarded Pr
    → MessageGuarded (unfold/proc Pr)
  message-guarded/unfold =
    message-guarded/proc-subst

  mutual

    message-guarded/∈T/head :
      ∀ {γ G P Pr}
        {Γ : Vec Sort γ}
      → MessageGuarded Pr
      → Γ ⊢head P ◂ Pr ∶ G
      → P ∈T G
    message-guarded/∈T/head mg/send (h/send gr _ _) =
      in/send gr
    message-guarded/∈T/head mg/send (h/skip std) =
      message-guarded/∈T/hskip mg/send std refl
    message-guarded/∈T/head mg/recv (h/recv gr _) =
      in/recv gr
    message-guarded/∈T/head mg/recv (h/skip std) =
      message-guarded/∈T/hskip mg/recv std refl
    message-guarded/∈T/head (mg/if mg₁ _) (h/if _ head₁ _) =
      message-guarded/∈T/head mg₁ head₁
    message-guarded/∈T/head guarded@(mg/if _ _) (h/skip std) =
      message-guarded/∈T/hskip guarded std refl

    message-guarded/∈T/hskip :
      ∀ {γ ξ m G P Pr}
        {Γ : Vec Sort γ}
        {Ξ : Vec Behav ξ}
      → MessageGuarded Pr
      → Γ & Ξ ⊢hskip[ m ] P ◂ Pr ∶ G
      → m ≡ prod
      → P ∈T G
    message-guarded/∈T/hskip guarded (skip/main head) _ =
      message-guarded/∈T/head guarded head
    message-guarded/∈T/hskip guarded (skip/step gr _ ktd mode-gr) _ =
      in/later gr (message-guarded/∈T/hskip guarded (ktd gr .proj₂) mode-gr)
    message-guarded/∈T/hskip guarded (skip/cycle _) ()

  message-guarded/∈T :
    ∀ {γ G P Pr}
      {Γ : Vec Sort γ}
    → MessageGuarded Pr
    → Γ & [] ⊢p P ◂ Pr ∶ G
    → P ∈T G
  message-guarded/∈T guarded td =
    message-guarded/∈T/head guarded (td/head td skip/refl)

  mutual

    not-in-type/done/head :
      ∀ {G P Pr}
      → P ∉T G
      → [] ⊢head P ◂ Pr ∶ G
      → done/proc Pr
    not-in-type/done/head P∉G (h/send gr _ _) =
      ⊥-elim (P∉G (in/send gr))
    not-in-type/done/head P∉G (h/recv gr _) =
      ⊥-elim (P∉G (in/recv gr))
    not-in-type/done/head P∉G (h/skip std) =
      not-in-type/done/hskip P∉G std refl
    not-in-type/done/head P∉G (h/if _ head₁ head₂) =
      done-if
        (not-in-type/done/head P∉G head₁)
        (not-in-type/done/head P∉G head₂)
    not-in-type/done/head P∉G htd@(h/rec _ guarded _) =
      ⊥-elim
        (P∉G
          (message-guarded/∈T
            (message-guarded/unfold guarded)
            (t/rec/unfold (head/typing htd))))
    not-in-type/done/head _ (h/end _) =
      done-∅

    not-in-type/done/hskip :
      ∀ {ξ m G P Pr}
        {Ξ : Vec Behav ξ}
      → P ∉T G
      → [] & Ξ ⊢hskip[ m ] P ◂ Pr ∶ G
      → m ≡ prod
      → done/proc Pr
    not-in-type/done/hskip P∉G (skip/main head) _ =
      not-in-type/done/head P∉G head
    not-in-type/done/hskip P∉G (skip/step gr _ ktd mode-gr) _ =
      not-in-type/done/hskip
        (P∉G ∘ in/later gr)
        (ktd gr .proj₂)
        mode-gr
    not-in-type/done/hskip P∉G (skip/cycle _) ()

  not-in-type/done :
    ∀ {G P Pr}
    → P ∉T G
    → [] & [] ⊢p P ◂ Pr ∶ G
    → done/proc Pr
  not-in-type/done P∉G td =
    not-in-type/done/head P∉G (td/head td skip/refl)

  data SessionStatus
    (M : Session)
    (G : Behav)
    {I : ℕ}
    (Ps : Vec Part I)
    : Set
    where

    ss/step :
      ∀ {α G′}
      → G -< α >-> G′
      → SessionStatus M G Ps

    ss/if :
      ∀ {P E Pr Pr′}
      → [] ⊢e E ∶ s/bool
      → M [ P ]= ifp E then Pr else Pr′
      → SessionStatus M G Ps

    ss/rec :
      ∀ {P Pr}
      → M [ P ]= rec Pr
      → SessionStatus M G Ps

    ss/end :
      (∀ i → lookup Ps i ∉T G)
      → SessionStatus M G Ps

  session/status/cons-end :
    ∀ {I M G P}
      {Ps : Vec Part I}
    → P ∉T G
    → SessionStatus M G Ps
    → SessionStatus M G (P ∷ Ps)
  session/status/cons-end _ (ss/step gr) =
    ss/step gr
  session/status/cons-end _ (ss/if etd proc≡) =
    ss/if etd proc≡
  session/status/cons-end _ (ss/rec proc≡) =
    ss/rec proc≡
  session/status/cons-end P∉G (ss/end done) =
    ss/end λ
      { zero     → P∉G
      ; (fsuc i) → done i
      }

  mutual

    head/session-status :
      ∀ {I M G P Pr}
        {Ps : Vec Part I}
      → SessionStatus M G Ps
      → M [ P ]= Pr
      → [] ⊢head P ◂ Pr ∶ G
      → SessionStatus M G (P ∷ Ps)
    head/session-status _ _ (h/send gr _ _) =
      ss/step gr
    head/session-status _ _ (h/recv gr _) =
      ss/step gr
    head/session-status tail proc≡ (h/skip std) =
      hskip/session-status tail proc≡ std
    head/session-status _ proc≡ (h/if etd _ _) =
      ss/if etd proc≡
    head/session-status _ proc≡ (h/rec _ _ _) =
      ss/rec proc≡
    head/session-status tail _ (h/end done) =
      session/status/cons-end done tail

    hskip/session-status :
      ∀ {I ξ M G P Pr}
        {Ps : Vec Part I}
        {Ξ : Vec Behav ξ}
      → SessionStatus M G Ps
      → M [ P ]= Pr
      → [] & Ξ ⊢hskip[ prod ] P ◂ Pr ∶ G
      → SessionStatus M G (P ∷ Ps)
    hskip/session-status tail proc≡ (skip/main head) =
      head/session-status tail proc≡ head
    hskip/session-status _ _ (skip/step gr _ _ _) =
      ss/step gr

  session/status :
    ∀ {I M G}
    → (Ps : Vec Part I)
    → ⊢s M ∶ G
    → SessionStatus M G Ps

  session/status [] M⊢G =
    ss/end λ ()

  session/status {M = M} (P ∷ Ps) M⊢G =
    head/session-status
      (session/status Ps M⊢G)
      (lookup-get refl)
      (td/head (M⊢G P) skip/refl)


  all-parts/end :
    ∀ {G}
    → (∀ i → lookup (tabulate (λ P → P)) i ∉T G)
    → ∀ P → P ∉T G
  all-parts/end ended P P∈G =
    ended P
      (subst
        (λ Q → Q ∈T _)
        (sym (lookup∘tabulate (λ Q → Q) P))
        P∈G)

  if/progress :
    ∀ {M P E Pr Pr′}
    → [] ⊢e E ∶ s/bool
    → M [ P ]= ifp E then Pr else Pr′
    → ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′
  if/progress {P = P} etd proc≡
    with eval-bool etd
  ... | inj₁ e⇓true =
    nothing , _ , s/if/true P proc≡ e⇓true
  ... | inj₂ e⇓false =
    nothing , _ , s/if/false P proc≡ e⇓false

  mutual

    receiver/head-progress :
      ∀ {M G G′ P Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {E : Exp 0}
        {Pr : Proc 0 0}
        {QPr : Proc 0 0}
      → ⊢s M ∶ G
      → [] ⊢e E ∶ S
      → G -< P ⟶ Q # i < S > >-> G′
      → M [ P ]= Q ! i < E >∙ Pr
      → M [ Q ]= QPr
      → [] ⊢head Q ◂ QPr ∶ G
      → ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′
    receiver/head-progress M⊢G etd gr send≡ recv≡ (h/send gr′ _ _)
      with recv-overlap⇒same-comm gr gr′ (∈S refl)
    ... | refl =
      ⊥-elim (sender≢receiver gr refl)
    receiver/head-progress {P = P} {Q = Q} {i = i}
      M⊢G etd gr send≡ recv≡ (h/recv gr′ _)
      with recv-overlap⇒same-comm gr gr′ (∈R refl)
    ... | refl
      with step-arity-deterministic gr gr′
    ...   | refl
      with eval-exp etd
    ...     | V , e⇓v =
      just (P ⟶ Q # i < sort/value V >) , _ ,
      s/comm P Q send≡ e⇓v recv≡
    receiver/head-progress M⊢G etd gr send≡ recv≡ (h/skip std) =
      receiver/hskip-progress M⊢G etd gr send≡ recv≡ std
    receiver/head-progress M⊢G etd gr send≡ recv≡ (h/if etd′ _ _) =
      if/progress etd′ recv≡
    receiver/head-progress {Q = Q} M⊢G etd gr send≡ recv≡
      (h/rec _ _ _) =
      nothing , _ , s/rec Q recv≡
    receiver/head-progress M⊢G etd gr send≡ recv≡ (h/end done) =
      ⊥-elim (done (in/recv gr))

    receiver/hskip-progress :
      ∀ {ξ M G G′ P Q I}
        {Ξ : Vec Behav ξ}
        {i : Fin (suc I)}
        {S : Sort}
        {E : Exp 0}
        {Pr : Proc 0 0}
        {QPr : Proc 0 0}
      → ⊢s M ∶ G
      → [] ⊢e E ∶ S
      → G -< P ⟶ Q # i < S > >-> G′
      → M [ P ]= Q ! i < E >∙ Pr
      → M [ Q ]= QPr
      → [] & Ξ ⊢hskip[ prod ] Q ◂ QPr ∶ G
      → ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′
    receiver/hskip-progress M⊢G etd gr send≡ recv≡ (skip/main head) =
      receiver/head-progress M⊢G etd gr send≡ recv≡ head
    receiver/hskip-progress M⊢G etd gr send≡ recv≡
      (skip/step _ Q∉G _ _) =
      ⊥-elim (∉c→¬∈c (Q∉G gr) (∈R refl))

    sender/head-progress :
      ∀ {M G G′ P Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {Pr : Proc 0 0}
      → ⊢s M ∶ G
      → G -< P ⟶ Q # i < S > >-> G′
      → M [ P ]= Pr
      → [] ⊢head P ◂ Pr ∶ G
      → ∃[ β ] ∃[ M′ ] M [ β ]⇒ M′
    sender/head-progress M⊢G gr send≡ (h/send {Q = Q′} gr′ etd _) =
      receiver/head-progress
        M⊢G
        etd
        gr′
        send≡
        (lookup-get refl)
        (td/head (M⊢G Q′) skip/refl)
    sender/head-progress M⊢G gr send≡ (h/recv gr′ _)
      with recv-overlap⇒same-comm gr′ gr (∈S refl)
    ... | refl =
      ⊥-elim (sender≢receiver gr refl)
    sender/head-progress M⊢G gr send≡ (h/skip std) =
      sender/hskip-progress M⊢G gr send≡ std
    sender/head-progress M⊢G gr send≡ (h/if etd _ _) =
      if/progress etd send≡
    sender/head-progress {P = P} M⊢G gr send≡ (h/rec _ _ _) =
      nothing , _ , s/rec P send≡
    sender/head-progress M⊢G gr send≡ (h/end done) =
      ⊥-elim (done (in/send gr))

    sender/hskip-progress :
      ∀ {ξ M G G′ P Q I}
        {Ξ : Vec Behav ξ}
        {i : Fin (suc I)}
        {S : Sort}
        {Pr : Proc 0 0}
      → ⊢s M ∶ G
      → G -< P ⟶ Q # i < S > >-> G′
      → M [ P ]= Pr
      → [] & Ξ ⊢hskip[ prod ] P ◂ Pr ∶ G
      → ∃[ β ] ∃[ M′ ] M [ β ]⇒ M′
    sender/hskip-progress M⊢G gr send≡ (skip/main head) =
      sender/head-progress M⊢G gr send≡ head
    sender/hskip-progress M⊢G gr send≡ (skip/step _ P∉G _ _) =
      ⊥-elim (∉c→¬∈c (P∉G gr) (∈S refl))

  step/progress :
    ∀ {M G G′ α}
    → ⊢s M ∶ G
    → G -< α >-> G′
    → ∃[ β ] ∃[ M′ ] M [ β ]⇒ M′
  step/progress {α = P ⟶ Q # i < S >} M⊢G gr =
    sender/head-progress
      M⊢G
      gr
      (lookup-get refl)
      (td/head (M⊢G P) skip/refl)

  progress :
    ∀ {M G}
    → ⊢s M ∶ G
    → done M ⊎ ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′

  progress {M = M} M⊢G
    with session/status (tabulate (λ P → P)) M⊢G
  ... | ss/step gr =
    inj₂ (step/progress M⊢G gr)
  ... | ss/if etd proc≡ =
    inj₂ (if/progress etd proc≡)
  ... | ss/rec proc≡ =
    inj₂ (nothing , _ , s/rec _ proc≡)
  ... | ss/end ended =
    inj₁ λ P →
      not-in-type/done (all-parts/end ended P) (M⊢G P)

  stepper :
    ∀ {M M′}
    → M [ nothing ]⇒ M′
    → Part
  stepper (s/if/true P _ _) =
    P
  stepper (s/if/false P _ _) =
    P
  stepper (s/rec P _) =
    P

  τ-depth/proc :
    ∀ {γ δ}
    → Proc γ δ
    → ℕ
  τ-depth/proc (_ ! _ < _ >∙ _) =
    0
  τ-depth/proc (Σ _ ？[ _ ]· _) =
    0
  τ-depth/proc (ifp _ then Pr else Pr′) =
    suc (τ-depth/proc Pr ⊔ τ-depth/proc Pr′)
  τ-depth/proc (rec Pr) =
    suc (τ-depth/proc Pr)
  τ-depth/proc (v _) =
    0
  τ-depth/proc ∅ =
    0

  τ-depth/message-subst :
    ∀ {γ δ X}
      {Pr  : Proc γ (suc δ)}
      {Pr′ : Proc γ δ}
    → MessageGuarded Pr
    → τ-depth/proc ([ Pr′ / X ]pr Pr) ≡ τ-depth/proc Pr
  τ-depth/message-subst mg/send =
    refl
  τ-depth/message-subst mg/recv =
    refl
  τ-depth/message-subst {X = X} {Pr′ = Pr′} (mg/if mg₁ mg₂)
    rewrite τ-depth/message-subst {X = X} {Pr′ = Pr′} mg₁
          | τ-depth/message-subst {X = X} {Pr′ = Pr′} mg₂ =
    refl

  τ-depth/unfold :
    ∀ {γ}
      {Pr : Proc γ 1}
    → MessageGuarded Pr
    → τ-depth/proc (unfold/proc Pr) ≡ τ-depth/proc Pr
  τ-depth/unfold {Pr = Pr} guarded =
    τ-depth/message-subst {X = zero} {Pr′ = rec Pr} guarded

  τ-depth/if-then :
    ∀ {γ δ E}
      {Pr Pr′ : Proc γ δ}
    → τ-depth/proc Pr < τ-depth/proc (ifp E then Pr else Pr′)
  τ-depth/if-then =
    s≤s (m≤n⇒m≤n⊔o _ ≤-refl)

  τ-depth/if-else :
    ∀ {γ δ E}
      {Pr Pr′ : Proc γ δ}
    → τ-depth/proc Pr′ < τ-depth/proc (ifp E then Pr else Pr′)
  τ-depth/if-else =
    s≤s (m≤n⇒m≤o⊔n _ ≤-refl)

  τ-depth/unfold<rec :
    ∀ {Pr : Proc 0 1}
    → MessageGuarded Pr
    → τ-depth/proc (unfold/proc Pr) < τ-depth/proc (rec Pr)
  τ-depth/unfold<rec guarded
    rewrite τ-depth/unfold guarded =
    ≤-refl

  mutual

    t/rec/message-guarded :
      ∀ {G P Pr}
      → [] & [] ⊢p P ◂ rec Pr ∶ G
      → MessageGuarded Pr
    t/rec/message-guarded (t/skip std) =
      skip/rec/message-guarded std refl
    t/rec/message-guarded (t/unskip _ td) =
      t/rec/message-guarded td
    t/rec/message-guarded (t/rec guarded _) =
      guarded

    skip/rec/message-guarded :
      ∀ {ξ m G P Pr}
        {Ξ : Vec Behav ξ}
      → [] & [] & Ξ ⊢skip[ m ] P ◂ rec Pr ∶ G
      → m ≡ prod
      → MessageGuarded Pr
    skip/rec/message-guarded (skip/main td) _ =
      t/rec/message-guarded td
    skip/rec/message-guarded (skip/step gr _ ktd mode-gr) _ =
      skip/rec/message-guarded (ktd gr .proj₂) mode-gr
    skip/rec/message-guarded (skip/cycle _) ()

  τ-depth/stepper-decrease :
    ∀ {G M M′}
    → (M⊢G : ⊢s M ∶ G)
    → (st : M [ nothing ]⇒ M′)
    → τ-depth/proc (M′ [ stepper st ]s)
      < τ-depth/proc (M  [ stepper st ]s)
  τ-depth/stepper-decrease
    {M = M}
    M⊢G
    (s/if/true {E = E} {Pr = Pr} {Pr' = Pr′} P proc≡ _)
    rewrite lookup∘update P M Pr
          | reflect-lookup proc≡ =
    τ-depth/if-then {E = E} {Pr = Pr} {Pr′ = Pr′}
  τ-depth/stepper-decrease
    {M = M}
    M⊢G
    (s/if/false {E = E} {Pr = Pr} {Pr' = Pr′} P proc≡ _)
    rewrite lookup∘update P M Pr′
          | reflect-lookup proc≡ =
    τ-depth/if-else {E = E} {Pr = Pr} {Pr′ = Pr′}
  τ-depth/stepper-decrease
    {M = M}
    M⊢G
    (s/rec {Pr = Pr} P proc≡)
    rewrite lookup∘update P M (unfold/proc Pr)
          | reflect-lookup proc≡ =
    τ-depth/unfold<rec
      (t/rec/message-guarded (td/lookup M⊢G proc≡))

  τ-depth/step-nonincreasing :
    ∀ {G M M′}
    → (P : Part)
    → (M⊢G : ⊢s M ∶ G)
    → (st : M [ nothing ]⇒ M′)
    → τ-depth/proc (M′ [ P ]s)
      ≤ τ-depth/proc (M  [ P ]s)
  τ-depth/step-nonincreasing P M⊢G st
    with P ≟f stepper st
  ... | yes refl =
    <⇒≤ (τ-depth/stepper-decrease M⊢G st)
  τ-depth/step-nonincreasing {M = M} P M⊢G
    (s/if/true {Pr = Pr} Q _ _)
    | no P≢Q
    rewrite lookup∘update′ P≢Q M Pr =
    ≤-refl
  τ-depth/step-nonincreasing {M = M} P M⊢G
    (s/if/false {Pr' = Pr′} Q _ _)
    | no P≢Q
    rewrite lookup∘update′ P≢Q M Pr′ =
    ≤-refl
  τ-depth/step-nonincreasing {M = M} P M⊢G (s/rec {Pr = Pr} Q _) | no P≢Q
    rewrite lookup∘update′ P≢Q M (unfold/proc Pr) =
    ≤-refl

  τ-depth/session-aux :
    ∀ {I}
    → Vec Part I
    → Session
    → ℕ
  τ-depth/session-aux [] M =
    0
  τ-depth/session-aux (P ∷ Ps) M =
    τ-depth/proc (M [ P ]s) + τ-depth/session-aux Ps M

  τ-depth/session :
    Session
    → ℕ
  τ-depth/session M =
    τ-depth/session-aux (tabulate (λ P → P)) M

  τ-depth/session-aux-nonincreasing :
    ∀ {I G M M′}
    → (Ps : Vec Part I)
    → (M⊢G : ⊢s M ∶ G)
    → (st : M [ nothing ]⇒ M′)
    → τ-depth/session-aux Ps M′
      ≤ τ-depth/session-aux Ps M
  τ-depth/session-aux-nonincreasing [] M⊢G st =
    ≤-refl
  τ-depth/session-aux-nonincreasing (P ∷ Ps) M⊢G st =
    +-mono-≤
      (τ-depth/step-nonincreasing P M⊢G st)
      (τ-depth/session-aux-nonincreasing Ps M⊢G st)

  τ-depth/session-aux-decrease :
    ∀ {I G M M′}
    → (i  : Fin I)
    → (Ps : Vec Part I)
    → (M⊢G : ⊢s M ∶ G)
    → (st : M [ nothing ]⇒ M′)
    → lookup Ps i ≡ stepper st
    → τ-depth/session-aux Ps M′
      < τ-depth/session-aux Ps M
  τ-depth/session-aux-decrease zero (_ ∷ Ps) M⊢G st refl =
    +-mono-<-≤
      (τ-depth/stepper-decrease M⊢G st)
      (τ-depth/session-aux-nonincreasing Ps M⊢G st)
  τ-depth/session-aux-decrease (fsuc i) (P ∷ Ps) M⊢G st eq =
    +-mono-≤-<
      (τ-depth/step-nonincreasing P M⊢G st)
      (τ-depth/session-aux-decrease i Ps M⊢G st eq)

  τ-depth/decrease :
    ∀ {G M M′}
    → (M⊢G : ⊢s M ∶ G)
    → (st : M [ nothing ]⇒ M′)
    → τ-depth/session M′ < τ-depth/session M
  τ-depth/decrease M⊢G st =
    τ-depth/session-aux-decrease
      (stepper st)
      (tabulate (λ P → P))
      M⊢G
      st
      (lookup∘tabulate (λ P → P) (stepper st))

  catτ :
    ∀ {M M′ M″}
    → M  τ⇒ M′
    → M′ τ⇒ M″
    → M  τ⇒ M″
  catτ s/zero tr′ =
    tr′
  catτ (s/more st tr) tr′ =
    s/more st (catτ tr tr′)

  lookup-done :
    ∀ {M P Pr}
    → done M
    → M [ P ]= Pr
    → done/proc Pr
  lookup-done {P = P} doneM proc≡
    rewrite sym (reflect-lookup proc≡) =
    doneM P

  done-rec⊥ :
    ∀ {γ δ}
      {Pr : Proc γ (suc δ)}
    → done/proc (rec Pr)
    → ⊥
  done-rec⊥ ()

  still-done :
    ∀ {M M′}
    → M [ nothing ]⇒ M′
    → done M
    → done M′
  still-done {M = M} (s/if/true {Pr = Pr} P proc≡ _) doneM Q
    with Q ≟f P | lookup-done doneM proc≡
  ... | yes refl | done-if donePr _
    rewrite lookup∘update P M Pr =
    donePr
  ... | no Q≢P | _
    rewrite lookup∘update′ Q≢P M Pr =
    doneM Q
  still-done {M = M} (s/if/false {Pr' = Pr′} P proc≡ _) doneM Q
    with Q ≟f P | lookup-done doneM proc≡
  ... | yes refl | done-if _ donePr′
    rewrite lookup∘update P M Pr′ =
    donePr′
  ... | no Q≢P | _
    rewrite lookup∘update′ Q≢P M Pr′ =
    doneM Q
  still-done {M = M} (s/rec {Pr = Pr} P proc≡) doneM Q
    with Q ≟f P
  ... | yes refl =
    ⊥-elim (done-rec⊥ (lookup-done doneM proc≡))
  ... | no Q≢P
    rewrite lookup∘update′ Q≢P M (unfold/proc Pr) =
    doneM Q

  still-done* :
    ∀ {M M′}
    → M τ⇒ M′
    → done M
    → done M′
  still-done* s/zero doneM =
    doneM
  still-done* (s/more st tr) doneM =
    still-done* tr (still-done st doneM)

  ifp≢∅ :
    ∀ {γ δ E}
      {Pr Pr′ : Proc γ δ}
    → ifp E then Pr else Pr′ ≡ ∅
    → ⊥
  ifp≢∅ ()

  rec≢∅ :
    ∀ {γ δ}
      {Pr : Proc γ (suc δ)}
    → rec Pr ≡ ∅
    → ⊥
  rec≢∅ ()

  still-ended :
    ∀ {M M′}
    → (P : Part)
    → M [ nothing ]⇒ M′
    → M  [ P ]s ≡ ∅
    → M′ [ P ]s ≡ ∅
  still-ended {M = M} P
    (s/if/true {Pr = Pr} Q proc≡ _)
    ended
    with P ≟f Q
  ... | yes refl
    rewrite lookup∘update Q M Pr
          | reflect-lookup proc≡ =
    ⊥-elim (ifp≢∅ ended)
  ... | no P≢Q
    rewrite lookup∘update′ P≢Q M Pr =
    ended
  still-ended {M = M} P
    (s/if/false {Pr' = Pr′} Q proc≡ _)
    ended
    with P ≟f Q
  ... | yes refl
    rewrite lookup∘update Q M Pr′
          | reflect-lookup proc≡ =
    ⊥-elim (ifp≢∅ ended)
  ... | no P≢Q
    rewrite lookup∘update′ P≢Q M Pr′ =
    ended
  still-ended {M = M} P (s/rec {Pr = Pr} Q proc≡) ended
    with P ≟f Q
  ... | yes refl
    rewrite lookup∘update Q M (unfold/proc Pr)
          | reflect-lookup proc≡ =
    ⊥-elim (rec≢∅ ended)
  ... | no P≢Q
    rewrite lookup∘update′ P≢Q M (unfold/proc Pr) =
    ended

  still-ended* :
    ∀ {M M′ P}
    → M τ⇒ M′
    → M  [ P ]s ≡ ∅
    → M′ [ P ]s ≡ ∅
  still-ended* s/zero ended =
    ended
  still-ended* {P = P} (s/more st tr) ended =
    still-ended* tr (still-ended P st ended)

  final-run/proc :
    ∀ {M G P}
    → (Pr : Proc 0 0)
    → ⊢s M ∶ G
    → M [ P ]s ≡ Pr
    → done/proc Pr
    → ∃[ M′ ] M τ⇒ M′ × M′ [ P ]s ≡ ∅
  final-run/proc Pr M⊢G proc≡ done-∅ =
    _ , s/zero , proc≡
  final-run/proc
    {M = M}
    {P = P}
    (ifp E then Pr else Pr′)
    M⊢G
    proc≡
    (done-if donePr donePr′)
    with t/if/inv
           refl
           (td/lookup
             {M = M}
             {P = P}
             M⊢G
             (lookup-get {V = M} {x = P} proc≡))
  ... | etd , _ , _
    with eval-bool etd
  ...   | inj₁ e⇓true =
    let st = s/if/true P (lookup-get {V = M} {x = P} proc≡) e⇓true
        M′ , tr , ended =
          final-run/proc
            {M = M [ P ]≔ Pr}
            {P = P}
            Pr
            (preservation/τ M M⊢G st)
            (lookup∘update P M Pr)
            donePr
    in M′ , s/more st tr , ended
  ...   | inj₂ e⇓false =
    let st = s/if/false P (lookup-get {V = M} {x = P} proc≡) e⇓false
        M′ , tr , ended =
          final-run/proc
            {M = M [ P ]≔ Pr′}
            {P = P}
            Pr′
            (preservation/τ M M⊢G st)
            (lookup∘update P M Pr′)
            donePr′
    in M′ , s/more st tr , ended

  final-run/aux :
    ∀ {I M G}
    → (Ps : Vec Part I)
    → ⊢s M ∶ G
    → done M
    → ∃[ M′ ]
        M τ⇒ M′
      × (∀ i → M′ [ lookup Ps i ]s ≡ ∅)
  final-run/aux [] M⊢G doneM =
    _ , s/zero , λ ()
  final-run/aux {M = M} (P ∷ Ps) M⊢G doneM
    with final-run/aux Ps M⊢G doneM
  ... | M′ , tr , endedPs
    with final-run/proc
           {M = M′}
           {P = P}
           (M′ [ P ]s)
           (preservation/τ* M⊢G tr)
           refl
           (still-done* tr doneM P)
  ...   | M″ , tr′ , endedP =
    M″ ,
    catτ tr tr′ ,
    λ
      { zero     → endedP
      ; (fsuc i) → still-ended* tr′ (endedPs i)
      }

  final-run :
    ∀ {M G}
    → ⊢s M ∶ G
    → done M
    → ∃[ M′ ] M τ⇒ M′ × finished M′
  final-run {M = M} M⊢G doneM
    with final-run/aux (tabulate (λ P → P)) M⊢G doneM
  ... | M′ , tr , ended =
    M′ ,
    tr ,
    λ P →
      let eq = lookup∘tabulate (λ Q → Q) P
      in subst (λ Q → M′ [ Q ]s ≡ ∅) eq (ended P)

  progress/eventual :
    ∀ {M G}
    → ⊢s M ∶ G
    → ∃[ M′ ]
        ((M τ⇒ M′ × finished M′)
        ⊎ ∃[ α ] M [ α ]⇒+ M′)
  progress/eventual {M = M} M⊢G =
    go M⊢G (<-wellFounded (τ-depth/session M))
    where
    go :
      ∀ {M G}
      → ⊢s M ∶ G
      → Acc _<_ (τ-depth/session M)
      → ∃[ M′ ]
          ((M τ⇒ M′ × finished M′)
          ⊎ ∃[ α ] M [ α ]⇒+ M′)
    go {M = M} M⊢G (acc rs)
      with progress {M = M} M⊢G
    ... | inj₁ doneM =
      let M′ , tr , finishedM′ = final-run M⊢G doneM
      in M′ , inj₁ (tr , finishedM′)
    ... | inj₂ (just α , M′ , st) =
      M′ , inj₂ (α , s/one st)
    ... | inj₂ (nothing , M′ , st)
      with go
             (preservation/τ M M⊢G st)
             (rs (τ-depth/decrease M⊢G st))
    ...   | M″ , inj₁ (tr , finishedM″) =
      M″ , inj₁ (s/more st tr , finishedM″)
    ...   | M″ , inj₂ (α , tr) =
      M″ , inj₂ (α , s/more st tr)

  no-infinite-τ-reductions :
    ∀ M {G}
    → ⊢s M ∶ G
    → M ⇏∞

  no-infinite-τ-reductions M td sr =
    go td sr (<-wellFounded (τ-depth/session M))
    where
    go :
      ∀ {M G}
      → ⊢s M ∶ G
      → M ⇒∞
      → Acc _<_ (τ-depth/session M)
      → ⊥
    go {M = M} M⊢G td (acc rs) =
      let open _⇒∞ td in
      go
        (preservation/τ M M⊢G ∞-step)
        ∞-next
        (rs (τ-depth/decrease M⊢G ∞-step))
