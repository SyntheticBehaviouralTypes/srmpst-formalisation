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
  using    (Fin; zero)
  renaming (_≟_ to _≟f_; suc to fsuc)

open import Data.Vec
  using (Vec; []; _∷_; _++_; _[_]=_; _[_]≔_; lookup; tabulate)

open import Data.Vec.Properties
  using (lookup∘tabulate; lookup∘update; lookup∘update′)

open import Data.Product using (∃-syntax; Σ-syntax; _,_; _×_; proj₁; proj₂)
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

  infix 4 _⊢head_∶_

  data _⊢head_∶_ {γ}
    (Γ : Vec Sort γ)
    : NProc γ 0 → Behav → Set
    where

    h/send :
      ∀ {P Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {E : Exp γ}
        {Pr : Proc γ 0}
        {G G′ : Behav}
      → G -< P ⟶ Q # i < S > >-> G′
      → Γ ⊢e E ∶ S
      → Γ ⊢head P ◂ Pr ∶ G′
      → Γ ⊢head P ◂ Q ! i < E >∙ Pr ∶ G

    h/recv :
      ∀ {P Q I}
        {i : Fin (suc I)}
        {T : Sort}
        {S : Vec Sort (suc I)}
        {Br : Vec (Proc (suc γ) 0) (suc I)}
        {G G′ : Behav}
      → G -< Q ⟶ P # i < T > >-> G′
      → (∀ {j U G″}
          → G -< Q ⟶ P # j < U > >-> G″
          → (U ∷ Γ) ⊢head P ◂ lookup Br j ∶ G″)
      → Γ ⊢head P ◂ Σ Q ？[ S ]· Br ∶ G

    h/skip :
      ∀ {P}
        {Pr : Proc γ 0}
        {G G′ : Behav}
        {α : Action}
      → (gr : G -< α >-> G′)
      → (na : P not-active-in G)
      → (ktd :
          ∀ {G″ α′}
          → G -< α′ >-> G″
          → ∃[ m ] ((_⊢head_∶_) Γ & G ∷ [] ⊢skip[ m ] P ◂ Pr ∶ G″))
      → ktd gr .proj₁ ≡ prod
      → Γ ⊢head P ◂ Pr ∶ G

    h/if :
      ∀ {P}
        {E : Exp γ}
        {Pr Pr′ : Proc γ 0}
        {G : Behav}
      → Γ ⊢e E ∶ s/bool
      → Γ ⊢head P ◂ Pr ∶ G
      → Γ ⊢head P ◂ Pr′ ∶ G
      → Γ ⊢head P ◂ ifp E then Pr else Pr′ ∶ G

    h/rec :
      ∀ {P}
        {Pr : Proc γ 1}
        {G G′ : Behav}
      → G -[¬ P ]->* G′
      → MessageGuarded Pr
      → Γ & G ∷ [] ⊢p P ◂ Pr ∶ G
      → Γ ⊢head P ◂ rec Pr ∶ G′

    h/end :
      ∀ {P}
        {G : Behav}
      → ¬ P ∈T G
      → Γ ⊢head P ◂ ∅ ∶ G


  infix  4 _&_⊢hskip[_]_∶_

  _&_⊢hskip[_]_∶_ :
    ∀ {γ ξ}
      (Γ : Vec Sort γ)
      (Ξ : Vec Behav ξ)
    → Mode
    → NProc γ 0
    → Behav 
    → Set
  Γ & Ξ ⊢hskip[ m ] PPr ∶ G =
    ((_⊢head_∶_) Γ) & Ξ ⊢skip[ m ] PPr ∶ G

  mutual
    head/typing :
      ∀ {γ P Pr G}
        {Γ : Vec Sort γ}
      → Γ ⊢head P ◂ Pr ∶ G
      → Γ & [] ⊢p P ◂ Pr ∶ G
    head/typing (h/send gr etd td) =
      t/send gr etd (head/typing td)
    head/typing (h/recv gr conts) =
      t/recv gr (head/typing ∘ conts)
    head/typing (h/skip gr na ktd x) =
      t/skip
        (skip/step gr na
          (λ gr′ → ktd gr′ .proj₁ , hskip/typing (ktd gr′ .proj₂))
          x)
    head/typing (h/if etd head₁ head₂) =
      t/if etd (head/typing head₁) (head/typing head₂)
    head/typing (h/rec tr guarded td) =
      t/unskip tr (t/rec guarded td)
    head/typing (h/end done) =
      t/end done

    hskip/typing :
      ∀ {γ ξ P Pr G m}
        {Γ : Vec Sort γ}
        {Ξ : Vec Behav ξ}
      → Γ & Ξ ⊢hskip[ m ] P ◂ Pr ∶ G
      → Γ & [] & Ξ ⊢skip[ m ] P ◂ Pr ∶ G
    hskip/typing (skip/main td) = 
      skip/main (head/typing td)
    hskip/typing (skip/step gr na ktd x) = 
      skip/step gr na 
        (λ gr′ → ktd gr′ .proj₁ , hskip/typing (ktd gr′ .proj₂))
        x
    hskip/typing (skip/cycle x) = 
      skip/cycle x

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

    head/bisim G~G′ (h/skip gr na ktd prod-gr) =
      h/skip
        (~L→ G~G′ gr)
        (na ∘ ~R→ G~G′)
        (λ gr′ →
          _ ,
          hskip/bisim
            (~ᵛ/∷ G~G′ ~ᵛ/[])
            (~R→~ G~G′ gr′)
            (ktd (~R→ G~G′ gr′) .proj₂))
        (subst (_≡ prod) (selected-step-mode (proj₁ ∘ ktd) G~G′ gr) prod-gr)

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
      ∀ {γ ξ m P Pr G G′}
        {Γ : Vec Sort γ}
        {Ξ Ξ′ : Vec Behav ξ}
      → Ξ ~ᵛ Ξ′
      → G ~ G′
      → Γ & Ξ ⊢hskip[ m ] P ◂ Pr ∶ G
      → Γ & Ξ′ ⊢hskip[ m ] P ◂ Pr ∶ G′

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

  pskip/unfold-cycle :
    ∀ {γ ξ m m′ G H P Pr}
      {Γ : Vec Sort γ}
      {Ξ : Vec Behav ξ}
    → Γ & [] & Ξ ⊢skip[ m ] P ◂ Pr ∶ G
    → Γ & [] & G ∷ Ξ ⊢skip[ m′ ] P ◂ Pr ∶ H
    → ∃[ n ] (Γ & [] & Ξ ⊢skip[ n ] P ◂ Pr ∶ H)
      × (m′ ≡ prod → n ≡ prod)
  pskip/unfold-cycle {P = P} {Pr = Pr} =
    skip/unfold-cycle
      {PPr = P ◂ Pr}
      {Ξ′ = []}
      ptd/bisim

  pskip/unfold-top-cycle :
    ∀ {γ m G H P Pr}
      {Γ : Vec Sort γ}
    → Γ & [] & [] ⊢skip[ prod ] P ◂ Pr ∶ G
    → Γ & [] & G ∷ [] ⊢skip[ m ] P ◂ Pr ∶ H
    → Γ & [] & []  ⊢skip[ prod ] P ◂ Pr ∶ H
  pskip/unfold-top-cycle td ktd with pskip/unfold-cycle td ktd 
  ... | prod , td , _ = td
  ... | nonprod , skip/cycle {X = ()} _ , _


  hskip/head :
    ∀ {γ G P Pr}
      {Γ : Vec Sort γ}
    → Γ & [] ⊢hskip[ prod ] P ◂ Pr ∶ G
    → Γ ⊢head P ◂ Pr ∶ G
  hskip/head (skip/main head) =
    head
  hskip/head (skip/step gr na ktd prod-gr) =
    h/skip gr na ktd prod-gr

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

  skip/~R-trace :
    ∀ {G G′ H′ P}
    → G ~ G′
    → G′ -[¬ P ]->* H′
    → ∃[ H ] (G -[¬ P ]->* H) × (H ~ H′)
  skip/~R-trace G~G′ skip/refl =
    _ , skip/refl , G~G′
  skip/~R-trace G~G′ (skip/step gr P∉α tr) =
    let _ , tr′ , H~H′ = skip/~R-trace (~R→~ G~G′ gr) tr
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
    main/step gr′ (mainLeaf/weaken-visited (ktd gr′ .proj₂) leaf)
  mainLeaf/weaken-visited (skip/cycle _) ()

  skip-leaf/head-bisim :
    ∀ {γ ξ m P Pr G G′}
      {Γ : Vec Sort γ}
      {Ξ Ξ′ : Vec Behav ξ}
    → (Ξ~Ξ′ : Ξ ~ᵛ Ξ′)
    → (G~G′ : G ~ G′)
    → (std : Γ & [] & Ξ ⊢skip[ m ] P ◂ Pr ∶ G)
    → LeafHead std
    → LeafHead (skip-leaf/bisim ptd/bisim Ξ~Ξ′ G~G′ std)
  skip-leaf/head-bisim Ξ~Ξ′ G~G′ (skip/main td) leafHead main/here tr =
    let _ , tr′ , H~H′ = skip/~R-trace G~G′ tr
    in head/bisim H~H′ (leafHead main/here tr′)
  skip-leaf/head-bisim Ξ~Ξ′ G~G′ (skip/step gr na ktd ok) leafHead (main/step gr′ leaf) tr =
    skip-leaf/head-bisim
      (~ᵛ/∷ G~G′ Ξ~Ξ′)
      (~R→~ G~G′ gr′)
      (ktd (~R→ G~G′ gr′) .proj₂)
      (λ leaf′ tr′ → leafHead (main/step (~R→ G~G′ gr′) leaf′) tr′)
      leaf
      tr
  skip-leaf/head-bisim Ξ~Ξ′ G~G′ (skip/cycle eq) leafHead ()

  skip/head/refl-head :
    ∀ {γ ξ P Pr G m}
      {Γ : Vec Sort γ}
      {Ξ : Vec Behav ξ}
    → (std : Γ & [] & Ξ ⊢skip[ m ] P ◂ Pr ∶ G)
    → LeafHead std
    → Γ & Ξ ⊢hskip[ m ] P ◂ Pr ∶ G
  skip/head/refl-head (skip/main td) leafHead =
    skip/main (leafHead main/here skip/refl)
  skip/head/refl-head (skip/step gr na ktd ok) leafHead =
    skip/step gr na
      (λ gr′ →
        ktd gr′ .proj₁ ,
        skip/head/refl-head
          (ktd gr′ .proj₂)
          (λ leaf tr → leafHead (main/step gr′ leaf) tr))
      ok
  skip/head/refl-head (skip/cycle eq) _ =
    skip/cycle eq

  pskip/unfold-cycle/head :
    ∀ {γ ξ ξ′ m m′ G H P Pr}
      {Γ : Vec Sort γ}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → (base : Γ & [] & Ξ′ ++ Ξ ⊢skip[ m ] P ◂ Pr ∶ G)
    → LeafHead base
    → (inner : Γ & [] & Ξ′ ++ G ∷ Ξ ⊢skip[ m′ ] P ◂ Pr ∶ H)
    → LeafHead inner
    → ∃[ n ]
        (Σ[ out ∈ Γ & [] & Ξ′ ++ Ξ ⊢skip[ n ] P ◂ Pr ∶ H ]
          LeafHead out)
        × (m′ ≡ prod → n ≡ prod)
  pskip/unfold-cycle/head base baseHead (skip/main td) innerHead =
    prod , (skip/main td , (λ { main/here → innerHead main/here })) , λ _ → refl
  pskip/unfold-cycle/head {Ξ = Ξ} {Ξ′ = Ξ′} base baseHead (skip/step {G = H} gr na ktd ok) innerHead =
    let base′ = skip/weaken-visited {H = H} {Ξ = Ξ′ ++ Ξ} {Ξ′ = []} base
        base′Head : LeafHead base′
        base′Head leaf tr =
          baseHead (mainLeaf/weaken-visited base leaf) tr
        unfold =
          λ {β H′} (gr′ : H -< β >-> H′) →
            pskip/unfold-cycle/head
              {Ξ′ = H ∷ Ξ′}
              base′
              base′Head
              (ktd gr′ .proj₂)
              (λ leaf tr → innerHead (main/step gr′ leaf) tr)
    in
      prod ,
      ( skip/step gr na
          (λ gr′ →
            unfold gr′ .proj₁ ,
            proj₁ (proj₁ (proj₂ (unfold gr′))))
          (proj₂ (proj₂ (unfold gr)) ok)
      , (λ { (main/step gr′ leaf) →
            proj₂ (proj₁ (proj₂ (unfold gr′))) leaf
          })
      ) ,
      λ _ → refl
  pskip/unfold-cycle/head {Ξ = Ξ} {Ξ′ = Ξ′} base baseHead (skip/cycle {X = X} eq) innerHead
    with lookup/insert {Ξ = Ξ} {Ξ′ = Ξ′} (X , eq)
  ... | inj₁ G~H =
    _ ,
    ( skip-leaf/bisim ptd/bisim ~ᵛ-refl G~H base
    , skip-leaf/head-bisim ~ᵛ-refl G~H base baseHead
    ) ,
    λ ()
  ... | inj₂ (_ , eq′) =
    nonprod , (skip/cycle eq′ , λ ()) , λ ()

  pskip/unfold-top-cycle/head :
    ∀ {γ m G H P Pr}
      {Γ : Vec Sort γ}
    → (base : Γ & [] & [] ⊢skip[ prod ] P ◂ Pr ∶ G)
    → LeafHead base
    → (inner : Γ & [] & G ∷ [] ⊢skip[ m ] P ◂ Pr ∶ H)
    → LeafHead inner
    → Σ[ out ∈ Γ & [] & [] ⊢skip[ prod ] P ◂ Pr ∶ H ]
        LeafHead out
  pskip/unfold-top-cycle/head base baseHead inner innerHead
    with pskip/unfold-cycle/head {Ξ = []} {Ξ′ = []} base baseHead inner innerHead
  ... | prod , out , _ =
    out
  ... | nonprod , (skip/cycle {X = ()} _ , _) , _

  mutual

    skip/head-step :
      ∀ {γ ξ m P Pr G}
        {Γ : Vec Sort γ}
        {Ξ : Vec Behav ξ}
      → (std : Γ & [] & Ξ ⊢skip[ m ] P ◂ Pr ∶ G)
      → LeafHead std

    skip/head-step (skip/main td) main/here tr =
      td/head td tr
    skip/head-step (skip/step _ _ ktd _) (main/step gr′ leaf) tr =
      skip/head-step (ktd gr′ .proj₂) leaf tr
    skip/head-step (skip/cycle _) ()

    cancel/unskip-skip :
      ∀ {γ P Pr G G′}
        {Γ : Vec Sort γ}
      → G -[¬ P ]->* G′
      → (std : Γ & [] & [] ⊢skip[ prod ] P ◂ Pr ∶ G)
      → LeafHead std
      → Γ ⊢head P ◂ Pr ∶ G′

    cancel/unskip-skip skip/refl std leafHead =
      hskip/head (skip/head/refl-head std leafHead)
    cancel/unskip-skip tr@(skip/step _ _ _) (skip/main td) leafHead =
      leafHead main/here tr
    cancel/unskip-skip (skip/step gr _ tr) std@(skip/step _ _ ktd _) leafHead =
      let unfolded =
            pskip/unfold-top-cycle/head
              std
              leafHead
              (ktd gr .proj₂)
              (λ leaf tr′ → leafHead (main/step gr leaf) tr′)
      in cancel/unskip-skip tr (proj₁ unfolded) (proj₂ unfolded)

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
      cancel/unskip-skip
        tr
        std
        (skip/head-step std)
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

  t/send/cont :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {E : Exp 0}
      {Pr : Proc 0 0}
    → [] & [] ⊢p P ◂ Q ! i < E >∙ Pr ∶ G
    → G -< P ⟶ Q # i < S > >-> G′
    → [] ⊢e E ∶ S × [] & [] ⊢p P ◂ Pr ∶ G′

  t/send/cont td gr
    with td/head td skip/refl
  ... | h/send gr₀ etd td′ =
    let etd′ , hd′ = t/send/cont-branch etd td′ gr gr₀
    in etd′ , head/typing hd′
  ... | h/skip _ na _ _ =
    ⊥-elim (∉c→¬∈c (na gr) (∈S refl))

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

    t/comm/ready/head (h/send gr _ _) (h/skip _ Q∉G _ _) =
      ⊥-elim (∉c→¬∈c (Q∉G gr) (∈R refl))

    t/comm/ready/head (h/send gr _ _) _ =
      _ , _ , gr

    t/comm/ready/head (h/skip _ P∉G _ _) (h/recv gr _) =
      ⊥-elim (∉c→¬∈c (P∉G gr) (∈S refl))

    t/comm/ready/head
      (h/skip grα P∉G headP prodP)
      (h/skip grQ Q∉G headQ modeQ) =
      let _ , stdQ , _ =
            hskip/unfold-cycle
              (skip/main (h/skip grQ Q∉G headQ modeQ))
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
      t/comm/ready/head headP (h/skip gr na ktd x)

    t/comm/ready/hskip-hskip 
      (skip/step gr na ktd x)
      refl
      (skip/main (h/recv x₁ x₂)) = 
      ⊥-elim (_∉c_.∉S (na x₁) refl)

    t/comm/ready/hskip-hskip
      (skip/step grα P∉G headP prodP)
      refl
      (skip/main (h/skip grQ Q∉G headQ modeQ)) =
      let _ , stdQ , _ =
            hskip/unfold-cycle
              (skip/main (h/skip grQ Q∉G headQ modeQ))
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

    t/comm/ready/hskip-hskip 
      (skip/step grα P∉G headP prodP)
      refl
      (skip/step grQ Q∉G headQ modeQ) =
      let _ , stdQ , _ =
            hskip/unfold-cycle
              (skip/main (h/skip grQ Q∉G headQ modeQ))
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


  t/recv/cont :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {T : Sort}
      {S : Vec Sort (suc I)}
      {Br : Vec (Proc 1 0) (suc I)}
    → [] & [] ⊢p Q ◂ Σ P ？[ S ]· Br ∶ G
    → (gr : G -< P ⟶ Q # i < T > >-> G′)
    → (T ∷ []) & [] ⊢p Q ◂ lookup Br i ∶ G′

  t/recv/cont td gr
    with td/head td skip/refl
  ... | h/recv _ conts =
    head/typing (conts gr)
  ... | h/skip _ na _ _ =
    ⊥-elim (∉c→¬∈c (na gr) (∈R refl))


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


  data ProcessStatus
    (G : Behav)
    (P : Part)
    : Proc 0 0 → Set
    where

    ps/step :
      ∀ {Pr α G′}
      → G -< α >-> G′
      → ProcessStatus G P Pr

    ps/if :
      ∀ {Pr E Pr′ Pr″}
      → [] ⊢e E ∶ s/bool
      → Pr ≡ ifp E then Pr′ else Pr″
      → ProcessStatus G P Pr

    ps/rec :
      ∀ {Pr Pr′}
      → Pr ≡ rec Pr′
      → ProcessStatus G P Pr

    ps/end :
      ∀ {Pr}
      → P ∉T G
      → ProcessStatus G P Pr

  process/status/head :
    ∀ {G P Pr}
    → [] ⊢head P ◂ Pr ∶ G
    → ProcessStatus G P Pr
  process/status/head (h/send gr _ _) =
    ps/step gr
  process/status/head (h/recv gr _) =
    ps/step gr
  process/status/head (h/skip gr _ _ _) =
    ps/step gr
  process/status/head (h/if etd _ _) =
    ps/if etd refl
  process/status/head (h/rec _ _ _) =
    ps/rec refl
  process/status/head (h/end done) =
    ps/end done

  process/status :
    ∀ {G P Pr}
    → [] & [] ⊢p P ◂ Pr ∶ G
    → ProcessStatus G P Pr
  process/status =
    λ td → process/status/head (td/head td skip/refl)

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
    message-guarded/∈T/head mg/send (h/skip gr _ ktd mode-gr) =
      in/later gr (message-guarded/∈T/hskip mg/send (ktd gr .proj₂) mode-gr)
    message-guarded/∈T/head mg/recv (h/recv gr _) =
      in/recv gr
    message-guarded/∈T/head mg/recv (h/skip gr _ ktd mode-gr) =
      in/later gr (message-guarded/∈T/hskip mg/recv (ktd gr .proj₂) mode-gr)
    message-guarded/∈T/head (mg/if mg₁ _) (h/if _ head₁ _) =
      message-guarded/∈T/head mg₁ head₁
    message-guarded/∈T/head guarded@(mg/if _ _) (h/skip gr _ ktd mode-gr) =
      in/later gr (message-guarded/∈T/hskip guarded (ktd gr .proj₂) mode-gr)

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
    not-in-type/done/head P∉G (h/skip gr _ ktd mode-gr) =
      not-in-type/done/hskip
        (λ P∈G′ → P∉G (in/later gr P∈G′))
        (ktd gr .proj₂)
        mode-gr
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
        (λ P∈G′ → P∉G (in/later gr P∈G′))
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

  data SendView
    (P : Part)
    (G : Behav)
    (Pr : Proc 0 0)
    : Set
    where

    sv/send :
      ∀ {Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {E : Exp 0}
        {Pr′ : Proc 0 0}
        {G′ : Behav}
      → [] ⊢e E ∶ S
      → G -< P ⟶ Q # i < S > >-> G′
      → Pr ≡ Q ! i < E >∙ Pr′
      → SendView P G Pr

    sv/if :
      ∀ {E Pr′ Pr″}
      → [] ⊢e E ∶ s/bool
      → Pr ≡ ifp E then Pr′ else Pr″
      → SendView P G Pr

    sv/rec :
      ∀ {Pr′}
      → Pr ≡ rec Pr′
      → SendView P G Pr

  send/view/head :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {Pr : Proc 0 0}
    → G -< P ⟶ Q # i < S > >-> G′
    → [] ⊢head P ◂ Pr ∶ G
    → SendView P G Pr
  send/view/head _ (h/send gr etd _) =
    sv/send etd gr refl
  send/view/head gr (h/recv gr′ _)
    with recv-overlap⇒same-comm gr′ gr (∈S refl)
  ... | refl =
    ⊥-elim (sender≢receiver gr refl)
  send/view/head gr (h/skip _ P∉G _ _) =
    ⊥-elim (∉c→¬∈c (P∉G gr) (∈S refl))
  send/view/head _ (h/if etd _ _) =
    sv/if etd refl
  send/view/head _ (h/rec _ _ _) =
    sv/rec refl
  send/view/head gr (h/end done) =
    ⊥-elim (done (in/send gr))

  send/view :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {Pr : Proc 0 0}
    → G -< P ⟶ Q # i < S > >-> G′
    → [] & [] ⊢p P ◂ Pr ∶ G
    → SendView P G Pr
  send/view gr td =
    send/view/head gr (td/head td skip/refl)

  data RecvView
    (P Q : Part)
    {I : ℕ}
    (i : Fin (suc I))
    (G : Behav)
    (Pr : Proc 0 0)
    : Set
    where

    rv/recv :
      ∀ {S : Vec Sort (suc I)}
        {Br : Vec (Proc 1 0) (suc I)}
      → Pr ≡ Σ P ？[ S ]· Br
      → RecvView P Q i G Pr

    rv/if :
      ∀ {E Pr′ Pr″}
      → [] ⊢e E ∶ s/bool
      → Pr ≡ ifp E then Pr′ else Pr″
      → RecvView P Q i G Pr

    rv/rec :
      ∀ {Pr′}
      → Pr ≡ rec Pr′
      → RecvView P Q i G Pr

  recv/view/head :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {Pr : Proc 0 0}
    → G -< P ⟶ Q # i < S > >-> G′
    → [] ⊢head Q ◂ Pr ∶ G
    → RecvView P Q i G Pr
  recv/view/head gr (h/send gr′ _ _)
    with recv-overlap⇒same-comm gr gr′ (∈S refl)
  ... | refl =
    ⊥-elim (sender≢receiver gr refl)
  recv/view/head gr (h/recv gr′ _)
    with recv-overlap⇒same-comm gr gr′ (∈R refl)
  ... | refl
    with step-arity-deterministic gr gr′
  ...   | refl =
    rv/recv refl
  recv/view/head gr (h/skip _ Q∉G _ _) =
    ⊥-elim (∉c→¬∈c (Q∉G gr) (∈R refl))
  recv/view/head _ (h/if etd _ _) =
    rv/if etd refl
  recv/view/head _ (h/rec _ _ _) =
    rv/rec refl
  recv/view/head gr (h/end done) =
    ⊥-elim (done (in/recv gr))

  recv/view :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {Pr : Proc 0 0}
    → G -< P ⟶ Q # i < S > >-> G′
    → [] & [] ⊢p Q ◂ Pr ∶ G
    → RecvView P Q i G Pr
  recv/view gr td =
    recv/view/head gr (td/head td skip/refl)

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

  session/status :
    ∀ {I M G}
    → (Ps : Vec Part I)
    → ⊢s M ∶ G
    → SessionStatus M G Ps

  session/status [] M⊢G =
    ss/end λ ()

  session/status {M = M} (P ∷ Ps) M⊢G
    with process/status (M⊢G P)
  ... | ps/step gr =
    ss/step gr
  ... | ps/if etd eq =
    ss/if etd (lookup-get eq)
  ... | ps/rec eq =
    ss/rec (lookup-get eq)
  ... | ps/end P∉G
    with session/status Ps M⊢G
  ...   | ss/step gr =
    ss/step gr
  ...   | ss/if etd luP =
    ss/if etd luP
  ...   | ss/rec luP =
    ss/rec luP
  ...   | ss/end done =
    ss/end λ
      { zero     → P∉G
      ; (fsuc i) → done i
      }


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

  recv/progress :
    ∀ {M G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {E : Exp 0}
      {Pr : Proc 0 0}
    → ⊢s M ∶ G
    → [] ⊢e E ∶ S
    → G -< P ⟶ Q # i < S > >-> G′
    → M [ P ]= Q ! i < E >∙ Pr
    → RecvView P Q i G (M [ Q ]s)
    → ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′
  recv/progress {P = P} {Q = Q} {i = i} M⊢G etd gr send≡ (rv/recv recv≡)
    with eval-exp etd
  ... | V , e⇓v =
    just (P ⟶ Q # i < sort/value V >) , _ ,
    s/comm P Q send≡ e⇓v (lookup-get recv≡)
  recv/progress M⊢G etd gr send≡ (rv/if etd′ recv≡) =
    if/progress etd′ (lookup-get recv≡)
  recv/progress M⊢G etd gr send≡ (rv/rec recv≡) =
    nothing , _ , s/rec _ (lookup-get recv≡)

  step/progress :
    ∀ {M G G′ α}
    → ⊢s M ∶ G
    → G -< α >-> G′
    → ∃[ β ] ∃[ M′ ] M [ β ]⇒ M′
  step/progress {α = P ⟶ Q # i < S >} M⊢G gr
    with send/view gr (M⊢G P)
  ... | sv/send {Q = Q′} etd gr′ send≡ =
    recv/progress M⊢G etd gr′ (lookup-get send≡) (recv/view gr′ (M⊢G Q′))
  ... | sv/if etd send≡ =
    if/progress etd (lookup-get send≡)
  ... | sv/rec send≡ =
    nothing , _ , s/rec P (lookup-get send≡)

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
  τ-depth/step-nonincreasing {M = M} P M⊢G (s/if/true {Pr = Pr} Q _ _) | no P≢Q
    rewrite lookup∘update′ P≢Q M Pr =
    ≤-refl
  τ-depth/step-nonincreasing {M = M} P M⊢G (s/if/false {Pr' = Pr′} Q _ _) | no P≢Q
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
  still-ended {M = M} P (s/if/true {E = E} {Pr = Pr} {Pr' = Pr′} Q proc≡ _) ended
    with P ≟f Q
  ... | yes refl
    rewrite lookup∘update Q M Pr
          | reflect-lookup proc≡ =
    ⊥-elim (ifp≢∅ ended)
  ... | no P≢Q
    rewrite lookup∘update′ P≢Q M Pr =
    ended
  still-ended {M = M} P (s/if/false {E = E} {Pr = Pr} {Pr' = Pr′} Q proc≡ _) ended
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
