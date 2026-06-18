{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc)

open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)

open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; sym)

open import Definitions.Expr using (Sort)

module Definitions.Behav where

  import Definitions.Actions
  import Definitions.Common

  record BTheory (N : ℕ) : Set₁ where
    open Definitions.Actions N
    open Definitions.Common N

    field
      Behav : Set
      _-<_>->_ : Behav → Action → Behav → Set

    -- Participation

    _not-active-in_ : Part → Behav → Set
    P not-active-in G =
      ∀ {α G′} → G -< α >-> G′ → P ∉α α

    infix 4 _-[¬_]->*_

    data _-[¬_]->*_ (G : Behav) (P : Part) : Behav → Set where
      unskip/refl :
        G -[¬ P ]->* G

      unskip/step :
        ∀ {G′ G″ α}
        → G -< α >-> G′
        → P ∉α α
        → G′ -[¬ P ]->* G″
        → G -[¬ P ]->* G″

    unskip/one :
      ∀ {G G′ P α}
      → G -< α >-> G′
      → P ∉α α
      → G -[¬ P ]->* G′
    unskip/one gr P∉α =
      unskip/step gr P∉α unskip/refl

    unskip/cat :
      ∀ {G G′ G″ P}
      → G -[¬ P ]->* G′
      → G′ -[¬ P ]->* G″
      → G -[¬ P ]->* G″
    unskip/cat unskip/refl tr′ =
      tr′
    unskip/cat (unskip/step gr P∉α tr) tr′ =
      unskip/step gr P∉α (unskip/cat tr tr′)

    data _∈T_ P : Behav → Set where
      in/α :
        ∀ {G G′ α}
        → G -< α >-> G′
        → P ∈α α
        → P ∈T G

      in/later :
        ∀ {G G′ α}
        → G -< α >-> G′
        → P ∈T G′
        → P ∈T G

    in/send : ∀ {G α G′} → G -< α >-> G′ → sender α ∈T G
    in/send gr =
      in/α gr (∈S refl)

    in/recv : ∀ {G α G′} → G -< α >-> G′ → receiver α ∈T G
    in/recv gr =
      in/α gr (∈R refl)

    unskip/∈T-back :
      ∀ {G G′ P Q}
      → G -[¬ P ]->* G′
      → Q ∈T G′
      → Q ∈T G
    unskip/∈T-back unskip/refl Q∈T =
      Q∈T
    unskip/∈T-back (unskip/step gr _ tr) Q∈T =
      in/later gr (unskip/∈T-back tr Q∈T)

    ended : Behav → Set
    ended G =
      ∀ P → ¬ P ∈T G

    _∉T_ : Part → Behav → Set
    P ∉T G =
      ¬ P ∈T G

    -- Bisimilarity

    record _~_ (G G′ : Behav) : Set where
      coinductive
      field
        ~L :
          ∀ {α G″}
          → G -< α >-> G″
          → ∃[ G‴ ] G′ -< α >-> G‴ × G″ ~ G‴

        ~R :
          ∀ {α G‴}
          → G′ -< α >-> G‴
          → ∃[ G″ ] G -< α >-> G″ × G″ ~ G‴

    open _~_

    ~refl : ∀ {G} → G ~ G
    ~L ~refl gr =
      _ , gr , ~refl
    ~R ~refl gr =
      _ , gr , ~refl

    ~sym : ∀ {G G′} → G ~ G′ → G′ ~ G
    ~L (~sym G~G′) gr =
      let _ , gr′ , b = ~R G~G′ gr
      in _ , gr′ , ~sym b
    ~R (~sym G~G′) gr =
      let _ , gr′ , b = ~L G~G′ gr
      in _ , gr′ , ~sym b

    ~trans : ∀ {G G′ G″} → G ~ G′ → G′ ~ G″ → G ~ G″
    ~L (~trans G~G′ G′~G″) gr =
      let _ , gr′ , b′ = ~L G~G′ gr
          _ , gr″ , b″ = ~L G′~G″ gr′
      in _ , gr″ , ~trans b′ b″
    ~R (~trans G~G′ G′~G″) gr =
      let _ , gr′ , b′ = ~R G′~G″ gr
          _ , gr″ , b″ = ~R G~G′ gr′
      in _ , gr″ , ~trans b″ b′

    ~L→G :
      ∀ {G G′ G″ α}
      → G ~ G′
      → G -< α >-> G″
      → Behav
    ~L→G G~G′ gr =
      ~L G~G′ gr .proj₁

    ~L→ :
      ∀ {G G′ G″ α}
      → (G~G′ : G ~ G′)
      → (gr : G -< α >-> G″)
      → G′ -< α >-> ~L→G G~G′ gr
    ~L→ G~G′ gr =
      ~L G~G′ gr .proj₂ .proj₁

    ~L→~ :
      ∀ {G G′ G″ α}
      → (G~G′ : G ~ G′)
      → (gr : G -< α >-> G″)
      → G″ ~ ~L→G G~G′ gr
    ~L→~ G~G′ gr =
      ~L G~G′ gr .proj₂ .proj₂

    ~R→G :
      ∀ {G G′ G″ α}
      → G ~ G′
      → G′ -< α >-> G″
      → Behav
    ~R→G G~G′ gr =
      ~R G~G′ gr .proj₁

    ~R→ :
      ∀ {G G′ G″ α}
      → (G~G′ : G ~ G′)
      → (gr : G′ -< α >-> G″)
      → G -< α >-> ~R→G G~G′ gr
    ~R→ G~G′ gr =
      ~R G~G′ gr .proj₂ .proj₁

    ~R→~ :
      ∀ {G G′ G″ α}
      → (G~G′ : G ~ G′)
      → (gr : G′ -< α >-> G″)
      → ~R→G G~G′ gr ~ G″
    ~R→~ G~G′ gr =
      ~R G~G′ gr .proj₂ .proj₂

    ∈~ : ∀ {P G G′} → G ~ G′ → P ∈T G → P ∈T G′
    ∈~ G~G′ (in/α gr P∈α) =
      in/α (~L→ G~G′ gr) P∈α
    ∈~ G~G′ (in/later gr P∈G″) =
      in/later (~L→ G~G′ gr) (∈~ (~L→~ G~G′ gr) P∈G″)

    -- Environment bisimilarity

    data _~ᵛ_ : ∀ {δ δ′} → Vec Behav δ → Vec Behav δ′ → Set where
      ~ᵛ/[] :
        [] ~ᵛ []

      ~ᵛ/∷ :
        ∀ {δ δ′}
          {G G′ : Behav}
          {Δ  : Vec Behav δ}
          {Δ′ : Vec Behav δ′}
        → G ~ G′
        → Δ ~ᵛ Δ′
        → (G ∷ Δ) ~ᵛ (G′ ∷ Δ′)

    ~ᵛ-refl : ∀ {δ} {Δ : Vec Behav δ} → Δ ~ᵛ Δ
    ~ᵛ-refl {Δ = []} =
      ~ᵛ/[]
    ~ᵛ-refl {Δ = _ ∷ _} =
      ~ᵛ/∷ ~refl ~ᵛ-refl

    lookup/~ᵛ :
      ∀ {δ}
        {Δ Δ′ : Vec Behav δ}
        {G : Behav}
      → Δ ~ᵛ Δ′
      → (X : Fin δ)
      → lookup Δ X ~ G
      → lookup Δ′ X ~ G
    lookup/~ᵛ (~ᵛ/∷ G~G′ _) zero G~lookup =
      ~trans (~sym G~G′) G~lookup
    lookup/~ᵛ (~ᵛ/∷ _ Δ~Δ′) (suc X) G~lookup =
      lookup/~ᵛ Δ~Δ′ X G~lookup

  record BT-Prop {N : ℕ} (B : BTheory N) : Set₁ where
    open Definitions.Actions N
    open Definitions.Common N
    open BTheory B

    field
      -- Action equality

      recv-overlap⇒same-comm :
        ∀ {G α α′ G′ G″}
        → G -< α  >-> G′
        → G -< α′ >-> G″
        → receiver α ∈α α′
        → Action.comm α ≡ Action.comm α′

      sender≢receiver :
        ∀ {G G′ α}
        → G -< α >-> G′
        → sender α ≢ receiver α

      step-deterministic :
        ∀ {G α G′ G″}
        → G -< α >-> G′
        → G -< α >-> G″
        → G′ ≡ G″

      step-sort-deterministic :
        ∀ {G G′ G″ P Q I}
          {i : Fin (suc I)}
          {S T : Sort}
        → G -< P ⟶ Q # i < S > >-> G′
        → G -< P ⟶ Q # i < T > >-> G″
        → S ≡ T

      step-arity-deterministic :
        ∀ {G G′ G″ P Q I J}
          {i : Fin (suc I)}
          {j : Fin (suc J)}
          {S T : Sort}
        → G -< P ⟶ Q # i < S > >-> G′
        → G -< P ⟶ Q # j < T > >-> G″
        → I ≡ J

      no-new-branch/step :
        ∀ {G G′ Gᵢ Gⱼ′ β γ}
          {cᵢ cⱼ : Choice}
        → G -< β >-> G′
        → Comm.receiver γ ∉α β
        → G  -< γ # cᵢ >-> Gᵢ
        → G′ -< γ # cⱼ >-> Gⱼ′
        → ∃[ Gⱼ ] G -< γ # cⱼ >-> Gⱼ

      -- Unrelated steps cannot be the first point where a communication
      -- becomes available.
      no-new-comm/step :
        ∀ {G G′ Gγ β γ}
          {c : Choice}
        → G -< β >-> G′
        → Comm.sender γ ∉α β
        → Comm.receiver γ ∉α β
        → G′ -< γ # c >-> Gγ
        → ∃[ Gγ′ ] G -< γ # c >-> Gγ′

      -- Bisimulation stepback

      stepback/~ :
        ∀ {α G₀ G₁ G₁′}
        → G₁ ~ G₁′
        → G₀ -< α >-> G₁
        → ∃[ G₀′ ] (G₀ ~ G₀′) × (G₀′ -< α >-> G₁′)

      -- Diamond

      step-diamond :
        ∀ {G α G₁ α′ G₂}
        → G -< α  >-> G₁
        → G -< α′ >-> G₂
        → α ⋄ α′
        → ∃[ G′ ] (G₁ -< α′ >-> G′) × (G₂ -< α >-> G′)

    active-inactive/⋄ :
      ∀ {G Gα Gβ P α β}
      → G -< α >-> Gα
      → G -< β >-> Gβ
      → P ∈α α
      → P ∉α β
      → α ⋄ β
    active-inactive/⋄ {P = P} grα grβ P∈α P∉β =
      ¬∈c→∉c
        (λ rα∈β →
          ∉c→¬∈c P∉β
            (subst (λ γ → P ∈c γ)
              (recv-overlap⇒same-comm grα grβ rα∈β)
              P∈α))
      ,
      ¬∈c→∉c
        (λ rβ∈α →
          ∉c→¬∈c P∉β
            (subst (λ γ → P ∈c γ)
              (sym (recv-overlap⇒same-comm grβ grα rβ∈α))
              P∈α))

    unskip/advance :
      ∀ {G G′ Gα P α}
      → G -[¬ P ]->* G′
      → G -< α >-> Gα
      → P ∈α α
      → ∃[ G′α ] G′ -< α >-> G′α × Gα -[¬ P ]->* G′α
    unskip/advance unskip/refl grα _ =
      _ , grα , unskip/refl
    unskip/advance (unskip/step grβ P∉β tr) grα P∈α
      with step-diamond grα grβ (active-inactive/⋄ grα grβ P∈α P∉β)
    ... | G◇ , Gα↝G◇ , Gβ↝G◇
      with unskip/advance tr Gβ↝G◇ P∈α
    ... | G′α , G′↝G′α , G◇↝G′α =
      G′α , G′↝G′α , unskip/step Gα↝G◇ P∉β G◇↝G′α

    unskip/advance-step :
      ∀ {G G′ Gα P α}
      → (tr  : G -[¬ P ]->* G′)
      → (grα : G -< α >-> Gα)
      → (P∈α : P ∈α α)
      → G′ -< α >-> proj₁ (unskip/advance tr grα P∈α)
    unskip/advance-step tr grα P∈α =
      proj₁ (proj₂ (unskip/advance tr grα P∈α))

    unskip/advance-trace :
      ∀ {G G′ Gα P α}
      → (tr  : G -[¬ P ]->* G′)
      → (grα : G -< α >-> Gα)
      → (P∈α : P ∈α α)
      → Gα -[¬ P ]->* proj₁ (unskip/advance tr grα P∈α)
    unskip/advance-trace tr grα P∈α =
      proj₂ (proj₂ (unskip/advance tr grα P∈α))

    no-new-branch/unskip :
      ∀ {G G′ Gᵢ Gⱼ′ γ}
        {cᵢ cⱼ : Choice}
      → G -[¬ Comm.receiver γ ]->* G′
      → G  -< γ # cᵢ >-> Gᵢ
      → G′ -< γ # cⱼ >-> Gⱼ′
      → ∃[ Gⱼ ] G -< γ # cⱼ >-> Gⱼ
    no-new-branch/unskip unskip/refl grᵢ grⱼ =
      _ , grⱼ
    no-new-branch/unskip (unskip/step grβ recvγ∉β tr) grᵢ grⱼ′
      with step-diamond grᵢ grβ (active-inactive/⋄ grᵢ grβ (∈R refl) recvγ∉β)
    ... | _ , _ , grᵢ′
      with no-new-branch/unskip tr grᵢ′ grⱼ′
    ... | _ , grⱼ =
      no-new-branch/step grβ recvγ∉β grᵢ grⱼ

    branch/before :
      ∀ {G G′ Gᵢ Gⱼ′ γ}
        {cᵢ cⱼ : Choice}
      → (tr   : G -[¬ Comm.receiver γ ]->* G′)
      → (grᵢ  : G  -< γ # cᵢ >-> Gᵢ)
      → (grⱼ′ : G′ -< γ # cⱼ >-> Gⱼ′)
      → ∃[ Gⱼ ]
          (G -< γ # cⱼ >-> Gⱼ)
        × (Gⱼ -[¬ Comm.receiver γ ]->* Gⱼ′)
    branch/before tr grᵢ grⱼ′
      with no-new-branch/unskip tr grᵢ grⱼ′
    ... | Gⱼ , grⱼ
      with unskip/advance tr grⱼ (∈R refl)
    ... | _ , grⱼ″ , trⱼ
      rewrite step-deterministic grⱼ″ grⱼ′ =
      Gⱼ , grⱼ , trⱼ

    branch/before-step :
      ∀ {G G′ Gᵢ Gⱼ′ γ}
        {cᵢ cⱼ : Choice}
      → (tr   : G -[¬ Comm.receiver γ ]->* G′)
      → (grᵢ  : G  -< γ # cᵢ >-> Gᵢ)
      → (grⱼ′ : G′ -< γ # cⱼ >-> Gⱼ′)
      → G -< γ # cⱼ >-> proj₁ (branch/before tr grᵢ grⱼ′)
    branch/before-step tr grᵢ grⱼ′ =
      proj₁ (proj₂ (branch/before tr grᵢ grⱼ′))

    branch/before-trace :
      ∀ {G G′ Gᵢ Gⱼ′ γ}
        {cᵢ cⱼ : Choice}
      → (tr   : G -[¬ Comm.receiver γ ]->* G′)
      → (grᵢ  : G  -< γ # cᵢ >-> Gᵢ)
      → (grⱼ′ : G′ -< γ # cⱼ >-> Gⱼ′)
      → proj₁ (branch/before tr grᵢ grⱼ′)
          -[¬ Comm.receiver γ ]->* Gⱼ′
    branch/before-trace tr grᵢ grⱼ′ =
      proj₂ (proj₂ (branch/before tr grᵢ grⱼ′))
