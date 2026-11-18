{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)

open import Data.Vec using (Vec; lookup)
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  as Pointwise using (Pointwise)
open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Data.Fin.Subset using (_∈_; _∉_; Nonempty)
open import Data.Sum using (inj₁; inj₂)

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

open import Relation.Nullary using (¬_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_; _◅◅_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans) renaming (sym to ≡-sym)

module Definitions.Behav where

  import Definitions.Actions
  import Definitions.Common

  record BTheory (N : ℕ) : Set₁ where
    open Definitions.Actions N
    open Definitions.Common N

    field
      Behav : Set
      _-<_>->_ : Behav → Action → Behav → Set

    -- Traces.

    infix 4 _-[_]->_

    data _-[_]->_ : Behav → List Action → Behav → Set where
      tr/refl :
        ∀ {G} → G -[ [] ]-> G

      tr/step :
        ∀ {G G′ G″ α αs}
        → G -< α >-> G′
        → G′ -[ αs ]-> G″
        → G -[ α ∷ αs ]-> G″

    -- A step whose event at `P` is `e`: the triple `(α , eq , gr)`.
    infix 4 _-<[_↦_]>->_

    _-<[_↦_]>->_ : Behav → Part → Event → Behav → Set
    s -<[ P ↦ e ]>-> t = ∃[ α ] ev α P ≡ just e × s -< α >-> t

    action-of : ∀ {s P e t} → s -<[ P ↦ e ]>-> t → Action
    action-of = proj₁

    -- ── The paper's derived transitions and participation (Fig. 3) ──

    infix 4 _-⟨_⟩->_ _-⟨_⟩-> _-→ _-→*_ _-[¬_]->_ _-[¬_]->*_ _∈T_
            _first-in_

    -- G —R→ G′: a step in which a role of `R` takes part.
    _-⟨_⟩->_ : Behav → PartSet → Behav → Set
    G -⟨ R ⟩-> G′ = ∃[ α ] G -< α >-> G′ × R ∈αˢ α

    -- G —R→
    _-⟨_⟩-> : Behav → PartSet → Set
    G -⟨ R ⟩-> = ∃[ G′ ] G -⟨ R ⟩-> G′

    -- G →
    _-→ : Behav → Set
    G -→ = ∃[ α ] ∃[ G′ ] G -< α >-> G′

    -- G →* G′
    _-→*_ : Behav → Behav → Set
    _-→*_ = Star λ G G′ → ∃[ α ] G -< α >-> G′

    -- G —R̄→ G′ and G —R̄→* G′: steps in which no role of `R` takes part.
    _-[¬_]->_ : Behav → PartSet → Behav → Set
    G -[¬ R ]-> G′ = ∃[ α ] G -< α >-> G′ × R ∉αˢ α

    _-[¬_]->*_ : Behav → PartSet → Behav → Set
    G -[¬ R ]->* G′ = Star (_-[¬ R ]->_) G G′

    -- R ∈ G: a role of `R` acts after some run.
    _∈T_ : PartSet → Behav → Set
    R ∈T G = ∃[ G′ ] G -→* G′ × G′ -⟨ R ⟩->

    ended : Behav → Set
    ended G = ∀ P → ¬ P ∈T G

    -- r first-in (R , G): `r ∈ R`, and after any run free of `R`, every
    -- step in which `R` takes part involves `r`.
    _first-in_ : Part → PartSet × Behav → Set
    r first-in (R , G) =
      r ∈ R
      × (∀ {G′ α G″} → G -[¬ R ]->* G′ → G′ -< α >-> G″ → R ∈αˢ α → r ∈α α)

    in/α : ∀ {P G G′ α} → G -< α >-> G′ → P ∈αˢ α → P ∈T G
    in/α gr px = _ , ε , (_ , _ , gr , px)

    in/later : ∀ {P G G′ α} → G -< α >-> G′ → P ∈T G′ → P ∈T G
    in/later gr (G″ , run , act) = G″ , (_ , gr) ◅ run , act

    in/ev :
      ∀ {P Q e G α G′} → G -< α >-> G′ → Q ∈ P → ev α Q ≡ just e → P ∈T G
    in/ev gr Q∈ eq = in/α gr (_ , Q∈ , _ , eq)

    skip/one :
      ∀ {G G′ P α}
      → G -< α >-> G′
      → P ∉αˢ α
      → G -[¬ P ]->* G′
    skip/one gr P∉α = (_ , gr , P∉α) ◅ ε

    -- A step out of a state where `R` cannot act is free of `R`.
    ¬act⇒∉ : ∀ {R G α G′} → ¬ G -⟨ R ⟩-> → G -< α >-> G′ → R ∉αˢ α
    ¬act⇒∉ na gr own = na (_ , _ , gr , own)

    -- A trace none of whose actions involves `R` is a run free of `R`.
    tr⇒run :
      ∀ {R G G′ αs} → G -[ αs ]-> G′ → All (R ∉αˢ_) αs → G -[¬ R ]->* G′
    tr⇒run tr/refl          []          = ε
    tr⇒run (tr/step gr tr) (R∉ ∷ idle) = (_ , gr , R∉) ◅ tr⇒run tr idle

    first-in/skip :
      ∀ {r R G G′} → r first-in (R , G) → G -[¬ R ]->* G′ → r first-in (R , G′)
    first-in/skip (r∈ , f) run = r∈ , λ run′ → f (run ◅◅ run′)

    -- Bisimilarity, as in the paper: `∼` is the largest relation that is
    -- symmetric and closed under steps,
    --   G ∼ H ∧ G —α→ G′ ⟹ ∃ H′ . H —α→ H′ ∧ G′ ∼ H′.
    -- The record is coinductive, so it is that largest relation; its two
    -- fields are the paper's two conditions.  Its module is not opened
    -- (`sym` would clash with `_≡_`'s): use `~sym` and `~L` below, and
    -- `._~_.sym` / `._~_.step` to build one by copatterns.

    record _~_ (G H : Behav) : Set where
      coinductive
      field
        sym  : H ~ G
        step : ∀ {α G′} → G -< α >-> G′ → ∃[ H′ ] H -< α >-> H′ × G′ ~ H′

    ~sym : ∀ {G H} → G ~ H → H ~ G
    ~sym = _~_.sym

    ~L :
      ∀ {G G′ α G″}
      → G ~ G′
      → G -< α >-> G″
      → ∃[ G‴ ] G′ -< α >-> G‴ × G″ ~ G‴
    ~L G~G′ = _~_.step G~G′

    ~R :
      ∀ {G G′ α G‴}
      → G ~ G′
      → G′ -< α >-> G‴
      → ∃[ G″ ] G -< α >-> G″ × G″ ~ G‴
    ~R G~G′ gr =
      let _ , gr′ , b = ~L (~sym G~G′) gr
      in _ , gr′ , ~sym b

    ~refl : ∀ {G} → G ~ G
    ~refl ._~_.sym     = ~refl
    ~refl ._~_.step gr = _ , gr , ~refl

    ~trans : ∀ {G G′ G″} → G ~ G′ → G′ ~ G″ → G ~ G″
    ~trans G~G′ G′~G″ ._~_.sym = ~trans (~sym G′~G″) (~sym G~G′)
    ~trans G~G′ G′~G″ ._~_.step gr =
      let _ , gr′ , b′ = ~L G~G′ gr
          _ , gr″ , b″ = ~L G′~G″ gr′
      in _ , gr″ , ~trans b′ b″

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

    -- Bisimilar states have the same runs, with bisimilar endpoints.
    steps/~ : ∀ {G G′ H} → G ~ G′ → G -→* H → ∃[ H′ ] G′ -→* H′ × H ~ H′
    steps/~ G~G′ ε = _ , ε , G~G′
    steps/~ G~G′ ((α , gr) ◅ run) =
      let _ , gr′ , b  = ~L G~G′ gr
          _ , run′ , b′ = steps/~ b run
      in _ , (α , gr′) ◅ run′ , b′

    run/~ :
      ∀ {R G G′ H} → G ~ G′ → G -[¬ R ]->* H
      → ∃[ H′ ] G′ -[¬ R ]->* H′ × H ~ H′
    run/~ G~G′ ε = _ , ε , G~G′
    run/~ G~G′ ((α , gr , R∉) ◅ run) =
      let _ , gr′ , b  = ~L G~G′ gr
          _ , run′ , b′ = run/~ b run
      in _ , (α , gr′ , R∉) ◅ run′ , b′

    first-in/~ :
      ∀ {r R G H} → G ~ H → r first-in (R , G) → r first-in (R , H)
    first-in/~ G~H (r∈ , f) = r∈ , λ run gr own →
      let _ , run′ , H′~G′ = run/~ (~sym G~H) run
          _ , gr′ , _ = ~L H′~G′ gr
      in f run′ gr′ own

    ∈~ : ∀ {P G G′} → G ~ G′ → P ∈T G → P ∈T G′
    ∈~ G~G′ (H , run , (_ , _ , gr , own)) =
      let H′ , run′ , H~H′ = steps/~ G~G′ run
          _ , gr′ , _ = ~L H~H′ gr
      in H′ , run′ , (_ , _ , gr′ , own)

    ¬act/~ : ∀ {R G G′} → G ~ G′ → ¬ G -⟨ R ⟩-> → ¬ G′ -⟨ R ⟩->
    ¬act/~ G~G′ ¬act (_ , _ , gr , own) = ¬act (_ , _ , ~R→ G~G′ gr , own)

    -- Environment bisimilarity

    _~ᵛ_ : ∀ {δ δ′} → Vec Behav δ → Vec Behav δ′ → Set
    _~ᵛ_ = Pointwise _~_

    ~ᵛ-refl : ∀ {δ} {Δ : Vec Behav δ} → Δ ~ᵛ Δ
    ~ᵛ-refl = Pointwise.refl ~refl

    lookup/~ᵛ :
      ∀ {δ}
        {Δ Δ′ : Vec Behav δ}
        {G : Behav}
      → Δ ~ᵛ Δ′
      → (X : Fin δ)
      → lookup Δ X ~ G
      → lookup Δ′ X ~ G
    lookup/~ᵛ Δ~Δ′ X = ~trans (~sym (Pointwise.lookup Δ~Δ′ X))

  record WellBehaved {N : ℕ} (B : BTheory N) : Set₁ where
    open Definitions.Actions N
    open Definitions.Common N
    open BTheory B

    field
      -- A receiver of `α` that takes part in `α′` makes them one
      -- communication.

      -- (`overlap` would be the natural name, but it is an Agda keyword.)
      recv-overlap :
        ∀ {G α α′ G′ G″ Q}
        → G -< α  >-> G′
        → G -< α′ >-> G″
        → Recv α Q
        → Q ∈α α′
        → comm α ≡ comm α′

      -- Up to `~`: in a view, one action may reach two bisimilar states.
      step-deterministic :
        ∀ {G α G′ G″}
        → G -< α >-> G′
        → G -< α >-> G″
        → G′ ~ G″

      -- Sort determinism, for receive events only: a label fixes its sort.
      step-sort-det :
        ∀ {G G′ G″ α α′ P Q ℓ S T}
        → G -< α >-> G′
        → G -< α′ >-> G″
        → ev α Q ≡ just ((？ P) # ℓ < S >)
        → ev α′ Q ≡ just ((？ P) # ℓ < T >)
        → S ≡ T

      no-new-branch/step :
        ∀ {G G′ Gᵢ Gⱼ′ β γ γ′}
        → G -< β >-> G′
        → (∀ Q → Recv γ Q → Q ∉α β)
        → G  -< γ  >-> Gᵢ
        → G′ -< γ′ >-> Gⱼ′
        → comm γ′ ≡ comm γ
        → ∃[ Gⱼ ] G -< γ′ >-> Gⱼ

      -- Diamond

      step-diamond :
        ∀ {G α G₁ α′ G₂}
        → G -< α  >-> G₁
        → G -< α′ >-> G₂
        → α ⋄ α′
        → ∃[ X ] ∃[ Y ] (G₁ -< α′ >-> X) × (G₂ -< α >-> Y) × X ~ Y

    active-inactive/⋄ :
      ∀ {G Gα Gβ P α β}
      → G -< α >-> Gα
      → G -< β >-> Gβ
      → P ∈α α
      → P ∉α β
      → α ⋄ β
    active-inactive/⋄ {P = P} {α} {β} grα grβ P∈α P∉β =
      ∈∉→≢ {P} {α} {β} P∈α P∉β
      ,
      (λ Q rQ Q∈β →
        P∉β
          (comm-∈α {α} {β} {P} (recv-overlap {Q = Q} grα grβ rQ Q∈β) P∈α))
      ,
      (λ Q rQ Q∈α →
        P∉β
          (comm-∈α {α} {β} {P}
            (≡-sym (recv-overlap {Q = Q} grβ grα rQ Q∈α)) P∈α))

    -- If one receiver of `γ` is idle in `β`, all of them are: an active one
    -- would make `γ` and `β` the same communication.
    recv-idle/all :
      ∀ {G Gγ Gβ γ β R}
      → G -< γ >-> Gγ
      → G -< β >-> Gβ
      → Recv γ R
      → R ∉α β
      → ∀ Q → Recv γ Q → Q ∉α β
    recv-idle/all {γ = γ} {β} {R} grγ grβ rR R∉β Q rQ Q∈β =
      R∉β
        (comm-∈α {γ} {β} {R} (recv-overlap {Q = Q} grγ grβ rQ Q∈β)
          (Recv→∈α {γ} {R} rR))

    skip/advance :
      ∀ {G G′ Gα P α}
      → G -[¬ P ]->* G′
      → G -< α >-> Gα
      → P ∈αˢ α
      → ∃[ G′α ] G′ -< α >-> G′α × ∃[ Z ] Gα -[¬ P ]->* Z × Z ~ G′α
    skip/advance ε grα _ =
      _ , grα , _ , ε , ~refl
    skip/advance ((β , grβ , P∉β) ◅ run) grα P∈α@(X , X∈ , X∈α)
      with step-diamond grα grβ
             (active-inactive/⋄ grα grβ X∈α (∉αˢ-at {α = β} P∉β X∈))
    ... | _ , _ , Gα↝X , Gβ↝Y , X~Y
      with skip/advance run Gβ↝Y P∈α
    ... | G′α , G′↝G′α , _ , runY , Z~G′α =
      let _ , runX , Z~Z′ = run/~ (~sym X~Y) runY
      in G′α , G′↝G′α , _ , (_ , Gα↝X , P∉β) ◅ runX
       , ~trans (~sym Z~Z′) Z~G′α

    no-new-branch/skip :
      ∀ {G G′ Gᵢ Gⱼ′ γ γ′ P Q}
      → G -[¬ P ]->* G′
      → Q ∈ P
      → Recv γ Q
      → G  -< γ  >-> Gᵢ
      → G′ -< γ′ >-> Gⱼ′
      → comm γ′ ≡ comm γ
      → ∃[ Gⱼ ] G -< γ′ >-> Gⱼ
    no-new-branch/skip ε Q∈ rQ grᵢ grⱼ ceq =
      _ , grⱼ
    no-new-branch/skip {γ = γ} {Q = Q}
      ((β , grβ , P∉β) ◅ run) Q∈ rQ grᵢ grⱼ′ ceq
      with step-diamond grᵢ grβ
             (active-inactive/⋄ grᵢ grβ (Recv→∈α {γ} {Q} rQ)
               (∉αˢ-at {α = β} P∉β Q∈))
    ... | _ , _ , _ , grᵢ′ , _
      with no-new-branch/skip run Q∈ rQ grᵢ′ grⱼ′ ceq
    ... | _ , grⱼ =
      no-new-branch/step grβ
        (recv-idle/all grᵢ grβ rQ (∉αˢ-at {α = β} P∉β Q∈)) grᵢ grⱼ ceq

    branch/before :
      ∀ {G G′ Gᵢ Gⱼ′ γ γ′ P Q}
      → (tr   : G -[¬ P ]->* G′)
      → Q ∈ P
      → Recv γ Q
      → (grᵢ  : G  -< γ  >-> Gᵢ)
      → (grⱼ′ : G′ -< γ′ >-> Gⱼ′)
      → comm γ′ ≡ comm γ
      → ∃[ Gⱼ ] (G -< γ′ >-> Gⱼ) × ∃[ H ] (Gⱼ -[¬ P ]->* H) × H ~ Gⱼ′
    branch/before {γ = γ} {γ′} {Q = Q} tr Q∈ rQ grᵢ grⱼ′ ceq
      with no-new-branch/skip tr Q∈ rQ grᵢ grⱼ′ ceq
    ... | Gⱼ , grⱼ
      with skip/advance tr grⱼ
             (Q , Q∈ , comm-∈α {γ} {γ′} {Q} (≡-sym ceq) (Recv→∈α {γ} {Q} rQ))
    ... | _ , grⱼ″ , H , trⱼ , H~Gⱼ″ =
      Gⱼ , grⱼ , H , trⱼ , ~trans H~Gⱼ″ (step-deterministic grⱼ″ grⱼ′)

    -- Two receives by `Q`, one before and one after a run free of `Q`'s
    -- process, are the same communication.
    recv/same-comm :
      ∀ {G G′ Gγ Gγ′ γ γ′ P Q}
      → G -[¬ P ]->* G′
      → Q ∈ P
      → G -< γ >-> Gγ
      → Recv γ Q
      → G′ -< γ′ >-> Gγ′
      → Recv γ′ Q
      → comm γ′ ≡ comm γ
    recv/same-comm {γ = γ} {Q = Q} tr Q∈ grγ rQ grγ′ rQ′
      with skip/advance tr grγ (Q , Q∈ , Recv→∈α {γ} {Q} rQ)
    ... | _ , grγ-at-G′ , _ =
      recv-overlap {Q = Q} grγ′ grγ-at-G′ rQ′ (Recv→∈α {γ} {Q} rQ)

  -- Every step is one multicast.
  record Balanced {N : ℕ} (B : BTheory N) : Set₁ where
    open Definitions.Actions N
    open Definitions.Common N
    open BTheory B

    field
      -- Nonempty receivers, sender not among them.
      balanced :
        ∀ {G G′ α}
        → G -< α >-> G′
        → ∃[ P ] ∃[ Qs ] ∃[ c ] P ∉ Qs × Nonempty Qs × α ≡ P ⟶ Qs # c

    -- A step with a send event at `P` IS `P`'s multicast.
    send-action :
      ∀ {G G′ α P Qs c}
      → G -< α >-> G′
      → ev α P ≡ just ((! Qs) # c)
      → P ∉ Qs × α ≡ P ⟶ Qs # c
    send-action {P = P} gr eq with balanced gr
    ... | P′ , Qs′ , c′ , P′∉Qs′ , _ , refl with ev-inv {P′} {Qs′} {c′} {P} eq
    ...   | inj₁ (refl , refl) = P′∉Qs′ , refl
    ...   | inj₂ (_ , _ , ())

    -- The sender of a receive takes part in the same step.
    recv-sender :
      ∀ {G G′ α R P c}
      → G -< α >-> G′
      → ev α R ≡ just ((？ P) # c)
      → P ∈α α
    recv-sender {R = R} gr eq with balanced gr
    ... | P′ , Qs′ , c′ , _ , _ , refl with ev-inv {P′} {Qs′} {c′} {R} eq
    ...   | inj₁ (_ , ())
    ...   | inj₂ (_ , _ , refl) = _ , ev-sender {P′} {Qs′} {c′}

    -- … with a send event.
    recv-send :
      ∀ {G G′ α R P c}
      → G -< α >-> G′
      → ev α R ≡ just ((？ P) # c)
      → ∃[ Qs ] ∃[ c′ ] ev α P ≡ just ((! Qs) # c′)
    recv-send {R = R} gr eq with balanced gr
    ... | P′ , Qs′ , c′ , _ , _ , refl with ev-inv {P′} {Qs′} {c′} {R} eq
    ...   | inj₁ (_ , ())
    ...   | inj₂ (_ , _ , refl) = Qs′ , c′ , ev-sender {P′} {Qs′} {c′}

    -- `P`'s send event determines the action.
    send-det :
      ∀ {G G′ G″ α α′ P Qs c}
      → G -< α >-> G′
      → G -< α′ >-> G″
      → ev α P ≡ just ((! Qs) # c)
      → ev α′ P ≡ just ((! Qs) # c)
      → α ≡ α′
    send-det gr gr′ eq eq′ =
      trans (proj₂ (send-action gr eq)) (≡-sym (proj₂ (send-action gr′ eq′)))

    -- The steps the rules ask about are the paper's labelled steps: `p`'s
    -- send to `Qs` is the multicast `p ⟶ Qs # c`, and `q`'s receive from
    -- `p` is one of `p`'s multicasts to some `Qs ∋ q`.
    send⇒step :
      ∀ {G G′ P Qs c} → G -<[ P ↦ (! Qs) # c ]>-> G′ → G -< P ⟶ Qs # c >-> G′
    send⇒step (_ , eq , gr) with send-action gr eq
    ... | _ , refl = gr

    step⇒send :
      ∀ {G G′ P Qs c} → G -< P ⟶ Qs # c >-> G′ → G -<[ P ↦ (! Qs) # c ]>-> G′
    step⇒send {P = P} {Qs} {c} gr = _ , ev-sender {P} {Qs} {c} , gr

    recv⇒step :
      ∀ {G G′ P Q c} → G -<[ Q ↦ (？ P) # c ]>-> G′
      → ∃[ Qs ] Q ∈ Qs × G -< P ⟶ Qs # c >-> G′
    recv⇒step {Q = Q} (_ , eq , gr) with balanced gr
    ... | P′ , Qs′ , c′ , _ , _ , refl with ev-inv {P′} {Qs′} {c′} {Q} eq
    ...   | inj₁ (_ , ())
    ...   | inj₂ (_ , Q∈ , refl) = Qs′ , Q∈ , gr

    step⇒recv :
      ∀ {G G′ P Q Qs c} → Q ≢ P → Q ∈ Qs → G -< P ⟶ Qs # c >-> G′
      → G -<[ Q ↦ (？ P) # c ]>-> G′
    step⇒recv {P = P} {Qs = Qs} {c} Q≢P Q∈ gr =
      _ , ev-recv {P} {Qs} {c} Q≢P Q∈ , gr

  -- Balanced, and no communication first appears after an unrelated step.
  record Synchronous {N : ℕ} (B : BTheory N) : Set₁ where
    open Definitions.Actions N
    open Definitions.Common N
    open BTheory B

    field
      balanced :
        ∀ {G G′ α}
        → G -< α >-> G′
        → ∃[ P ] ∃[ Qs ] ∃[ c ] P ∉ Qs × Nonempty Qs × α ≡ P ⟶ Qs # c

      no-new-comm/step :
        ∀ {G G′ Gγ β γ}
        → G -< β >-> G′
        → (∀ X → X ∈α γ → X ∉α β)
        → G′ -< γ >-> Gγ
        → ∃[ Gγ′ ] G -< γ >-> Gγ′

    bal : Balanced B
    bal = record { balanced = balanced }

    open Balanced bal public using (send-action; recv-sender; send-det)
