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
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllProp

open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)

module Definitions.Behav where

  import Definitions.Actions
  import Definitions.Common

  record BTheory (N : ℕ) : Set₁ where
    open Definitions.Actions N
    open Definitions.Common N

    field
      Behav : Set
      _-<_>->_ : Behav → Action → Behav → Set

    -- Participation of a set of roles.

    _not-active-in_ : PartSet → Behav → Set
    P not-active-in G =
      ∀ {α G′} → G -< α >-> G′ → P ∉αˢ α

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

    tr/trans :
      ∀ {G G′ G″ αs βs}
      → G -[ αs ]-> G′ → G′ -[ βs ]-> G″ → G -[ αs ++ βs ]-> G″
    tr/trans tr/refl tr′         = tr′
    tr/trans (tr/step gr tr) tr′ = tr/step gr (tr/trans tr tr′)

    -- A step whose event at `P` is `e`: the triple `(α , eq , gr)`.
    infix 4 _-<[_↦_]>->_

    _-<[_↦_]>->_ : Behav → Part → Event → Behav → Set
    s -<[ P ↦ e ]>-> t = ∃[ α ] ev α P ≡ just e × s -< α >-> t

    -- A step with event `e` at `R`, sent from outside `Q`.
    infix 4 _-<[_∣_↦_]>->_

    _-<[_∣_↦_]>->_ : Behav → PartSet → Part → Event → Behav → Set
    s -<[ Q ∣ R ↦ e ]>-> t =
      ∃[ α ] ev α R ≡ just e × s -< α >-> t × Foreign Q α

    -- `P ∈T G`: some trace from `G` mentions `P`.  `G -[¬ P ]->* G′`: a
    -- trace to `G′` that never mentions `P`.

    _∈T_ : PartSet → Behav → Set
    P ∈T G = ∃[ αs ] ∃[ G′ ] (G -[ αs ]-> G′) × Any (P ∈αˢ_) αs

    ended : Behav → Set
    ended G = ∀ P → ¬ P ∈T G

    infix 4 _-[¬_]->*_

    _-[¬_]->*_ : Behav → PartSet → Behav → Set
    G -[¬ P ]->* G′ = ∃[ αs ] (G -[ αs ]-> G′) × All (P ∉αˢ_) αs


    in/α : ∀ {P G G′ α} → G -< α >-> G′ → P ∈αˢ α → P ∈T G
    in/α gr px = _ ∷ [] , _ , tr/step gr tr/refl , here px

    in/later : ∀ {P G G′ α} → G -< α >-> G′ → P ∈T G′ → P ∈T G
    in/later gr (αs , G″ , tr , mem) = _ ∷ αs , G″ , tr/step gr tr , there mem

    in/ev :
      ∀ {P Q e G α G′} → G -< α >-> G′ → Q ∈ P → ev α Q ≡ just e → P ∈T G
    in/ev gr Q∈ eq = in/α gr (_ , Q∈ , _ , eq)

    skip/refl : ∀ {G P} → G -[¬ P ]->* G
    skip/refl = [] , tr/refl , []

    tr¬/step :
      ∀ {G G′ G″ P α}
      → G -< α >-> G′ → P ∉αˢ α → G′ -[¬ P ]->* G″ → G -[¬ P ]->* G″
    tr¬/step gr P∉α (αs , tr , allP) = _ ∷ αs , tr/step gr tr , P∉α ∷ allP

    skip/one :
      ∀ {G G′ P α}
      → G -< α >-> G′
      → P ∉αˢ α
      → G -[¬ P ]->* G′
    skip/one gr P∉α =
      tr¬/step gr P∉α skip/refl

    skip/cat :
      ∀ {G G′ G″ P}
      → G -[¬ P ]->* G′
      → G′ -[¬ P ]->* G″
      → G -[¬ P ]->* G″
    skip/cat (αs , tr , allP) (βs , tr′ , allP′) =
      αs ++ βs , tr/trans tr tr′ , AllProp.++⁺ allP allP′

    -- `P` acts at role `X` only, at `G` and wherever outsiders move `G`.
    Focus : PartSet → Part → Behav → Set
    Focus P X G =
      ∀ {G′ β G″} → G -[¬ P ]->* G′ → G′ -< β >-> G″ → P ∈αˢ β → X ∈α β

    focus/skip :
      ∀ {P X G G′} → Focus P X G → G -[¬ P ]->* G′ → Focus P X G′
    focus/skip f tr tr′ = f (skip/cat tr tr′)

    -- Bisimilarity

    mutual
      record _≲_ (G G′ : Behav) : Set where
        coinductive
        field
          simulate :
            ∀ {α G″}
            → G -< α >-> G″
            → ∃[ G‴ ] G′ -< α >-> G‴ × G″ ~ G‴

      _~_ : Behav → Behav → Set
      G ~ G′ = G ≲ G′ × G′ ≲ G

    open _≲_

    mutual
      ≲refl : ∀ {G} → G ≲ G
      simulate ≲refl gr =
        _ , gr , ~refl

      ~refl : ∀ {G} → G ~ G
      ~refl =
        ≲refl , ≲refl

    ~sym : ∀ {G G′} → G ~ G′ → G′ ~ G
    ~sym (G≲G′ , G′≲G) =
      G′≲G , G≲G′

    mutual
      ≲trans : ∀ {G G′ G″} → G ≲ G′ → G′ ≲ G″ → G ≲ G″
      simulate (≲trans G≲G′ G′≲G″) gr =
        let _ , gr′ , b′ = simulate G≲G′ gr
            _ , gr″ , b″ = simulate G′≲G″ gr′
        in _ , gr″ , ~trans b′ b″

      ~trans : ∀ {G G′ G″} → G ~ G′ → G′ ~ G″ → G ~ G″
      ~trans (G≲G′ , G′≲G) (G′≲G″ , G″≲G′) =
        ≲trans G≲G′ G′≲G″ , ≲trans G″≲G′ G′≲G

    ~L :
      ∀ {G G′ α G″}
      → G ~ G′
      → G -< α >-> G″
      → ∃[ G‴ ] G′ -< α >-> G‴ × G″ ~ G‴
    ~L (G≲G′ , _) =
      simulate G≲G′

    ~R :
      ∀ {G G′ α G‴}
      → G ~ G′
      → G′ -< α >-> G‴
      → ∃[ G″ ] G -< α >-> G″ × G″ ~ G‴
    ~R (_ , G′≲G) gr =
      let _ , gr′ , b = simulate G′≲G gr
      in _ , gr′ , ~sym b

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

    -- Bisimilar states have the same traces, with bisimilar endpoints.
    tr-transport :
      ∀ {G G′ H αs}
      → G ~ G′
      → G -[ αs ]-> H
      → ∃[ H′ ] (G′ -[ αs ]-> H′) × (H ~ H′)
    tr-transport G~G′ tr/refl =
      _ , tr/refl , G~G′
    tr-transport G~G′ (tr/step gr tr) =
      let _ , gr′ , G″~G‴ = ~L G~G′ gr
          _ , tr′ , H~H′  = tr-transport G″~G‴ tr
      in _ , tr/step gr′ tr′ , H~H′

    focus/~ : ∀ {P X G H} → G ~ H → Focus P X G → Focus P X H
    focus/~ G~H f (αs , tr , idles) gr own =
      let _ , tr′ , H′~G′ = tr-transport (~sym G~H) tr
          _ , gr′ , _ = ~L H′~G′ gr
      in f (αs , tr′ , idles) gr′ own

    ∈~ : ∀ {P G G′} → G ~ G′ → P ∈T G → P ∈T G′
    ∈~ G~G′ (αs , H , tr , mem) =
      let H′ , tr′ , _ = tr-transport G~G′ tr
      in αs , H′ , tr′ , mem

    na-bisim :
      ∀ {P G G′}
      → G ~ G′
      → P not-active-in G
      → P not-active-in G′
    na-bisim G~G′ na gr =
      na (~R→ G~G′ gr)

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

      -- Sort/arity determinism, for receive events only.
      step-sort-det :
        ∀ {G G′ G″ α α′ P Q I S T}
          {i : Fin (suc I)}
        → G -< α >-> G′
        → G -< α′ >-> G″
        → ev α Q ≡ just ((？ P) # i < S >)
        → ev α′ Q ≡ just ((？ P) # i < T >)
        → S ≡ T

      step-arity-det :
        ∀ {G G′ G″ α α′ P Q I J S T}
          {i : Fin (suc I)}
          {j : Fin (suc J)}
        → G -< α >-> G′
        → G -< α′ >-> G″
        → ev α Q ≡ just ((？ P) # i < S >)
        → ev α′ Q ≡ just ((？ P) # j < T >)
        → I ≡ J

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
      (λ Q rQ → ¬∈α→∉α {Q} {β} λ Q∈β →
        ∉α→¬∈α {P} {β} P∉β
          (comm-∈α {α} {β} {P} (recv-overlap {Q = Q} grα grβ rQ Q∈β) P∈α))
      ,
      (λ Q rQ → ¬∈α→∉α {Q} {α} λ Q∈α →
        ∉α→¬∈α {P} {β} P∉β
          (comm-∈α {α} {β} {P}
            (sym (recv-overlap {Q = Q} grβ grα rQ Q∈α)) P∈α))

    -- If one receiver of `γ` is idle in `β`, all of them are: an active one
    -- would make `γ` and `β` the same communication.
    recv-idle/all :
      ∀ {G Gγ Gβ γ β R}
      → G -< γ >-> Gγ
      → G -< β >-> Gβ
      → Recv γ R
      → R ∉α β
      → ∀ Q → Recv γ Q → Q ∉α β
    recv-idle/all {γ = γ} {β} {R} grγ grβ rR R∉β Q rQ =
      ¬∈α→∉α {Q} {β} λ Q∈β →
        ∉α→¬∈α {R} {β} R∉β
          (comm-∈α {γ} {β} {R} (recv-overlap {Q = Q} grγ grβ rQ Q∈β)
            (Recv→∈α {γ} {R} rR))

    -- The `-aux` helpers take the run curried: repacking it into a Σ at
    -- each call hides the structural recursion from the termination checker.

    skip/advance-aux :
      ∀ {G G′ Gα P α αs}
      → G -[ αs ]-> G′
      → All (P ∉αˢ_) αs
      → G -< α >-> Gα
      → P ∈αˢ α
      → ∃[ G′α ] G′ -< α >-> G′α × ∃[ Z ] Gα -[¬ P ]->* Z × Z ~ G′α
    skip/advance-aux tr/refl [] grα _ =
      _ , grα , _ , skip/refl , ~refl
    skip/advance-aux (tr/step grβ tr) (P∉β ∷ allP) grα P∈α@(X , X∈ , X∈α)
      with step-diamond grα grβ (active-inactive/⋄ grα grβ X∈α (P∉β X X∈))
    ... | _ , _ , Gα↝X , Gβ↝Y , X~Y
      with skip/advance-aux tr allP Gβ↝Y P∈α
    ... | G′α , G′↝G′α , _ , (βs , trY , allP′) , Z~G′α =
      let _ , trX , Z~Z′ = tr-transport (~sym X~Y) trY
      in G′α , G′↝G′α , _ , tr¬/step Gα↝X P∉β (βs , trX , allP′)
       , ~trans (~sym Z~Z′) Z~G′α

    skip/advance :
      ∀ {G G′ Gα P α}
      → G -[¬ P ]->* G′
      → G -< α >-> Gα
      → P ∈αˢ α
      → ∃[ G′α ] G′ -< α >-> G′α × ∃[ Z ] Gα -[¬ P ]->* Z × Z ~ G′α
    skip/advance (_ , tr , allP) =
      skip/advance-aux tr allP

    no-new-branch/skip-aux :
      ∀ {G G′ Gᵢ Gⱼ′ γ γ′ P Q αs}
      → G -[ αs ]-> G′
      → All (P ∉αˢ_) αs
      → Q ∈ P
      → Recv γ Q
      → G  -< γ  >-> Gᵢ
      → G′ -< γ′ >-> Gⱼ′
      → comm γ′ ≡ comm γ
      → ∃[ Gⱼ ] G -< γ′ >-> Gⱼ
    no-new-branch/skip-aux tr/refl [] Q∈ rQ grᵢ grⱼ ceq =
      _ , grⱼ
    no-new-branch/skip-aux {γ = γ} {Q = Q}
      (tr/step grβ tr) (P∉β ∷ allP) Q∈ rQ grᵢ grⱼ′ ceq
      with step-diamond grᵢ grβ
             (active-inactive/⋄ grᵢ grβ (Recv→∈α {γ} {Q} rQ) (P∉β Q Q∈))
    ... | _ , _ , _ , grᵢ′ , _
      with no-new-branch/skip-aux tr allP Q∈ rQ grᵢ′ grⱼ′ ceq
    ... | _ , grⱼ =
      no-new-branch/step grβ (recv-idle/all grᵢ grβ rQ (P∉β Q Q∈)) grᵢ grⱼ
        ceq

    no-new-branch/skip :
      ∀ {G G′ Gᵢ Gⱼ′ γ γ′ P Q}
      → G -[¬ P ]->* G′
      → Q ∈ P
      → Recv γ Q
      → G  -< γ  >-> Gᵢ
      → G′ -< γ′ >-> Gⱼ′
      → comm γ′ ≡ comm γ
      → ∃[ Gⱼ ] G -< γ′ >-> Gⱼ
    no-new-branch/skip (_ , tr , allP) =
      no-new-branch/skip-aux tr allP

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
             (Q , Q∈ , comm-∈α {γ} {γ′} {Q} (sym ceq) (Recv→∈α {γ} {Q} rQ))
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

    -- `P`'s send event determines the action.
    send-det :
      ∀ {G G′ G″ α α′ P Qs c}
      → G -< α >-> G′
      → G -< α′ >-> G″
      → ev α P ≡ just ((! Qs) # c)
      → ev α′ P ≡ just ((! Qs) # c)
      → α ≡ α′
    send-det gr gr′ eq eq′ =
      trans (proj₂ (send-action gr eq)) (sym (proj₂ (send-action gr′ eq′)))

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
