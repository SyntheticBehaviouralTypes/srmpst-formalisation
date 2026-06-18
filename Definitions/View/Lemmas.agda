{-# OPTIONS --guardedness #-}

-- Facts about views used by the safety proofs.

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (_∈_; _∉_; ⁅_⁆)
open import Data.Fin.Subset.Properties using (_∈?_; x∈⁅y⁆⇒x≡y)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just)
open import Data.Product using (∃-syntax; _,_; _×_; proj₂)
open import Data.Unit using (⊤; tt)
open import Function using (id)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using () renaming (lookup to lu)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)

open import Definitions.Behav using (BTheory; WellBehaved; Synchronous)

module Definitions.View.Lemmas
  {N : ℕ} (B : BTheory N) (wb : WellBehaved B) (sync : Synchronous B)
  where

  open import Definitions.Common N
  open import Definitions.Actions N
  open import Definitions.Proc N using (Assignment)
  open import Definitions.View B
  open BTheory B
  open WellBehaved wb
  open Synchronous sync

  -- ══════════════════════════════════════════════════════════════════
  --  Senders
  -- ══════════════════════════════════════════════════════════════════

  -- A step has one sending role.
  sender/same :
    ∀ {G G′ α X Qs c Y Qs′ c′}
    → G -< α >-> G′
    → ev α X ≡ just ((! Qs) # c) → ev α Y ≡ just ((! Qs′) # c′)
    → Y ≡ X
  sender/same {X = X} {Y = Y} gr eqX eqY with balanced gr
  ... | P₀ , Qs₀ , c₀ , _ , _ , refl
    with ev-inv {P₀} {Qs₀} {c₀} {X} eqX | ev-inv {P₀} {Qs₀} {c₀} {Y} eqY
  ... | inj₁ (refl , _) | inj₁ (refl , _) = refl
  ... | inj₂ (_ , _ , ()) | _
  ... | _ | inj₂ (_ , _ , ())

  -- No step is internal to a single role: a sender is not its own
  -- receiver, and there is a receiver.
  singleton/external :
    ∀ {G G′ α X} → G -< α >-> G′ → ¬ Internal ⁅ X ⁆ α
  singleton/external {X = X} gr int with balanced gr
  ... | P , Qs , c , P∉ , (Q , Q∈) , refl
    with x∈⁅y⁆⇒x≡y X (int P (_ , ev-sender {P} {Qs} {c}))
       | x∈⁅y⁆⇒x≡y X
           (int Q (_ , ev-recv {P} {Qs} {c} {Q} (λ { refl → P∉ Q∈ }) Q∈))
  ... | refl | refl = P∉ Q∈

  -- A single role's view has exactly the steps of `B`.
  singleton⇒ :
    ∀ {X G α G″} → G -< α >-> G″ → _-<_>->ᵛ_ ⁅ X ⁆ G α G″
  singleton⇒ {X} {α = α} gr with ⁅ X ⁆ ∈αˢ? α
  ... | yes X∈ = inj₂ (singleton/external gr , X∈ , _ , ε , gr)
  ... | no  X∉ = inj₁ (¬∈αˢ→∉αˢ {⁅ X ⁆} {α} X∉ , gr)

  singleton⇐ :
    ∀ {X G α G″} → _-<_>->ᵛ_ ⁅ X ⁆ G α G″ → G -< α >-> G″
  singleton⇐ (inj₁ (_ , gr))                            = gr
  singleton⇐ (inj₂ (_ , _ , _ , ε , gr))                 = gr
  singleton⇐ (inj₂ (_ , _ , _ , (_ , g , int) ◅ _ , _)) =
    ⊥-elim (singleton/external g int)

  -- ══════════════════════════════════════════════════════════════════
  --  Commuting steps of disjoint blocks
  -- ══════════════════════════════════════════════════════════════════

  -- Nobody takes part in both.
  Apart : Action → Action → Set
  Apart a b = ∀ Z → Z ∈α b → Z ∉α a

  -- `b` after `a`, where they share no participant: `b` was available
  -- before `a` (`no-new-comm/step`), and the two commute up to `~`.
  swap :
    ∀ {G X Y a b}
    → G -< a >-> X → X -< b >-> Y → Apart a b
    → ∃[ X′ ] ∃[ Y′ ] G -< b >-> X′ × X′ -< a >-> Y′ × Y′ ~ Y
  swap {a = a} {b} gra grb apart
    with no-new-comm/step gra apart grb
  ... | X′ , grb′
    with step-diamond gra grb′ ind
    where
      ind : a ⋄ b
      ind =
        (λ { refl → actor grb λ Z Z∈ → ∉α→¬∈α {Z} {b} (apart Z Z∈) Z∈ })
        , (λ Q rQ → ¬∈α→∉α {Q} {b} λ Q∈b →
             ∉α→¬∈α {Q} {a} (apart Q Q∈b) (Recv→∈α {a} {Q} rQ))
        , (λ Q rQ → apart Q (Recv→∈α {b} {Q} rQ))
        where
          actor : ∀ {u v} → u -< b >-> v → (∀ Z → Z ∈α b → ⊥) → ⊥
          actor gr none with balanced gr
          ... | P , Qs , c , _ , _ , refl = none P (_ , ev-sender {P} {Qs} {c})
  ... | X₂ , Y′ , grb″ , gra′ , X₂~Y′ =
    X′ , Y′ , grb′ , gra′
    , ~trans (~sym X₂~Y′) (~sym (step-deterministic grb grb″))

  -- `a`, then a run sharing no participant with it: the run first.
  push-aux :
    ∀ {G X X′ H a bs}
    → G -< a >-> X′ → X′ ~ X → X -[ bs ]-> H → All (Apart a) bs
    → ∃[ H₀ ] ∃[ H′ ] G -[ bs ]-> H₀ × H₀ -< a >-> H′ × H′ ~ H
  push-aux gra X′~X tr/refl [] = _ , _ , tr/refl , gra , X′~X
  push-aux gra X′~X (tr/step grb tr) (apart ∷ aparts)
    with ~R X′~X grb
  ... | Y₁ , grb₁ , Y₁~Y
    with swap gra grb₁ apart
  ... | X″ , Y′ , grb′ , gra′ , Y′~Y₁
    with push-aux gra′ (~trans Y′~Y₁ Y₁~Y) tr aparts
  ... | H₀ , H′ , tr′ , gra″ , H′~H =
    H₀ , H′ , tr/step grb′ tr′ , gra″ , H′~H

  -- Within a block's run: the steps it takes no part in first, then its
  -- own internal steps.
  module _ {Ps : PartSet} where

    -- A step internal to `Ps`, or one `Ps` takes no part in.
    Mixed : Behav → Behav → Set
    Mixed G G′ = ∃[ γ ] G -< γ >-> G′ × (Internal Ps γ ⊎ Ps ∉αˢ γ)

    τs/~ :
      ∀ {G H G₁}
      → G ~ H → Star (_-τ->_ Ps) G G₁
      → ∃[ H₁ ] Star (_-τ->_ Ps) H H₁ × G₁ ~ H₁
    τs/~ G~H ε = _ , ε , G~H
    τs/~ G~H ((γ , gr , int) ◅ τs) =
      let _ , gr′ , G′~H′ = ~L G~H gr
          H₁ , τs′ , G₁~H₁ = τs/~ G′~H′ τs
      in H₁ , (γ , gr′ , int) ◅ τs′ , G₁~H₁

    -- `Mixed`, with a property `Q` of the label that `split` remembers
    -- for the steps it moves first.
    Mixed/ : (Action → Set) → Behav → Behav → Set
    Mixed/ Q G G′ =
      ∃[ γ ] G -< γ >-> G′ × Q γ × (Internal Ps γ ⊎ Ps ∉αˢ γ)

    split/ :
      ∀ {Q G G₁}
      → Star (Mixed/ Q) G G₁
      → ∃[ H ] ∃[ H₁ ]
          (∃[ bs ] G -[ bs ]-> H × All (λ b → Q b × Ps ∉αˢ b) bs)
          × Star (_-τ->_ Ps) H H₁ × H₁ ~ G₁
    split/ ε = _ , _ , ([] , tr/refl , []) , ε , ~refl
    split/ ((γ , gr , q , inj₂ idle) ◅ rest) =
      let H , H₁ , (bs , tr , qs) , τs , H₁~G₁ = split/ rest
      in H , H₁ , (γ ∷ bs , tr/step gr tr , (q , idle) ∷ qs) , τs , H₁~G₁
    split/ ((γ , gr , _ , inj₁ int) ◅ rest)
      with split/ rest
    ... | H , H₁ , (bs , tr , qs) , τs , H₁~G₁
      with push-aux gr ~refl tr
             (All.map
                (λ {b} (_ , idle) Z Z∈b → ¬∈α→∉α {Z} {γ} λ Z∈γ →
                   ∉α→¬∈α {Z} {b} (idle Z (int Z Z∈γ)) Z∈b)
                qs)
    ... | H₀ , H′ , tr′ , grγ , H′~H =
      let H₁′ , τs′ , H₁~H₁′ = τs/~ (~sym H′~H) τs
      in H₀ , H₁′ , (bs , tr′ , qs) , (γ , grγ , int) ◅ τs′
         , ~trans (~sym H₁~H₁′) H₁~G₁

    split :
      ∀ {G G₁}
      → Star Mixed G G₁
      → ∃[ H ] ∃[ H₁ ]
          G -[¬ Ps ]->* H × Star (_-τ->_ Ps) H H₁ × H₁ ~ G₁
    split mixed
      with split/ {Q = λ _ → ⊤}
             (Star.gmap id (λ (γ , gr , m) → γ , gr , tt , m) mixed)
    ... | H , H₁ , (bs , tr , qs) , τs , H₁~G₁ =
      H , H₁ , (bs , tr , All.map proj₂ qs) , τs , H₁~G₁

  -- ══════════════════════════════════════════════════════════════════
  --  The local view of a block
  -- ══════════════════════════════════════════════════════════════════

  module _ {Ps : PartSet} where

    private
      module V = BTheory (view Ps)

    local/idle :
      ∀ {G α G″} → Ps ∉αˢ α → G -< α >-> G″ → _-<_>->ᵛ_ Ps G α G″
    local/idle idle gr = inj₁ (idle , gr)

    -- Bisimilar in `B`, bisimilar in the local view.
    mutual
      ≲ᴸ : ∀ {G H} → G ~ H → G V.≲ H
      ≲ᴸ G~H .V._≲_.simulate (inj₁ (idle , gr)) =
        let _ , gr′ , b = ~L G~H gr
        in _ , inj₁ (idle , gr′) , local/~ b
      ≲ᴸ G~H .V._≲_.simulate (inj₂ (¬int , own , G₁ , τs , gr)) =
        let H₁ , τs′ , G₁~H₁ = τs/~ G~H τs
            _ , gr′ , b = ~L G₁~H₁ gr
        in _ , inj₂ (¬int , own , H₁ , τs′ , gr′) , local/~ b

      local/~ : ∀ {G H} → G ~ H → G V.~ H
      local/~ G~H = ≲ᴸ G~H , ≲ᴸ (~sym G~H)

  -- ══════════════════════════════════════════════════════════════════
  --  The global view of an assignment
  -- ══════════════════════════════════════════════════════════════════

  module _ {K : ℕ} (Ρ : Assignment K) where

    open Assignment Ρ
    open Global Ρ

    -- A global step after a `β` that involves no block of `α`'s
    -- participants was available before `β`.
    pullback :
      ∀ {G t t′ α β}
      → G -< β >-> t → (∀ X → X ∈α α → block X ∉αˢ β)
      → t -< α >->ᵍ t′ → ∃[ G′ ] G -< α >->ᵍ G′
    pullback {α = α} {β} grβ apart (¬hid , t₁ , τs , grα) =
      let G₁ , G′ , τs′ , grα′ = pull grβ ~refl τs grα
      in G′ , ¬hid , G₁ , τs′ , grα′
      where
        apart/α : ∀ Z → Z ∈α α → Z ∉α β
        apart/α Z Z∈α = apart Z Z∈α Z (owner/∈ Z)

        pull :
          ∀ {G u u′ t₁ t″}
          → G -< β >-> u′ → u′ ~ u → Star τ⟨ α ⟩ u t₁ → t₁ -< α >-> t″
          → ∃[ G₁ ] ∃[ G′ ] Star τ⟨ α ⟩ G G₁ × G₁ -< α >-> G′
        pull grβ u′~u ε grα =
          let _ , grα′ , _ = ~R u′~u grα
          in _ , _ , ε , proj₂ (no-new-comm/step grβ apart/α grα′)
        pull grβ u′~u ((γ , grγ , X , X∈α , int) ◅ τs) grα =
          let _ , grγ′ , v′~v = ~R u′~u grγ
              _ , _ , grγG , grβ′ , Y′~v′ =
                swap grβ grγ′ (λ Z Z∈γ → apart X X∈α Z (int Z Z∈γ))
              G₁ , G′ , τs′ , grα′ = pull grβ′ (~trans Y′~v′ v′~v) τs grα
          in G₁ , G′ , (γ , grγG , X , X∈α , int) ◅ τs′ , grα′

    -- Process `j`'s block, against the global view.
    module Projection (j : Fin K) where

      private
        Ps = lu roles j

        Ps-block : ∀ {X} → X ∈ Ps → block X ≡ Ps
        Ps-block X∈ = cong (lu roles) (∈/owner X∈)

        outside : ∀ {X Z} → X ∉ Ps → Z ∈ block X → Z ∉ Ps
        outside {X} X∉ Z∈ Z∈Ps =
          X∉ (subst (λ k → X ∈ lu roles k)
                    (trans (sym (∈/owner Z∈)) (∈/owner Z∈Ps))
                    (owner/∈ X))

        -- Another block's internal step is an outsiders' step to `Ps`.
        classify : ∀ {G G′ α} → τ⟨ α ⟩ G G′ → Mixed {Ps} G G′
        classify (γ , gr , X , _ , int) with X ∈? Ps
        ... | yes X∈ =
          γ , gr , inj₁ (subst (λ b → Internal b γ) (Ps-block X∈) int)
        ... | no X∉ =
          γ , gr , inj₂ λ Z Z∈Ps → ¬∈α→∉α {Z} {γ} λ Z∈γ →
            outside X∉ (int Z Z∈γ) Z∈Ps

        idle* :
          ∀ {G G₁ α} → Ps ∉αˢ α → Star τ⟨ α ⟩ G G₁ → G -[¬ Ps ]->* G₁
        idle* idle ε = skip/refl
        idle* {α = α} idle ((γ , gr , X , X∈α , int) ◅ τs) =
          tr¬/step gr
            (λ Z Z∈Ps → ¬∈α→∉α {Z} {γ} λ Z∈γ →
               outside (λ X∈Ps → ∉α→¬∈α {X} {α} (idle X X∈Ps) X∈α)
                 (int Z Z∈γ) Z∈Ps)
            (idle* {α = α} idle τs)

      -- `Ps` takes no part: outsiders' steps only.
      project/idle :
        ∀ {G α G′} → Ps ∉αˢ α → G -< α >->ᵍ G′ → G -[¬ Ps ]->* G′
      project/idle {α = α} idle (_ , _ , τs , gr) =
        skip/cat (idle* {α = α} idle τs) (skip/one gr idle)

      -- `Ps` takes part: outsiders' steps, then a step of the local view.
      project/own :
        ∀ {G α G′}
        → Ps ∈αˢ α → G -< α >->ᵍ G′
        → ∃[ H ] ∃[ H′ ] G -[¬ Ps ]->* H × _-<_>->ᵛ_ Ps H α H′ × H′ ~ G′
      project/own {α = α} own@(X₀ , X₀∈ , X₀∈α) (¬hid , G₁ , τs , gr)
        with split {Ps} (Star.gmap id (classify {α = α}) τs)
      ... | H , H₁ , tr , τs′ , H₁~G₁
        with ~R H₁~G₁ gr
      ... | H′ , gr′ , H′~G′ =
        H , H′ , tr , inj₂ (¬int , own , H₁ , τs′ , gr′) , H′~G′
        where
          ¬int : ¬ Internal Ps α
          ¬int int =
            ¬hid ( X₀ , X₀∈α
                 , subst (λ b → Internal b α) (sym (Ps-block X₀∈)) int )

      -- An own step of the local view is a global step.
      own/global :
        ∀ {G α G″} → Ps ∈αˢ α → _-<_>->ᵛ_ Ps G α G″ → G -< α >->ᵍ G″
      own/global {α = α} (X , X∈ , X∈α) (inj₁ (idle , _)) =
        ⊥-elim (∉α→¬∈α {X} {α} (idle X X∈) X∈α)
      own/global {α = α} _ (inj₂ (¬int , (X₀ , X₀∈ , X₀∈α) , G₁ , τs , gr)) =
        ¬hid , G₁ , Star.gmap id lift τs , gr
        where
          ¬hid : ¬ Hidden α
          ¬hid (X , X∈α , int) =
            ¬int λ Z Z∈α →
              subst (Z ∈_)
                (trans (cong (lu roles) (sym (∈/owner (int X₀ X₀∈α))))
                       (Ps-block X₀∈))
                (int Z Z∈α)

          lift : ∀ {u v} → _-τ->_ Ps u v → τ⟨ α ⟩ u v
          lift (γ , grγ , int) =
            γ , grγ , X₀ , X₀∈α
            , subst (λ b → Internal b γ) (sym (Ps-block X₀∈)) int
