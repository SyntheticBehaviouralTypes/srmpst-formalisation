{-# OPTIONS --guardedness #-}

-- The paper's typing rules (`sections/roles.tex`, Fig. 4), on the
-- bisimilarity classes of a theory (Fig. 3, `Definitions.Classes`).
--
--   Γ & Δ ⊢[ R ] P ∶ G        is   Γ; Δ ⊢_R P : G
--   Γ & Δ & Ξ ⊢[ R ] P ∶ G    is   Γ; Δ; Ξ ⊢_R P : G
--
-- Agda departs from the paper only where the paper's section is
-- point-to-point: a send names its receivers `Qs`, and a receive asks
-- `p ∉ R`, as the paper's multicast rules do.

open import Data.Nat using (ℕ; suc)
import Data.Fin.Subset as Subset
open import Data.Maybe using (Maybe)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Vec using (Vec; []; _∷_) renaming (lookup to lu)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Utils.Family using (_∋_↦_)
open import Definitions.Proc using (Assignment)

module Definitions.Typing.Declarative where

open import Definitions.Expr public
open import Definitions.Behav public

module MPST {N : ℕ} {B : BTheory N} (wb : WellBehaved B) where

  open import Definitions.Common  N public
  open import Definitions.Proc    N public
  open import Definitions.Actions N public
  open import Definitions.Classes B public

  -- ══════════════════════════════════════════════════════════════════
  --  The paper's notions, and its rules, on classes
  -- ══════════════════════════════════════════════════════════════════

  module Paper where

    -- The paper's notions (Fig. 3), on classes.
    open C public
      using ( _-<_>->_; _-<[_↦_]>->_; _-⟨_⟩->_; _-⟨_⟩->; _-→; _-→*_
            ; _-[¬_]->_; _-[¬_]->*_; _∈T_; _first-in_ )

    private
      variable
        γ δ ξ : ℕ

    -- `Δ ▸ G` and `Ξ ▸ G`, the paper's `Δ, X : G` and `Ξ, G` (de Bruijn:
    -- the newest entry is the head).
    infixl 5 _▸_

    pattern _▸_ xs x = x ∷ xs

    -- One membership symbol, as the paper's `∈`: `r ∈ R`, `R ∈ α`,
    -- `r ∈ α`, `R ∈ G` and `G ∈ Ξ`.
    record Membership (A B : Set) : Set₁ where
      infix 4 _∈_
      field _∈_ : A → B → Set

    open Membership {{...}} public

    infix 4 _∉_

    _∉_ : ∀ {A B : Set} {{_ : Membership A B}} → A → B → Set
    x ∉ y = ¬ (x ∈ y)

    instance
      ∈-role-roles : Membership Part PartSet
      ∈-role-roles = record { _∈_ = Subset._∈_ }

      ∈-roles-action : Membership PartSet Action
      ∈-roles-action = record { _∈_ = _∈αˢ_ }

      ∈-role-action : Membership Part Action
      ∈-role-action = record { _∈_ = _∈α_ }

      ∈-roles-class : Membership PartSet Cls
      ∈-roles-class = record { _∈_ = _∈T_ }

      ∈-class-ctx : ∀ {ξ} → Membership Cls (Vec Cls ξ)
      ∈-class-ctx = record { _∈_ = _∈ᵛ_ }

    -- G —p→q:ℓ(t)→ G′, at the sender `p` (to all of `Qs`) and at a
    -- receiver `q`.
    infix 4 _-[_⇒_∶_]->_ _-[_⇐_∶_]->_ _-[_⇐_]->

    _-[_⇒_∶_]->_ : Cls → Part → PartSet → Choice → Cls → Set
    G -[ p ⇒ Qs ∶ c ]-> G′ = G -<[ p ↦ (! Qs) # c ]>-> G′

    _-[_⇐_∶_]->_ : Cls → Part → Part → Choice → Cls → Set
    G -[ q ⇐ p ∶ c ]-> G′ = G -<[ q ↦ (？ p) # c ]>-> G′

    -- G —p→q→
    _-[_⇐_]-> : Cls → Part → Part → Set
    G -[ q ⇐ p ]-> = ∃[ c ] ∃[ G′ ] G -[ q ⇐ p ∶ c ]-> G′

    -- In the synchronous case, the steps the rules ask about are the
    -- paper's labelled steps `G —p→Qs:c→ G′` (`p ⇾ q # c` for one `q`).
    module Sync (bal : Balanced B) where

      open Balanced bal using (send⇒step; step⇒send; recv⇒step; step⇒recv)

      send⇒label :
        ∀ {G p Qs c G′} → G -[ p ⇒ Qs ∶ c ]-> G′ → G -< p ⟶ Qs # c >-> G′
      send⇒label (α , eq , (G″ , G″~ , gr)) =
        G″ , G″~ , send⇒step (α , eq , gr)

      label⇒send :
        ∀ {G p Qs c G′} → G -< p ⟶ Qs # c >-> G′ → G -[ p ⇒ Qs ∶ c ]-> G′
      label⇒send (G″ , G″~ , gr) =
        let α , eq , gr′ = step⇒send gr in α , eq , (G″ , G″~ , gr′)

      recv⇒label :
        ∀ {G q p c G′} → G -[ q ⇐ p ∶ c ]-> G′
        → ∃[ Qs ] q ∈ Qs × G -< p ⟶ Qs # c >-> G′
      recv⇒label (α , eq , (G″ , G″~ , gr)) =
        let Qs , q∈ , gr′ = recv⇒step (α , eq , gr) in Qs , q∈ , (G″ , G″~ , gr′)

      label⇒recv :
        ∀ {G q p Qs c G′} → q ≢ p → q ∈ Qs → G -< p ⟶ Qs # c >-> G′
        → G -[ q ⇐ p ∶ c ]-> G′
      label⇒recv q≢p q∈ (G″ , G″~ , gr) =
        let α , eq , gr′ = step⇒recv q≢p q∈ gr in α , eq , (G″ , G″~ , gr′)

    -- ── Fig. 4 ──

    infix 4 _&_⊢[_]_∶_ _&_&_⊢[_]_∶_

    data _&_⊢[_]_∶_
      (Γ : Vec Sort γ) (Δ : Vec Cls δ) (R : PartSet)
      : Proc γ δ → Cls → Set

    data _&_&_⊢[_]_∶_
      (Γ : Vec Sort γ) (Δ : Vec Cls δ) (Ξ : Vec Cls ξ) (R : PartSet)
      : Proc γ δ → Cls → Set

    data _&_⊢[_]_∶_ Γ Δ R where

      send :
        ∀ {p Qs ℓ t e P G G′}
        → p first-in (R , G)
        → G -[ p ⇒ Qs ∶ ℓ < t > ]-> G′
        → Γ ⊢e e ∶ t
        → Γ & Δ ⊢[ R ] P ∶ G′
        → Γ & Δ ⊢[ R ] p ⇒ Qs ! ℓ < e >∙ P ∶ G

      recv :
        ∀ {q p n} {Br : Vec (Maybe (Proc (suc _) _)) n} {G}
        → q first-in (R , G)
        → p ∉ R
        → G -[ q ⇐ p ]->
        → (∀ {ℓ t G′}
           → G -[ q ⇐ p ∶ ℓ < t > ]-> G′
           → ∃[ Pℓ ] Br ∋ ℓ ↦ Pℓ × Γ ▸ t & Δ ⊢[ R ] Pℓ ∶ G′)
        → Γ & Δ ⊢[ R ] q ⇐ p ？· Br ∶ G

      skip :
        ∀ {P G}
        → Γ & Δ & [] ⊢[ R ] P ∶ G
        → Γ & Δ ⊢[ R ] P ∶ G

      forward :
        ∀ {P G G′}
        → Γ & Δ ⊢[ R ] P ∶ G
        → G -[¬ R ]->* G′
        → Γ & Δ ⊢[ R ] P ∶ G′

      if :
        ∀ {e P₁ P₂ G}
        → Γ ⊢e e ∶ s/bool
        → Γ & Δ ⊢[ R ] P₁ ∶ G
        → Γ & Δ ⊢[ R ] P₂ ∶ G
        → Γ & Δ ⊢[ R ] ifp e then P₁ else P₂ ∶ G

      end :
        ∀ {G}
        → R ∉ G
        → Γ & Δ ⊢[ R ] ∅ ∶ G

      rec :
        ∀ {P G}
        → Γ & Δ ▸ G ⊢[ R ] P ∶ G
        → MessageGuarded P
        → Γ & Δ ⊢[ R ] rec P ∶ G

      var :
        ∀ {X G}
        → X ∶ G ∈ Δ
        → Γ & Δ ⊢[ R ] v X ∶ G

    data _&_&_⊢[_]_∶_ Γ Δ Ξ R where

      skip-main :
        ∀ {P G}
        → Γ & Δ ⊢[ R ] P ∶ G
        → Γ & Δ & Ξ ⊢[ R ] P ∶ G

      skip-cycle :
        ∀ {P G}
        → G ∈ Ξ
        → R ∈ G
        → Γ & Δ & Ξ ⊢[ R ] P ∶ G

      skip-step :
        ∀ {P G}
        → G -→
        → ¬ G -⟨ R ⟩->
        → (∀ {α G′} → G -< α >-> G′ → Γ & Δ & Ξ ▸ G ⊢[ R ] P ∶ G′)
        → Γ & Δ & Ξ ⊢[ R ] P ∶ G

  open Paper public
    hiding ( _-<_>->_; _-<[_↦_]>->_; _-⟨_⟩->_; _-⟨_⟩->; _-→; _-→*_
           ; _-[¬_]->_; _-[¬_]->*_; _∈T_; _first-in_
           ; Membership; _∈_; _∉_ )

  -- The theory's own names, for the proofs.
  open BTheory B public
  open WellBehaved wb public

-- Sessions: one process per block, each typed against its block's local
-- view at the class of the session's state, and carrying that view's
-- `WellBehaved`.
module Sessions {N : ℕ} (B : BTheory N) where

  open import Definitions.Common N using (PartSet)
  open import Definitions.Proc N using (Proc; module Over)
  open import Definitions.View B using (view)
  open BTheory B using (Behav)

  infix 4 ⊢ᵛ[_]_∶_ ⊢s[_]_∶_

  -- The process `Pr` of role set `Ps`, typed against `Ps`'s view at the
  -- class of `G` there.
  ⊢ᵛ[_]_∶_ : PartSet → Proc 0 0 → Behav → Set₁
  ⊢ᵛ[ Ps ] Pr ∶ G =
    Σ[ wb ∈ WellBehaved (view Ps) ]
      (let open MPST wb in [] & [] ⊢[ Ps ] Pr ∶ [ G ])

  -- Every process of the session, at its block.
  ⊢s[_]_∶_ : ∀ {K} (Ρ : Assignment N K) → Over.Session Ρ → Behav → Set₁
  ⊢s[ Ρ ] M ∶ G = ∀ j → ⊢ᵛ[ lu (Assignment.roles Ρ) j ] lu M j ∶ G
