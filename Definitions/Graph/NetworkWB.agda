{-# OPTIONS --guardedness #-}

-- Compositional well-behavedness for networks: if the two sides of a
-- parallel composition are well-behaved and *receiver-disjoint*, the
-- composition is well-behaved — with the cross-component diamond holding
-- by construction (both interleavings literally rebuild the same pair),
-- cross `no-new-comm`/`no-new-branch` trivial (a side's enabledness
-- depends only on its own state), and `stepback/~` via the product
-- bisimilarity characterization `mkPair a b ~ mkPair a′ b′ ⇔ a ~ a′ × b ~ b′`
-- (the one genuinely coinductive part, and the place disjointness is
-- essential: it forces matching steps to stay in their own component).
--
-- `Disjoint` quantifies over the (finitely many) edges of the two sides:
-- no action of one side may involve the *receiver* of any action of the
-- other.  It is decidable (`disjoint?`), and for closed networks the
-- witness is found by evaluation, `buildG`-style.

open import Data.Bool using (T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Properties using (T-irrelevant)
open import Data.Fin using (Fin)
import Data.Fin.Properties as FinP
open import Data.List using (List)
import Data.List.Relation.Unary.All as All
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Definitions.Behav using (BTheory; WellBehaved)

module Definitions.Graph.NetworkWB (N : ℕ) where

  open import Definitions.Actions N
  open import Definitions.Graph.Network N

  -- ── quantification over all edges of a network ──

  EdgePred : Net → (Action → Set) → Set
  EdgePred n P = ∀ i → All.All (λ e → P (proj₁ e)) (nedges n (nst n i))

  edgePred? :
    ∀ n {P : Action → Set}
    → (∀ α → Dec (P α))
    → Dec (EdgePred n P)
  edgePred? n P? =
    FinP.all? (λ i → All.all? (λ e → P? (proj₁ e)) (nedges n (nst n i)))

  step-edge :
    ∀ n {P : Action → Set} {s α t}
    → EdgePred n P
    → NStep n s α t
    → P α
  step-edge n {P} {s} {α} {t} ep st =
    All.lookup (ep (nix n s))
      (subst (λ z → (α , t) ∈ nedges n z) (sym (nst-nix n s))
        (nstep⇒listed n {s = s} st))

  -- ── receiver-disjointness of two networks ──

  Disjoint : Net → Net → Set
  Disjoint n₁ n₂ =
    EdgePred n₁ (λ α → EdgePred n₂ (λ β →
      (receiver α ∉α β) × (receiver β ∉α α)))

  disjoint? : ∀ n₁ n₂ → Dec (Disjoint n₁ n₂)
  disjoint? n₁ n₂ =
    edgePred? n₁ (λ α →
      edgePred? n₂ (λ β →
        (receiver α ∉α? β) ×-dec (receiver β ∉α? α)))

  module _ {n₁ n₂ : Net} (dis : Disjoint n₁ n₂) where

    -- two steps of the two sides are always independent …
    dis-⋄ :
      ∀ {a α a′ b β b′}
      → NStep n₁ a α a′ → NStep n₂ b β b′
      → α ⋄ β
    dis-⋄ st₁ st₂ = step-edge n₂ (step-edge n₁ dis st₁) st₂

    -- … in particular they can never carry the same communication
    dis-¬share :
      ∀ {a α a′ b β b′}
      → NStep n₁ a α a′ → NStep n₂ b β b′
      → Action.comm α ≡ Action.comm β
      → ⊥
    dis-¬share {α = α} st₁ st₂ eq =
      ∉c→¬∈c (proj₁ (dis-⋄ st₁ st₂))
        (subst (Comm.receiver (Action.comm α) ∈c_) eq (∈R refl))

  -- ── every product state is a pair ──

  data PairView (n₁ n₂ : Net) : NState (n₁ ∥ n₂) → Set where
    is-pair : (a : NState n₁) (b : NState n₂) → PairView n₁ n₂ (mkPair a b)

  pairView : ∀ n₁ n₂ s → PairView n₁ n₂ s
  pairView n₁ n₂ (live (inj₂ (a , b))) = is-pair (live a) b
  pairView n₁ n₂ (live (inj₁ b))       = is-pair nend (live b)
  pairView n₁ n₂ nend                  = is-pair nend nend

  -- ── the compositional well-behavedness theorem ──

  module ParWB
    (n₁ n₂ : Net)
    (wb₁ : WellBehaved (netTheory n₁))
    (wb₂ : WellBehaved (netTheory n₂))
    (dis : Disjoint n₁ n₂)
    where

    private
      module T∥ = BTheory (netTheory (n₁ ∥ n₂))
      module T₁ = BTheory (netTheory n₁)
      module T₂ = BTheory (netTheory n₂)
      module W₁ = WellBehaved wb₁
      module W₂ = WellBehaved wb₂

    -- ── product bisimilarity: pairing ──

    mutual
      ≲-pair :
        ∀ {a₁ b₁ a₂ b₂}
        → a₁ T₁.~ a₂ → b₁ T₂.~ b₂
        → mkPair a₁ b₁ T∥.≲ mkPair a₂ b₂
      ≲-pair {a₁} {b₁} {a₂} {b₂} pa pb .T∥._≲_.simulate st
        with pstep-inv n₁ n₂ {a = a₁} {b = b₁} st
      ... | inj₁ (a₁′ , st₁ , refl) =
        let a₂′ , st₂ , pa′ = T₁.~L pa st₁
        in mkPair a₂′ b₂ , stepL {a = a₂} {a′ = a₂′} b₂ st₂ , ~-pair pa′ pb
      ... | inj₂ (b₁′ , st₁ , refl) =
        let b₂′ , st₂ , pb′ = T₂.~L pb st₁
        in mkPair a₂ b₂′ , stepR {b = b₂} {b′ = b₂′} a₂ st₂ , ~-pair pa pb′

      ~-pair :
        ∀ {a₁ b₁ a₂ b₂}
        → a₁ T₁.~ a₂ → b₁ T₂.~ b₂
        → mkPair a₁ b₁ T∥.~ mkPair a₂ b₂
      ~-pair pa pb =
        ≲-pair pa pb , ≲-pair (T₁.~sym pa) (T₂.~sym pb)

    -- ── product bisimilarity: projections (needs disjointness) ──

    mutual
      ≲-projL :
        ∀ {a₁ b₁ a₂ b₂}
        → mkPair a₁ b₁ T∥.~ mkPair a₂ b₂
        → a₁ T₁.≲ a₂
      ≲-projL {a₁} {b₁} {a₂} {b₂} pr .T₁._≲_.simulate st₁
        with T∥.~L pr (stepL b₁ st₁)
      ... | X , stP , prX with pstep-inv n₁ n₂ {a = a₂} {b = b₂} stP
      ...   | inj₁ (a₂′ , st₂ , refl) =
        a₂′ , st₂ , ~-projL prX
      ...   | inj₂ (b₂′ , st₂ , refl) =
        ⊥-elim (dis-¬share dis st₁ st₂ refl)

      ~-projL :
        ∀ {a₁ b₁ a₂ b₂}
        → mkPair a₁ b₁ T∥.~ mkPair a₂ b₂
        → a₁ T₁.~ a₂
      ~-projL pr = ≲-projL pr , ≲-projL (T∥.~sym pr)

    mutual
      ≲-projR :
        ∀ {a₁ b₁ a₂ b₂}
        → mkPair a₁ b₁ T∥.~ mkPair a₂ b₂
        → b₁ T₂.≲ b₂
      ≲-projR {a₁} {b₁} {a₂} {b₂} pr .T₂._≲_.simulate st₁
        with T∥.~L pr (stepR a₁ st₁)
      ... | X , stP , prX with pstep-inv n₁ n₂ {a = a₂} {b = b₂} stP
      ...   | inj₁ (a₂′ , st₂ , refl) =
        ⊥-elim (dis-¬share dis st₂ st₁ refl)
      ...   | inj₂ (b₂′ , st₂ , refl) =
        b₂′ , st₂ , ~-projR prX

      ~-projR :
        ∀ {a₁ b₁ a₂ b₂}
        → mkPair a₁ b₁ T∥.~ mkPair a₂ b₂
        → b₁ T₂.~ b₂
      ~-projR pr = ≲-projR pr , ≲-projR (T∥.~sym pr)

    -- ── the axioms ──

    parWB : WellBehaved (netTheory (n₁ ∥ n₂))
    parWB .WellBehaved.recv-overlap⇒same-comm {G} {α} {α′} st st′ rov
      with pairView n₁ n₂ G
    ... | is-pair a b
      with pstep-inv n₁ n₂ {a = a} {b = b} st
         | pstep-inv n₁ n₂ {a = a} {b = b} st′
    ... | inj₁ (_ , st₁ , _) | inj₁ (_ , st₁′ , _) =
      W₁.recv-overlap⇒same-comm st₁ st₁′ rov
    ... | inj₁ (_ , st₁ , _) | inj₂ (_ , st₂′ , _) =
      ⊥-elim (∉c→¬∈c (proj₁ (dis-⋄ dis st₁ st₂′)) rov)
    ... | inj₂ (_ , st₂ , _) | inj₁ (_ , st₁′ , _) =
      ⊥-elim (∉c→¬∈c (proj₂ (dis-⋄ dis st₁′ st₂)) rov)
    ... | inj₂ (_ , st₂ , _) | inj₂ (_ , st₂′ , _) =
      W₂.recv-overlap⇒same-comm st₂ st₂′ rov
    parWB .WellBehaved.sender≢receiver {G} st
      with pairView n₁ n₂ G
    ... | is-pair a b with pstep-inv n₁ n₂ {a = a} {b = b} st
    ... | inj₁ (_ , st₁ , _) = W₁.sender≢receiver st₁
    ... | inj₂ (_ , st₂ , _) = W₂.sender≢receiver st₂
    parWB .WellBehaved.step-deterministic {G} st st′
      with pairView n₁ n₂ G
    ... | is-pair a b
      with pstep-inv n₁ n₂ {a = a} {b = b} st
         | pstep-inv n₁ n₂ {a = a} {b = b} st′
    ... | inj₁ (_ , st₁ , refl) | inj₁ (_ , st₁′ , refl) =
      cong (λ x → mkPair x b) (W₁.step-deterministic st₁ st₁′)
    ... | inj₁ (_ , st₁ , _) | inj₂ (_ , st₂′ , _) =
      ⊥-elim (dis-¬share dis st₁ st₂′ refl)
    ... | inj₂ (_ , st₂ , _) | inj₁ (_ , st₁′ , _) =
      ⊥-elim (dis-¬share dis st₁′ st₂ refl)
    ... | inj₂ (_ , st₂ , refl) | inj₂ (_ , st₂′ , refl) =
      cong (mkPair a) (W₂.step-deterministic st₂ st₂′)
    parWB .WellBehaved.step-sort-deterministic {G} st st′
      with pairView n₁ n₂ G
    ... | is-pair a b
      with pstep-inv n₁ n₂ {a = a} {b = b} st
         | pstep-inv n₁ n₂ {a = a} {b = b} st′
    ... | inj₁ (_ , st₁ , _) | inj₁ (_ , st₁′ , _) =
      W₁.step-sort-deterministic st₁ st₁′
    ... | inj₁ (_ , st₁ , _) | inj₂ (_ , st₂′ , _) =
      ⊥-elim (dis-¬share dis st₁ st₂′ refl)
    ... | inj₂ (_ , st₂ , _) | inj₁ (_ , st₁′ , _) =
      ⊥-elim (dis-¬share dis st₁′ st₂ refl)
    ... | inj₂ (_ , st₂ , _) | inj₂ (_ , st₂′ , _) =
      W₂.step-sort-deterministic st₂ st₂′
    parWB .WellBehaved.step-arity-deterministic {G} st st′
      with pairView n₁ n₂ G
    ... | is-pair a b
      with pstep-inv n₁ n₂ {a = a} {b = b} st
         | pstep-inv n₁ n₂ {a = a} {b = b} st′
    ... | inj₁ (_ , st₁ , _) | inj₁ (_ , st₁′ , _) =
      W₁.step-arity-deterministic st₁ st₁′
    ... | inj₁ (_ , st₁ , _) | inj₂ (_ , st₂′ , _) =
      ⊥-elim (dis-¬share dis st₁ st₂′ refl)
    ... | inj₂ (_ , st₂ , _) | inj₁ (_ , st₁′ , _) =
      ⊥-elim (dis-¬share dis st₁′ st₂ refl)
    ... | inj₂ (_ , st₂ , _) | inj₂ (_ , st₂′ , _) =
      W₂.step-arity-deterministic st₂ st₂′
    parWB .WellBehaved.step-is-prop st st′ =
      cong nstep (T-irrelevant (un st) (un st′))
    parWB .WellBehaved.no-new-branch/step {G} {G′} st r∉β stᵢ stⱼ′
      with pairView n₁ n₂ G
    ... | is-pair a b
      with pstep-inv n₁ n₂ {a = a} {b = b} st
    parWB .WellBehaved.no-new-branch/step _ r∉β stᵢ stⱼ′
      | is-pair a b | inj₁ (a′ , st₁ , refl)
      with pstep-inv n₁ n₂ {a = a′} {b = b} stⱼ′
    ... | inj₂ (bⱼ , st₂ⱼ , _) =
      -- the γ-branch lives in the untouched right component
      mkPair a bⱼ , stepR {b = b} {b′ = bⱼ} a st₂ⱼ
    ... | inj₁ (aⱼ , st₁ⱼ , _)
      with pstep-inv n₁ n₂ {a = a} {b = b} stᵢ
    ...   | inj₂ (_ , st₂ᵢ , _) =
      ⊥-elim (dis-¬share dis st₁ⱼ st₂ᵢ refl)
    ...   | inj₁ (_ , st₁ᵢ , _) =
      let aⱼ₀ , st₁ⱼ₀ = W₁.no-new-branch/step st₁ r∉β st₁ᵢ st₁ⱼ
      in mkPair aⱼ₀ b , stepL {a = a} {a′ = aⱼ₀} b st₁ⱼ₀
    parWB .WellBehaved.no-new-branch/step _ r∉β stᵢ stⱼ′
      | is-pair a b | inj₂ (b′ , st₂ , refl)
      with pstep-inv n₁ n₂ {a = a} {b = b′} stⱼ′
    ... | inj₁ (aⱼ , st₁ⱼ , _) =
      mkPair aⱼ b , stepL {a = a} {a′ = aⱼ} b st₁ⱼ
    ... | inj₂ (bⱼ , st₂ⱼ , _)
      with pstep-inv n₁ n₂ {a = a} {b = b} stᵢ
    ...   | inj₁ (_ , st₁ᵢ , _) =
      ⊥-elim (dis-¬share dis st₁ᵢ st₂ⱼ refl)
    ...   | inj₂ (_ , st₂ᵢ , _) =
      let bⱼ₀ , st₂ⱼ₀ = W₂.no-new-branch/step st₂ r∉β st₂ᵢ st₂ⱼ
      in mkPair a bⱼ₀ , stepR {b = b} {b′ = bⱼ₀} a st₂ⱼ₀
    parWB .WellBehaved.no-new-comm/step {G} {G′} st s∉β r∉β stγ
      with pairView n₁ n₂ G
    ... | is-pair a b
      with pstep-inv n₁ n₂ {a = a} {b = b} st
    parWB .WellBehaved.no-new-comm/step _ s∉β r∉β stγ
      | is-pair a b | inj₁ (a′ , st₁ , refl)
      with pstep-inv n₁ n₂ {a = a′} {b = b} stγ
    ... | inj₂ (bγ , st₂γ , _) =
      mkPair a bγ , stepR {b = b} {b′ = bγ} a st₂γ
    ... | inj₁ (aγ , st₁γ , _) =
      let aγ₀ , st₁γ₀ = W₁.no-new-comm/step st₁ s∉β r∉β st₁γ
      in mkPair aγ₀ b , stepL {a = a} {a′ = aγ₀} b st₁γ₀
    parWB .WellBehaved.no-new-comm/step _ s∉β r∉β stγ
      | is-pair a b | inj₂ (b′ , st₂ , refl)
      with pstep-inv n₁ n₂ {a = a} {b = b′} stγ
    ... | inj₁ (aγ , st₁γ , _) =
      mkPair aγ b , stepL {a = a} {a′ = aγ} b st₁γ
    ... | inj₂ (bγ , st₂γ , _) =
      let bγ₀ , st₂γ₀ = W₂.no-new-comm/step st₂ s∉β r∉β st₂γ
      in mkPair a bγ₀ , stepR {b = b} {b′ = bγ₀} a st₂γ₀
    parWB .WellBehaved.stepback/~ {α} {G₀} {G₁} {G₁′} pr st
      with pairView n₁ n₂ G₀ | pairView n₁ n₂ G₁′
    ... | is-pair a b | is-pair c′ d′
      with pstep-inv n₁ n₂ {a = a} {b = b} st
    ... | inj₁ (a′ , st₁ , refl) =
      let pa′ = ~-projL pr
          pb  = ~-projR pr
          a₀′ , pa₀ , st₀ = W₁.stepback/~ pa′ st₁
      in mkPair a₀′ d′ , ~-pair pa₀ pb , stepL {a = a₀′} {a′ = c′} d′ st₀
    ... | inj₂ (b′ , st₂ , refl) =
      let pb′ = ~-projR pr
          pa  = ~-projL pr
          b₀′ , pb₀ , st₀ = W₂.stepback/~ pb′ st₂
      in mkPair c′ b₀′ , ~-pair pa pb₀ , stepR {b = b₀′} {b′ = d′} c′ st₀
    parWB .WellBehaved.step-diamond {G} st st′ ind
      with pairView n₁ n₂ G
    ... | is-pair a b
      with pstep-inv n₁ n₂ {a = a} {b = b} st
         | pstep-inv n₁ n₂ {a = a} {b = b} st′
    ... | inj₁ (a₁ , st₁ , refl) | inj₁ (a₂ , st₁′ , refl) =
      let a₃ , d₁ , d₂ = W₁.step-diamond st₁ st₁′ ind
      in mkPair a₃ b , stepL {a = a₁} {a′ = a₃} b d₁ , stepL {a = a₂} {a′ = a₃} b d₂
    ... | inj₁ (a₁ , st₁ , refl) | inj₂ (b₂ , st₂′ , refl) =
      -- the trivial cross-component diamond: both orders rebuild the pair
      mkPair a₁ b₂ , stepR {b = b} {b′ = b₂} a₁ st₂′ , stepL {a = a} {a′ = a₁} b₂ st₁
    ... | inj₂ (b₁ , st₂ , refl) | inj₁ (a₂ , st₁′ , refl) =
      mkPair a₂ b₁ , stepL {a = a} {a′ = a₂} b₁ st₁′ , stepR {b = b} {b′ = b₁} a₂ st₂
    ... | inj₂ (b₁ , st₂ , refl) | inj₂ (b₂ , st₂′ , refl) =
      let b₃ , d₁ , d₂ = W₂.step-diamond st₂ st₂′ ind
      in mkPair a b₃ , stepR {b = b₁} {b′ = b₃} a d₁ , stepR {b = b₂} {b′ = b₃} a d₂
