{-# OPTIONS --guardedness #-}

-- `n₁ ∥ n₂` is well-behaved when both sides are and they are
-- receiver-disjoint (`Disjoint`, decided by `disjoint?`).

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin.Properties as FinP
import Data.List.Relation.Unary.All as All
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Definitions.Behav using (BTheory; WellBehaved; Synchronous)

module Definitions.Graph.NetworkWB (N : ℕ) where

  open import Definitions.Actions N
  open import Definitions.Graph.Action N using (_⋄?_)
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
  --
  -- `HasRecv` (every edge has a receiver) refutes cross-side "same comm".

  HasRecv : Action → Set
  HasRecv α = ∃[ Q ] Recv α Q

  Disjoint : Net → Net → Set
  Disjoint n₁ n₂ =
    EdgePred n₁ HasRecv
    × EdgePred n₂ HasRecv
    × EdgePred n₁ (λ α → EdgePred n₂ (λ β → α ⋄ β))

  disjoint? : ∀ n₁ n₂ → Dec (Disjoint n₁ n₂)
  disjoint? n₁ n₂ =
    edgePred? n₁ (λ α → FinP.any? (Recv? α))
    ×-dec edgePred? n₂ (λ α → FinP.any? (Recv? α))
    ×-dec edgePred? n₁ (λ α → edgePred? n₂ (λ β → α ⋄? β))

  module _ {n₁ n₂ : Net} (dis : Disjoint n₁ n₂) where

    -- two steps of the two sides are always independent …
    dis-⋄ :
      ∀ {a α a′ b β b′}
      → NStep n₁ a α a′ → NStep n₂ b β b′
      → α ⋄ β
    dis-⋄ st₁ st₂ = step-edge n₂ (step-edge n₁ (proj₂ (proj₂ dis)) st₁) st₂

    -- … so a receiver on one side takes no part in the other …
    dis-recv₁ :
      ∀ {a α a′ b β b′ Q}
      → NStep n₁ a α a′ → NStep n₂ b β b′
      → Recv α Q → Q ∈α β → ⊥
    dis-recv₁ {β = β} {Q = Q} st₁ st₂ rQ Q∈β =
      ∉α→¬∈α {Q} {β} (proj₁ (proj₂ (dis-⋄ st₁ st₂)) Q rQ) Q∈β

    dis-recv₂ :
      ∀ {a α a′ b β b′ Q}
      → NStep n₁ a α a′ → NStep n₂ b β b′
      → Recv β Q → Q ∈α α → ⊥
    dis-recv₂ {α = α} {Q = Q} st₁ st₂ rQ Q∈α =
      ∉α→¬∈α {Q} {α} (proj₂ (proj₂ (dis-⋄ st₁ st₂)) Q rQ) Q∈α

    -- … and they can never carry the same communication.
    dis-¬share :
      ∀ {a α a′ b β b′}
      → NStep n₁ a α a′ → NStep n₂ b β b′
      → comm α ≡ comm β
      → ⊥
    dis-¬share {α = α} {β = β} st₁ st₂ eq
      with step-edge n₁ (proj₁ dis) st₁
    ... | Q , rQ =
      dis-recv₁ st₁ st₂ rQ (comm-∈α {α} {β} {Q} eq (Recv→∈α {α} {Q} rQ))

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

    -- ── the axioms ──

    parWB : WellBehaved (netTheory (n₁ ∥ n₂))
    parWB .WellBehaved.recv-overlap {G} {α} {α′} st st′ rQ Q∈
      with pairView n₁ n₂ G
    ... | is-pair a b
      with pstep-inv n₁ n₂ {a = a} {b = b} st
         | pstep-inv n₁ n₂ {a = a} {b = b} st′
    ... | inj₁ (_ , st₁ , _) | inj₁ (_ , st₁′ , _) =
      W₁.recv-overlap st₁ st₁′ rQ Q∈
    ... | inj₁ (_ , st₁ , _) | inj₂ (_ , st₂′ , _) =
      ⊥-elim (dis-recv₁ dis st₁ st₂′ rQ Q∈)
    ... | inj₂ (_ , st₂ , _) | inj₁ (_ , st₁′ , _) =
      ⊥-elim (dis-recv₂ dis st₁′ st₂ rQ Q∈)
    ... | inj₂ (_ , st₂ , _) | inj₂ (_ , st₂′ , _) =
      W₂.recv-overlap st₂ st₂′ rQ Q∈
    parWB .WellBehaved.step-deterministic {G} st st′
      with pairView n₁ n₂ G
    ... | is-pair a b
      with pstep-inv n₁ n₂ {a = a} {b = b} st
         | pstep-inv n₁ n₂ {a = a} {b = b} st′
    ... | inj₁ (_ , st₁ , refl) | inj₁ (_ , st₁′ , refl) =
      ~-pair (W₁.step-deterministic st₁ st₁′) T₂.~refl
    ... | inj₁ (_ , st₁ , _) | inj₂ (_ , st₂′ , _) =
      ⊥-elim (dis-¬share dis st₁ st₂′ refl)
    ... | inj₂ (_ , st₂ , _) | inj₁ (_ , st₁′ , _) =
      ⊥-elim (dis-¬share dis st₁′ st₂ refl)
    ... | inj₂ (_ , st₂ , refl) | inj₂ (_ , st₂′ , refl) =
      ~-pair T₁.~refl (W₂.step-deterministic st₂ st₂′)
    -- Cross-side: `Q` receives on one side and acts on the other.
    parWB .WellBehaved.step-sort-det {G} st st′ eq eq′
      with pairView n₁ n₂ G
    ... | is-pair a b
      with pstep-inv n₁ n₂ {a = a} {b = b} st
         | pstep-inv n₁ n₂ {a = a} {b = b} st′
    ... | inj₁ (_ , st₁ , _) | inj₁ (_ , st₁′ , _) =
      W₁.step-sort-det st₁ st₁′ eq eq′
    ... | inj₁ (_ , st₁ , _) | inj₂ (_ , st₂′ , _) =
      ⊥-elim (dis-recv₁ dis st₁ st₂′ (_ , _ , eq) (_ , eq′))
    ... | inj₂ (_ , st₂ , _) | inj₁ (_ , st₁′ , _) =
      ⊥-elim (dis-recv₂ dis st₁′ st₂ (_ , _ , eq) (_ , eq′))
    ... | inj₂ (_ , st₂ , _) | inj₂ (_ , st₂′ , _) =
      W₂.step-sort-det st₂ st₂′ eq eq′
    parWB .WellBehaved.step-arity-det {G} st st′ eq eq′
      with pairView n₁ n₂ G
    ... | is-pair a b
      with pstep-inv n₁ n₂ {a = a} {b = b} st
         | pstep-inv n₁ n₂ {a = a} {b = b} st′
    ... | inj₁ (_ , st₁ , _) | inj₁ (_ , st₁′ , _) =
      W₁.step-arity-det st₁ st₁′ eq eq′
    ... | inj₁ (_ , st₁ , _) | inj₂ (_ , st₂′ , _) =
      ⊥-elim (dis-recv₁ dis st₁ st₂′ (_ , _ , eq) (_ , eq′))
    ... | inj₂ (_ , st₂ , _) | inj₁ (_ , st₁′ , _) =
      ⊥-elim (dis-recv₂ dis st₁′ st₂ (_ , _ , eq) (_ , eq′))
    ... | inj₂ (_ , st₂ , _) | inj₂ (_ , st₂′ , _) =
      W₂.step-arity-det st₂ st₂′ eq eq′
    parWB .WellBehaved.no-new-branch/step {G} {G′} st idle stᵢ stⱼ′ ceq
      with pairView n₁ n₂ G
    ... | is-pair a b
      with pstep-inv n₁ n₂ {a = a} {b = b} st
    parWB .WellBehaved.no-new-branch/step _ idle stᵢ stⱼ′ ceq
      | is-pair a b | inj₁ (a′ , st₁ , refl)
      with pstep-inv n₁ n₂ {a = a′} {b = b} stⱼ′
    ... | inj₂ (bⱼ , st₂ⱼ , _) =
      -- the γ′-branch lives in the untouched right component
      mkPair a bⱼ , stepR {b = b} {b′ = bⱼ} a st₂ⱼ
    ... | inj₁ (aⱼ , st₁ⱼ , _)
      with pstep-inv n₁ n₂ {a = a} {b = b} stᵢ
    ...   | inj₂ (_ , st₂ᵢ , _) =
      ⊥-elim (dis-¬share dis st₁ⱼ st₂ᵢ ceq)
    ...   | inj₁ (_ , st₁ᵢ , _) =
      let aⱼ₀ , st₁ⱼ₀ = W₁.no-new-branch/step st₁ idle st₁ᵢ st₁ⱼ ceq
      in mkPair aⱼ₀ b , stepL {a = a} {a′ = aⱼ₀} b st₁ⱼ₀
    parWB .WellBehaved.no-new-branch/step _ idle stᵢ stⱼ′ ceq
      | is-pair a b | inj₂ (b′ , st₂ , refl)
      with pstep-inv n₁ n₂ {a = a} {b = b′} stⱼ′
    ... | inj₁ (aⱼ , st₁ⱼ , _) =
      mkPair aⱼ b , stepL {a = a} {a′ = aⱼ} b st₁ⱼ
    ... | inj₂ (bⱼ , st₂ⱼ , _)
      with pstep-inv n₁ n₂ {a = a} {b = b} stᵢ
    ...   | inj₁ (_ , st₁ᵢ , _) =
      ⊥-elim (dis-¬share dis st₁ᵢ st₂ⱼ (sym ceq))
    ...   | inj₂ (_ , st₂ᵢ , _) =
      let bⱼ₀ , st₂ⱼ₀ = W₂.no-new-branch/step st₂ idle st₂ᵢ st₂ⱼ ceq
      in mkPair a bⱼ₀ , stepR {b = b} {b′ = bⱼ₀} a st₂ⱼ₀
    parWB .WellBehaved.step-diamond {G} st st′ ind
      with pairView n₁ n₂ G
    ... | is-pair a b
      with pstep-inv n₁ n₂ {a = a} {b = b} st
         | pstep-inv n₁ n₂ {a = a} {b = b} st′
    ... | inj₁ (a₁ , st₁ , refl) | inj₁ (a₂ , st₁′ , refl) =
      let a₃ , a₄ , d₁ , d₂ , pa = W₁.step-diamond st₁ st₁′ ind
      in mkPair a₃ b , mkPair a₄ b
       , stepL {a = a₁} {a′ = a₃} b d₁ , stepL {a = a₂} {a′ = a₄} b d₂
       , ~-pair pa T₂.~refl
    ... | inj₁ (a₁ , st₁ , refl) | inj₂ (b₂ , st₂′ , refl) =
      -- the trivial cross-component diamond: both orders rebuild the pair
      mkPair a₁ b₂ , mkPair a₁ b₂
      , stepR {b = b} {b′ = b₂} a₁ st₂′ , stepL {a = a} {a′ = a₁} b₂ st₁
      , T∥.~refl
    ... | inj₂ (b₁ , st₂ , refl) | inj₁ (a₂ , st₁′ , refl) =
      mkPair a₂ b₁ , mkPair a₂ b₁
      , stepL {a = a} {a′ = a₂} b₁ st₁′ , stepR {b = b} {b′ = b₁} a₂ st₂
      , T∥.~refl
    ... | inj₂ (b₁ , st₂ , refl) | inj₂ (b₂ , st₂′ , refl) =
      let b₃ , b₄ , d₁ , d₂ , pb = W₂.step-diamond st₂ st₂′ ind
      in mkPair a b₃ , mkPair a b₄
       , stepR {b = b₁} {b′ = b₃} a d₁ , stepR {b = b₂} {b′ = b₄} a d₂
       , ~-pair T₁.~refl pb

  -- ── the synchronous facts, compositionally ──

  module ParSync
    (n₁ n₂ : Net)
    (sy₁ : Synchronous (netTheory n₁))
    (sy₂ : Synchronous (netTheory n₂))
    where

    private
      module S₁ = Synchronous sy₁
      module S₂ = Synchronous sy₂

    parSync : Synchronous (netTheory (n₁ ∥ n₂))
    parSync .Synchronous.balanced {G} st
      with pairView n₁ n₂ G
    ... | is-pair a b with pstep-inv n₁ n₂ {a = a} {b = b} st
    ... | inj₁ (_ , st₁ , _) = S₁.balanced st₁
    ... | inj₂ (_ , st₂ , _) = S₂.balanced st₂
    parSync .Synchronous.no-new-comm/step {G} {G′} st idle stγ
      with pairView n₁ n₂ G
    ... | is-pair a b
      with pstep-inv n₁ n₂ {a = a} {b = b} st
    parSync .Synchronous.no-new-comm/step _ idle stγ
      | is-pair a b | inj₁ (a′ , st₁ , refl)
      with pstep-inv n₁ n₂ {a = a′} {b = b} stγ
    ... | inj₂ (bγ , st₂γ , _) =
      mkPair a bγ , stepR {b = b} {b′ = bγ} a st₂γ
    ... | inj₁ (aγ , st₁γ , _) =
      let aγ₀ , st₁γ₀ = S₁.no-new-comm/step st₁ idle st₁γ
      in mkPair aγ₀ b , stepL {a = a} {a′ = aγ₀} b st₁γ₀
    parSync .Synchronous.no-new-comm/step _ idle stγ
      | is-pair a b | inj₂ (b′ , st₂ , refl)
      with pstep-inv n₁ n₂ {a = a} {b = b′} stγ
    ... | inj₁ (aγ , st₁γ , _) =
      mkPair aγ b , stepL {a = a} {a′ = aγ} b st₁γ
    ... | inj₂ (bγ , st₂γ , _) =
      let bγ₀ , st₂γ₀ = S₂.no-new-comm/step st₂ idle st₂γ
      in mkPair a bγ₀ , stepR {b = b} {b′ = bγ₀} a st₂γ₀
