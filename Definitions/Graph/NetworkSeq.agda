{-# OPTIONS --guardedness #-}

-- Well-behavedness of `n₁ ⨾ n₂`.  The axioms come from the components,
-- except at the seam, where `SeamComm`/`SeamBranch` (decided on the seam
-- edges) discharge them.  `seamTo` preserves `~` when `n₁` has no stuck live
-- state (`Moves`, decided on base graphs).

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin.Properties as FinP
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; find; lose)
import Data.List.Membership.Propositional.Properties as MemP
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties using (¬Any[])
open import Data.Nat using (ℕ)
open import Data.Product
  using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax; map₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (map′; _→?_)

open import Definitions.Behav using (BTheory; WellBehaved; Synchronous)

module Definitions.Graph.NetworkSeq (N : ℕ) where

  open import Definitions.Actions N
  open import Definitions.Graph.Action N using (_≟Action_; _≟Comm_)
  open import Definitions.Graph.Network N

  -- ── step intro/inversion for the two parts of a `⨾` ──

  stepSeq₁ :
    ∀ {n₁ n₂ a α t₀}
    → NStep n₁ (live a) α t₀
    → NStep (n₁ ⨾ n₂) (live (inj₂ a)) α (seamTo n₁ n₂ t₀)
  stepSeq₁ {n₁} {n₂} {a} st =
    nlisted⇒step (n₁ ⨾ n₂) {s = live (inj₂ a)}
      (MemP.∈-map⁺ (map₂ (seamTo n₁ n₂))
        (nstep⇒listed n₁ {s = live a} st))

  stepSeq₂ :
    ∀ {n₁ n₂ b α b′}
    → NStep n₂ (live b) α b′
    → NStep (n₁ ⨾ n₂) (live (inj₁ b)) α (injR b′)
  stepSeq₂ {n₁} {n₂} {b} st =
    nlisted⇒step (n₁ ⨾ n₂) {s = live (inj₁ b)}
      (MemP.∈-map⁺ (map₂ injR)
        (nstep⇒listed n₂ {s = live b} st))

  sstep-inv₁ :
    ∀ n₁ n₂ {a α t}
    → NStep (n₁ ⨾ n₂) (live (inj₂ a)) α t
    → Σ[ t₀ ∈ NState n₁ ]
        NStep n₁ (live a) α t₀ × t ≡ seamTo n₁ n₂ t₀
  sstep-inv₁ n₁ n₂ {a} st
    with MemP.∈-map⁻ (map₂ (seamTo n₁ n₂))
           (nstep⇒listed (n₁ ⨾ n₂) {s = live (inj₂ a)} st)
  ... | (α₀ , t₀) , m₀ , refl =
    t₀ , nlisted⇒step n₁ {s = live a} m₀ , refl

  sstep-inv₂ :
    ∀ n₁ n₂ {b α t}
    → NStep (n₁ ⨾ n₂) (live (inj₁ b)) α t
    → Σ[ b′ ∈ NState n₂ ]
        NStep n₂ (live b) α b′ × t ≡ injR b′
  sstep-inv₂ n₁ n₂ {b} st
    with MemP.∈-map⁻ (map₂ injR)
           (nstep⇒listed (n₁ ⨾ n₂) {s = live (inj₁ b)} st)
  ... | (α₀ , b′) , m₀ , refl =
    b′ , nlisted⇒step n₂ {s = live b} m₀ , refl

  -- the network end never steps
  nstep-nend-⊥ : ∀ n {α t} → NStep n nend α t → ⊥
  nstep-nend-⊥ n st = un st

  -- ── no live dead ends ──

  Moves : Net → Set
  Moves n = ∀ l → ∃[ α ] ∃[ t ] NStep n (live l) α t

  steps? : ∀ n s → Dec (∃[ α ] ∃[ t ] NStep n s α t)
  steps? n s with nedges n s in eq
  ... | [] =
    no λ { (_ , _ , st) → ¬Any[] (subst (_ ∈_) eq (nstep⇒listed n st)) }
  ... | (α , t) ∷ _ =
    yes (α , t , nlisted⇒step n (subst (_ ∈_) (sym eq) (here refl)))

  moves? : ∀ G → Dec (Moves (base G))
  moves? G = FinP.all? λ l → steps? (base G) (live l)

  moves/par : ∀ {n₁ n₂} → Moves n₁ → Moves n₂ → Moves (n₁ ∥ n₂)
  moves/par m₁ m₂ (inj₂ (a , b)) =
    let α , _ , st = m₁ a in α , _ , stepL b st
  moves/par m₁ m₂ (inj₁ b) =
    let α , _ , st = m₂ b in α , _ , stepR nend st

  moves/seq : ∀ {n₁ n₂} → Moves n₁ → Moves n₂ → Moves (n₁ ⨾ n₂)
  moves/seq m₁ m₂ (inj₂ a) =
    let α , _ , st = m₁ a in α , _ , stepSeq₁ st
  moves/seq m₁ m₂ (inj₁ b) =
    let α , _ , st = m₂ b in α , _ , stepSeq₂ st

  -- ── the seam-causality conditions ──

  -- decide `∃ t. (γ , t) ∈ xs`
  findAction :
    ∀ {A : Set} (γ : Action) (xs : List (Action × A))
    → Dec (∃[ t ] (γ , t) ∈ xs)
  findAction {A} γ xs =
    map′
      (λ hit →
         let (_ , t) , m , α≡γ = find {A = Action × A} hit
         in t , subst (λ β → (β , t) ∈ xs) α≡γ m)
      (λ (_ , m) → lose m refl)
      (Any.any? (λ e → proj₁ e ≟Action γ) xs)

  -- An action at `n₂`'s start, independent of the seam-entering `β`, is
  -- available before the seam.
  SeamComm : Net → Net → Set
  SeamComm n₁ n₂ =
    ∀ i {β γ u}
    → (β , nend) ∈ nedges n₁ (nst n₁ i)
    → (γ , u) ∈ nedges n₂ (ninit n₂)
    → (∀ X → X ∈α γ → X ∉α β)
    → ∃[ t₀ ] (γ , t₀) ∈ nedges n₁ (nst n₁ i)

  seamComm? : ∀ n₁ n₂ → Dec (SeamComm n₁ n₂)
  seamComm? n₁ n₂ =
    map′ from to
      (FinP.all? λ i →
        All.all?
          (λ e₁ →
            nEq? n₁ (proj₂ e₁) nend →?
            All.all?
              (λ e₂ →
                FinP.all?
                  (λ X → (X ∈α? proj₁ e₂) →? (X ∉α? proj₁ e₁))
                →?
                findAction (proj₁ e₂) (nedges n₁ (nst n₁ i)))
              (nedges n₂ (ninit n₂)))
          (nedges n₁ (nst n₁ i)))
    where
    -- `SeamComm`, as the nest of `All`s decided above.
    Nest : Set
    Nest =
      ∀ i →
        All.All
          (λ e₁ →
            proj₂ e₁ ≡ nend →
            All.All
              (λ e₂ →
                (∀ X → X ∈α proj₁ e₂ → X ∉α proj₁ e₁) →
                ∃[ t₀ ] (proj₁ e₂ , t₀) ∈ nedges n₁ (nst n₁ i))
              (nedges n₂ (ninit n₂)))
          (nedges n₁ (nst n₁ i))

    from : Nest → SeamComm n₁ n₂
    from as i mβ mγ idle =
      All.lookup (All.lookup (as i) mβ refl) mγ idle

    to : SeamComm n₁ n₂ → Nest
    to sc i =
      All.tabulate λ {e₁} m₁ eq →
        All.tabulate λ {e₂} m₂ idle →
          sc i
            (subst (λ z → (proj₁ e₁ , z) ∈ nedges n₁ (nst n₁ i)) eq m₁)
            m₂ idle

  -- A branch at `n₂`'s start, of a communication available before the
  -- seam and with receivers not in `β`, is available before the seam.
  SeamBranch : Net → Net → Set
  SeamBranch n₁ n₂ =
    ∀ i {β α₁ tᵢ α₂ u}
    → (β , nend) ∈ nedges n₁ (nst n₁ i)
    → (α₁ , tᵢ) ∈ nedges n₁ (nst n₁ i)
    → comm α₂ ≡ comm α₁
    → (∀ Q → Recv α₁ Q → Q ∉α β)
    → (α₂ , u) ∈ nedges n₂ (ninit n₂)
    → ∃[ tⱼ ] (α₂ , tⱼ) ∈ nedges n₁ (nst n₁ i)

  seamBranch? : ∀ n₁ n₂ → Dec (SeamBranch n₁ n₂)
  seamBranch? n₁ n₂ =
    map′ from to
      (FinP.all? λ i →
        All.all?
          (λ e₁ →
            nEq? n₁ (proj₂ e₁) nend →?
            All.all?
              (λ eᵢ →
                All.all?
                  (λ e₂ →
                    (comm (proj₁ e₂) ≟Comm comm (proj₁ eᵢ))
                      →?
                    FinP.all?
                      (λ Q → Recv? (proj₁ eᵢ) Q →? (Q ∉α? proj₁ e₁))
                      →?
                    findAction (proj₁ e₂) (nedges n₁ (nst n₁ i)))
                  (nedges n₂ (ninit n₂)))
              (nedges n₁ (nst n₁ i)))
          (nedges n₁ (nst n₁ i)))
    where
    -- `SeamBranch`, as the nest of `All`s decided above.
    Nest : Set
    Nest =
      ∀ i →
        All.All
          (λ e₁ →
            proj₂ e₁ ≡ nend →
            All.All
              (λ eᵢ →
                All.All
                  (λ e₂ →
                    comm (proj₁ e₂) ≡ comm (proj₁ eᵢ) →
                    (∀ Q → Recv (proj₁ eᵢ) Q → Q ∉α proj₁ e₁) →
                    ∃[ tⱼ ] (proj₁ e₂ , tⱼ) ∈ nedges n₁ (nst n₁ i))
                  (nedges n₂ (ninit n₂)))
              (nedges n₁ (nst n₁ i)))
          (nedges n₁ (nst n₁ i))

    from : Nest → SeamBranch n₁ n₂
    from as i mβ mᵢ ceq idle m₂ =
      All.lookup (All.lookup (All.lookup (as i) mβ refl) mᵢ) m₂ ceq idle

    to : SeamBranch n₁ n₂ → Nest
    to sb i =
      All.tabulate λ {e₁} m₁ eq →
        All.tabulate λ {eᵢ} mᵢ →
          All.tabulate λ {e₂} m₂ ceq idle →
            sb i
              (subst (λ z → (proj₁ e₁ , z) ∈ nedges n₁ (nst n₁ i)) eq m₁)
              mᵢ ceq idle m₂

  -- convert an `n₁`-side membership at a live state to the indexed form
  -- the seam conditions are stated in, and back
  at₁ :
    ∀ (n₁ : Net) (a : Live n₁) {α t}
    → (α , t) ∈ nedges n₁ (live a)
    → (α , t) ∈ nedges n₁ (nst n₁ (nix n₁ (live a)))
  at₁ n₁ a m =
    subst (λ z → (_ , _) ∈ nedges n₁ z)
      (sym (nst-nix n₁ (live a))) m

  from₁ :
    ∀ (n₁ : Net) (a : Live n₁) {α t}
    → (α , t) ∈ nedges n₁ (nst n₁ (nix n₁ (live a)))
    → (α , t) ∈ nedges n₁ (live a)
  from₁ n₁ a m =
    subst (λ z → (_ , _) ∈ nedges n₁ z)
      (nst-nix n₁ (live a)) m

  -- ── the compositional theorem ──

  module SeqWB
    (n₁ n₂ : Net)
    (wb₁ : WellBehaved (netTheory n₁))
    (wb₂ : WellBehaved (netTheory n₂))
    (sbr : SeamBranch n₁ n₂)
    (mv₁ : Moves n₁)
    where

    private
      module W₁ = WellBehaved wb₁
      module W₂ = WellBehaved wb₂
      module T₁ = BTheory (netTheory n₁)
      module T₂ = BTheory (netTheory n₂)
      module T⨾ = BTheory (netTheory (n₁ ⨾ n₂))

      n⨾ : Net
      n⨾ = n₁ ⨾ n₂

    -- ── `injR` and `seamTo` preserve `~` ──

    mutual
      ≲-injR : ∀ {b b′} → b T₂.~ b′ → injR {n₁} b T⨾.≲ injR b′
      ≲-injR {live b} {b′} pb .T⨾._≲_.simulate st
        with sstep-inv₂ n₁ n₂ {b = b} st
      ... | _ , st₂ , refl
        with T₂.~L pb st₂
      ...   | _ , st₂′ , pc
        with b′
      ...     | live _ = _ , stepSeq₂ st₂′ , ~-injR pc
      ...     | nend   = ⊥-elim (nstep-nend-⊥ n₂ st₂′)
      ≲-injR {nend} pb .T⨾._≲_.simulate st =
        ⊥-elim (nstep-nend-⊥ n⨾ st)

      ~-injR : ∀ {b b′} → b T₂.~ b′ → injR {n₁} b T⨾.~ injR b′
      ~-injR pb = ≲-injR pb , ≲-injR (T₂.~sym pb)

    -- A live state moves (`mv₁`) and `nend` does not: never related.
    mutual
      ≲-seam : ∀ {a a′} → a T₁.~ a′ → seamTo n₁ n₂ a T⨾.≲ seamTo n₁ n₂ a′
      ≲-seam {live a} {live a′} pa .T⨾._≲_.simulate st
        with sstep-inv₁ n₁ n₂ {a = a} st
      ... | _ , st₁ , refl
        with T₁.~L pa st₁
      ...   | _ , st₁′ , pt = _ , stepSeq₁ st₁′ , ~-seam pt
      ≲-seam {live a} {nend} pa =
        let _ , _ , st = mv₁ a
            _ , st′ , _ = T₁.~L pa st
        in ⊥-elim (nstep-nend-⊥ n₁ st′)
      ≲-seam {nend} {live a′} pa =
        let _ , _ , st = mv₁ a′
            _ , st′ , _ = T₁.~R pa st
        in ⊥-elim (nstep-nend-⊥ n₁ st′)
      ≲-seam {nend} {nend} pa = T⨾.≲refl

      ~-seam : ∀ {a a′} → a T₁.~ a′ → seamTo n₁ n₂ a T⨾.~ seamTo n₁ n₂ a′
      ~-seam pa = ≲-seam pa , ≲-seam (T₁.~sym pa)

    seqWB : WellBehaved (netTheory n⨾)
    seqWB .WellBehaved.recv-overlap {live (inj₂ a)} st st′ rQ Q∈
      with sstep-inv₁ n₁ n₂ {a = a} st | sstep-inv₁ n₁ n₂ {a = a} st′
    ... | _ , st₁ , _ | _ , st₁′ , _ =
      W₁.recv-overlap st₁ st₁′ rQ Q∈
    seqWB .WellBehaved.recv-overlap {live (inj₁ b)} st st′ rQ Q∈
      with sstep-inv₂ n₁ n₂ {b = b} st | sstep-inv₂ n₁ n₂ {b = b} st′
    ... | _ , st₂ , _ | _ , st₂′ , _ =
      W₂.recv-overlap st₂ st₂′ rQ Q∈
    seqWB .WellBehaved.recv-overlap {nend} st st′ rQ Q∈ =
      ⊥-elim (nstep-nend-⊥ n⨾ st)

    seqWB .WellBehaved.step-deterministic {live (inj₂ a)} st st′
      with sstep-inv₁ n₁ n₂ {a = a} st | sstep-inv₁ n₁ n₂ {a = a} st′
    ... | _ , st₁ , refl | _ , st₁′ , refl =
      ~-seam (W₁.step-deterministic st₁ st₁′)
    seqWB .WellBehaved.step-deterministic {live (inj₁ b)} st st′
      with sstep-inv₂ n₁ n₂ {b = b} st | sstep-inv₂ n₁ n₂ {b = b} st′
    ... | _ , st₂ , refl | _ , st₂′ , refl =
      ~-injR (W₂.step-deterministic st₂ st₂′)
    seqWB .WellBehaved.step-deterministic {nend} st st′ =
      ⊥-elim (nstep-nend-⊥ n⨾ st)

    seqWB .WellBehaved.step-sort-det {live (inj₂ a)} st st′ eq eq′
      with sstep-inv₁ n₁ n₂ {a = a} st | sstep-inv₁ n₁ n₂ {a = a} st′
    ... | _ , st₁ , _ | _ , st₁′ , _ =
      W₁.step-sort-det st₁ st₁′ eq eq′
    seqWB .WellBehaved.step-sort-det {live (inj₁ b)} st st′ eq eq′
      with sstep-inv₂ n₁ n₂ {b = b} st | sstep-inv₂ n₁ n₂ {b = b} st′
    ... | _ , st₂ , _ | _ , st₂′ , _ =
      W₂.step-sort-det st₂ st₂′ eq eq′
    seqWB .WellBehaved.step-sort-det {nend} st st′ eq eq′ =
      ⊥-elim (nstep-nend-⊥ n⨾ st)

    seqWB .WellBehaved.step-arity-det {live (inj₂ a)} st st′ eq eq′
      with sstep-inv₁ n₁ n₂ {a = a} st | sstep-inv₁ n₁ n₂ {a = a} st′
    ... | _ , st₁ , _ | _ , st₁′ , _ =
      W₁.step-arity-det st₁ st₁′ eq eq′
    seqWB .WellBehaved.step-arity-det {live (inj₁ b)} st st′ eq eq′
      with sstep-inv₂ n₁ n₂ {b = b} st | sstep-inv₂ n₁ n₂ {b = b} st′
    ... | _ , st₂ , _ | _ , st₂′ , _ =
      W₂.step-arity-det st₂ st₂′ eq eq′
    seqWB .WellBehaved.step-arity-det {nend} st st′ eq eq′ =
      ⊥-elim (nstep-nend-⊥ n⨾ st)

    seqWB .WellBehaved.no-new-branch/step
      {live (inj₂ a)} st idle stᵢ stⱼ′ ceq
      with sstep-inv₁ n₁ n₂ {a = a} st | sstep-inv₁ n₁ n₂ {a = a} stᵢ
    seqWB .WellBehaved.no-new-branch/step
      {live (inj₂ a)} st idle stᵢ stⱼ′ ceq
      | live a′ , st₁ , refl | _ , stᵢ₁ , _
      with sstep-inv₁ n₁ n₂ {a = a′} stⱼ′
    ... | _ , stⱼ₁ , _ =
      let tⱼ , grⱼ = W₁.no-new-branch/step st₁ idle stᵢ₁ stⱼ₁ ceq
      in seamTo n₁ n₂ tⱼ , stepSeq₁ grⱼ
    seqWB .WellBehaved.no-new-branch/step
      {live (inj₂ a)} st idle stᵢ stⱼ′ ceq
      | nend , st₁ , refl | _ , stᵢ₁ , _
      with ninit n₂ in eqI
    ... | nend = ⊥-elim (nstep-nend-⊥ n⨾ stⱼ′)
    ... | live c₀
      with sstep-inv₂ n₁ n₂ {b = c₀} stⱼ′
    ...   | _ , stⱼ₂ , _ =
      let tⱼ , mⱼ =
            sbr (nix n₁ (live a))
              (at₁ n₁ a (nstep⇒listed n₁ {s = live a} st₁))
              (at₁ n₁ a (nstep⇒listed n₁ {s = live a} stᵢ₁))
              ceq idle
              (nstep⇒listed n₂ {s = live c₀} stⱼ₂)
      in seamTo n₁ n₂ tⱼ
       , stepSeq₁ (nlisted⇒step n₁ {s = live a} (from₁ n₁ a mⱼ))
    seqWB .WellBehaved.no-new-branch/step
      {live (inj₁ b)} st idle stᵢ stⱼ′ ceq
      with sstep-inv₂ n₁ n₂ {b = b} st | sstep-inv₂ n₁ n₂ {b = b} stᵢ
    seqWB .WellBehaved.no-new-branch/step
      {live (inj₁ b)} st idle stᵢ stⱼ′ ceq
      | live b₁ , st₂ , refl | _ , stᵢ₂ , _
      with sstep-inv₂ n₁ n₂ {b = b₁} stⱼ′
    ... | _ , stⱼ₂ , _ =
      let uⱼ , grⱼ = W₂.no-new-branch/step st₂ idle stᵢ₂ stⱼ₂ ceq
      in injR uⱼ , stepSeq₂ grⱼ
    seqWB .WellBehaved.no-new-branch/step
      {live (inj₁ b)} st idle stᵢ stⱼ′ ceq
      | nend , st₂ , refl | _ , stᵢ₂ , _ =
      ⊥-elim (nstep-nend-⊥ n⨾ stⱼ′)
    seqWB .WellBehaved.no-new-branch/step {nend} st idle stᵢ stⱼ′ ceq =
      ⊥-elim (nstep-nend-⊥ n⨾ st)

    seqWB .WellBehaved.step-diamond {live (inj₂ a)} st st′ ind
      with sstep-inv₁ n₁ n₂ {a = a} st | sstep-inv₁ n₁ n₂ {a = a} st′
    ... | _ , st₁ , refl | _ , st₂ , refl = diamond₁ st₁ st₂ ind
      where
      -- Absurd seam cases: the component diamond would need a step from
      -- its end.
      diamond₁ :
        ∀ {a′ α α′} {t₀₁ t₀₂ : NState n₁}
        → NStep n₁ (live a′) α t₀₁
        → NStep n₁ (live a′) α′ t₀₂
        → α ⋄ α′
        → ∃[ u ] ∃[ u′ ] NStep n⨾ (seamTo n₁ n₂ t₀₁) α′ u
                       × NStep n⨾ (seamTo n₁ n₂ t₀₂) α u′ × u T⨾.~ u′
      diamond₁ {t₀₁ = live x} {t₀₂ = live y} st₁ st₂ ind′
        with W₁.step-diamond st₁ st₂ ind′
      ... | u₀ , u₁ , d₁ , d₂ , pu =
        seamTo n₁ n₂ u₀ , seamTo n₁ n₂ u₁ , stepSeq₁ d₁ , stepSeq₁ d₂
        , ~-seam pu
      diamond₁ {t₀₁ = nend} st₁ st₂ ind′
        with W₁.step-diamond st₁ st₂ ind′
      ... | _ , _ , d₁ , _ , _ = ⊥-elim (nstep-nend-⊥ n₁ d₁)
      diamond₁ {t₀₁ = live x} {t₀₂ = nend} st₁ st₂ ind′
        with W₁.step-diamond st₁ st₂ ind′
      ... | _ , _ , _ , d₂ , _ = ⊥-elim (nstep-nend-⊥ n₁ d₂)
    seqWB .WellBehaved.step-diamond {live (inj₁ b)} st st′ ind
      with sstep-inv₂ n₁ n₂ {b = b} st | sstep-inv₂ n₁ n₂ {b = b} st′
    ... | _ , st₂ , refl | _ , st₂′ , refl = diamond₂ st₂ st₂′ ind
      where
      diamond₂ :
        ∀ {b′ α α′} {c₁ c₂ : NState n₂}
        → NStep n₂ (live b′) α c₁
        → NStep n₂ (live b′) α′ c₂
        → α ⋄ α′
        → ∃[ u ] ∃[ u′ ] NStep n⨾ (injR c₁) α′ u
                       × NStep n⨾ (injR c₂) α u′ × u T⨾.~ u′
      diamond₂ {c₁ = live x} {c₂ = live y} st₁ st₂ ind′
        with W₂.step-diamond st₁ st₂ ind′
      ... | v , w , d₁ , d₂ , pv =
        injR v , injR w , stepSeq₂ d₁ , stepSeq₂ d₂ , ~-injR pv
      diamond₂ {c₁ = nend} st₁ st₂ ind′
        with W₂.step-diamond st₁ st₂ ind′
      ... | _ , _ , d₁ , _ , _ = ⊥-elim (nstep-nend-⊥ n₂ d₁)
      diamond₂ {c₁ = live x} {c₂ = nend} st₁ st₂ ind′
        with W₂.step-diamond st₁ st₂ ind′
      ... | _ , _ , _ , d₂ , _ = ⊥-elim (nstep-nend-⊥ n₂ d₂)
    seqWB .WellBehaved.step-diamond {nend} st st′ ind =
      ⊥-elim (nstep-nend-⊥ n⨾ st)

  -- ── the synchronous facts ──

  module SeqSync
    (n₁ n₂ : Net)
    (sy₁ : Synchronous (netTheory n₁))
    (sy₂ : Synchronous (netTheory n₂))
    (scm : SeamComm n₁ n₂)
    where

    private
      module S₁ = Synchronous sy₁
      module S₂ = Synchronous sy₂

      n⨾ : Net
      n⨾ = n₁ ⨾ n₂

    seqSync : Synchronous (netTheory n⨾)
    seqSync .Synchronous.balanced {live (inj₂ a)} st
      with sstep-inv₁ n₁ n₂ {a = a} st
    ... | _ , st₁ , _ = S₁.balanced st₁
    seqSync .Synchronous.balanced {live (inj₁ b)} st
      with sstep-inv₂ n₁ n₂ {b = b} st
    ... | _ , st₂ , _ = S₂.balanced st₂
    seqSync .Synchronous.balanced {nend} st =
      ⊥-elim (nstep-nend-⊥ n⨾ st)

    seqSync .Synchronous.no-new-comm/step {live (inj₂ a)} st idle stγ
      with sstep-inv₁ n₁ n₂ {a = a} st
    seqSync .Synchronous.no-new-comm/step {live (inj₂ a)} st idle stγ
      | live a′ , st₁ , refl
      with sstep-inv₁ n₁ n₂ {a = a′} stγ
    ... | _ , stγ₁ , _ =
      let tγ , grγ = S₁.no-new-comm/step st₁ idle stγ₁
      in seamTo n₁ n₂ tγ , stepSeq₁ grγ
    seqSync .Synchronous.no-new-comm/step {live (inj₂ a)} st idle stγ
      | nend , st₁ , refl
      with ninit n₂ in eqI
    ... | nend = ⊥-elim (nstep-nend-⊥ n⨾ stγ)
    ... | live c₀
      with sstep-inv₂ n₁ n₂ {b = c₀} stγ
    ...   | _ , stγ₂ , _ =
      let tγ , mγ =
            scm (nix n₁ (live a))
              (at₁ n₁ a (nstep⇒listed n₁ {s = live a} st₁))
              (nstep⇒listed n₂ {s = live c₀} stγ₂)
              idle
      in seamTo n₁ n₂ tγ
       , stepSeq₁ (nlisted⇒step n₁ {s = live a} (from₁ n₁ a mγ))
    seqSync .Synchronous.no-new-comm/step {live (inj₁ b)} st idle stγ
      with sstep-inv₂ n₁ n₂ {b = b} st
    seqSync .Synchronous.no-new-comm/step {live (inj₁ b)} st idle stγ
      | live b₁ , st₂ , refl
      with sstep-inv₂ n₁ n₂ {b = b₁} stγ
    ... | _ , stγ₂ , _ =
      let uγ , grγ = S₂.no-new-comm/step st₂ idle stγ₂
      in injR uγ , stepSeq₂ grγ
    seqSync .Synchronous.no-new-comm/step {live (inj₁ b)} st idle stγ
      | nend , st₂ , refl =
      ⊥-elim (nstep-nend-⊥ n⨾ stγ)
    seqSync .Synchronous.no-new-comm/step {nend} st idle stγ =
      ⊥-elim (nstep-nend-⊥ n⨾ st)
