{-# OPTIONS --guardedness #-}

-- Well-behavedness of sequential composition (`n₁ ⨾ n₂`).
--
-- All *local* axioms compose: they inherit from the component theories via
-- the step inversions (`sstep-inv₁`/`sstep-inv₂`), with the two seam cases
-- (`no-new-comm/step` and `no-new-branch/step`, where a step crosses from
-- `n₁`'s pre-end states into `ninit n₂`) discharged by the decidable
-- seam-causality conditions `SeamComm`/`SeamBranch` — checks over the seam
-- edges only, never a product sweep.  The diamond's seam case is absurd: in
-- a well-behaved component, two independent actions cannot both leave from
-- a state entering `end` (the component diamond would demand a step *from*
-- its end).
--
-- The one genuinely global axiom is `stepback/~`: sequencing creates new
-- bisimilarity classes spanning states arbitrarily far from the seam (e.g.
-- `X∙X∙end ⨾ μ(X∙var₀)` merges the whole chain with the loop), so no seam-
-- local premise can be complete.  It is instead *decided* on the net's
-- finite presentation (`Stepback (underlying (present (n₁ ⨾ n₂)))`, from
-- `finiteStepback?`/`stepback/sound`) and transported to the network theory
-- by `Definitions.Graph.NetworkPresent.stepbackG→N` — the network itself is never
-- flattened into an open graph.

open import Data.Bool using (T)
open import Data.Bool.Properties using (T-irrelevant)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
import Data.Fin.Properties as FinP
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as MemP
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ)
open import Data.Product
  using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (map′; _→-dec_)

open import Definitions.Behav using (BTheory; WellBehaved; Synchronous)

module Definitions.Graph.NetworkSeq (N : ℕ) where

  open import Definitions.Actions N
  open import Definitions.Graph.Action N using (_≟Action_; _≟Comm_)
  open import Definitions.Graph.Algebra N using (underlying)
  open import Definitions.Graph.WellBehaved N using (Stepback)
  open import Definitions.Graph.Network N
  open import Definitions.Graph.NetworkPresent N using (stepbackG→N)

  -- ── step intro/inversion for the two parts of a `⨾` ──

  stepSeq₁ :
    ∀ {n₁ n₂ a α t₀}
    → NStep n₁ (live a) α t₀
    → NStep (n₁ ⨾ n₂) (live (inj₂ a)) α (seamTo n₁ n₂ t₀)
  stepSeq₁ {n₁} {n₂} {a} st =
    nlisted⇒step (n₁ ⨾ n₂) {s = live (inj₂ a)}
      (MemP.∈-map⁺ (λ e → proj₁ e , seamTo n₁ n₂ (proj₂ e))
        (nstep⇒listed n₁ {s = live a} st))

  stepSeq₂ :
    ∀ {n₁ n₂ b α b′}
    → NStep n₂ (live b) α b′
    → NStep (n₁ ⨾ n₂) (live (inj₁ b)) α (injR b′)
  stepSeq₂ {n₁} {n₂} {b} st =
    nlisted⇒step (n₁ ⨾ n₂) {s = live (inj₁ b)}
      (MemP.∈-map⁺ (λ e → proj₁ e , injR (proj₂ e))
        (nstep⇒listed n₂ {s = live b} st))

  sstep-inv₁ :
    ∀ n₁ n₂ {a α t}
    → NStep (n₁ ⨾ n₂) (live (inj₂ a)) α t
    → Σ[ t₀ ∈ NState n₁ ]
        NStep n₁ (live a) α t₀ × t ≡ seamTo n₁ n₂ t₀
  sstep-inv₁ n₁ n₂ {a} st
    with MemP.∈-map⁻ (λ e → proj₁ e , seamTo n₁ n₂ (proj₂ e))
           (nstep⇒listed (n₁ ⨾ n₂) {s = live (inj₂ a)} st)
  ... | (α₀ , t₀) , m₀ , refl =
    t₀ , nlisted⇒step n₁ {s = live a} m₀ , refl

  sstep-inv₂ :
    ∀ n₁ n₂ {b α t}
    → NStep (n₁ ⨾ n₂) (live (inj₁ b)) α t
    → Σ[ b′ ∈ NState n₂ ]
        NStep n₂ (live b) α b′ × t ≡ injR b′
  sstep-inv₂ n₁ n₂ {b} st
    with MemP.∈-map⁻ (λ e → proj₁ e , injR (proj₂ e))
           (nstep⇒listed (n₁ ⨾ n₂) {s = live (inj₁ b)} st)
  ... | (α₀ , b′) , m₀ , refl =
    b′ , nlisted⇒step n₂ {s = live b} m₀ , refl

  -- the network end never steps
  nstep-nend-⊥ : ∀ n {α t} → NStep n nend α t → ⊥
  nstep-nend-⊥ n st = un st

  -- ── the seam-causality conditions ──

  -- decide `∃ t. (γ , t) ∈ xs`
  findAction :
    ∀ {A : Set} (γ : Action) (xs : List (Action × A))
    → Dec (∃[ t ] (γ , t) ∈ xs)
  findAction γ [] = no λ ()
  findAction γ ((α , u) ∷ xs) with γ ≟Action α
  ... | yes refl = yes (u , here refl)
  ... | no γ≢α with findAction γ xs
  ...   | yes (t , m) = yes (t , there m)
  ...   | no ¬ex =
    no λ where
      (t , here eq)  → γ≢α (cong proj₁ eq)
      (t , there m)  → ¬ex (t , m)

  -- `no-new-comm/step` at the seam: an action available at `n₂`'s start
  -- none of whose participants is involved in a seam-entering action `β`
  -- must already be available just before the seam.
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
            nEq? n₁ (proj₂ e₁) nend →-dec
            All.all?
              (λ e₂ →
                FinP.all?
                  (λ X → (X ∈α? proj₁ e₂) →-dec (X ∉α? proj₁ e₁))
                →-dec
                findAction (proj₁ e₂) (nedges n₁ (nst n₁ i)))
              (nedges n₂ (ninit n₂)))
          (nedges n₁ (nst n₁ i)))
    where
    from :
      (∀ i →
        All.All
          (λ e₁ →
            proj₂ e₁ ≡ nend →
            All.All
              (λ e₂ →
                (∀ X → X ∈α proj₁ e₂ → X ∉α proj₁ e₁) →
                ∃[ t₀ ] (proj₁ e₂ , t₀) ∈ nedges n₁ (nst n₁ i))
              (nedges n₂ (ninit n₂)))
          (nedges n₁ (nst n₁ i)))
      → SeamComm n₁ n₂
    from as i mβ mγ idle =
      All.lookup (All.lookup (as i) mβ refl) mγ idle

    to :
      SeamComm n₁ n₂
      → ∀ i →
        All.All
          (λ e₁ →
            proj₂ e₁ ≡ nend →
            All.All
              (λ e₂ →
                (∀ X → X ∈α proj₁ e₂ → X ∉α proj₁ e₁) →
                ∃[ t₀ ] (proj₁ e₂ , t₀) ∈ nedges n₁ (nst n₁ i))
              (nedges n₂ (ninit n₂)))
          (nedges n₁ (nst n₁ i))
    to sc i =
      All.tabulate λ {e₁} m₁ eq →
        All.tabulate λ {e₂} m₂ idle →
          sc i
            (subst (λ z → (proj₁ e₁ , z) ∈ nedges n₁ (nst n₁ i)) eq m₁)
            m₂ idle

  -- `no-new-branch/step` at the seam: a branch available at `n₂`'s start,
  -- of the same communication as a branch `α₁` that already exists just
  -- before the seam, whose receivers are uninvolved in the seam-entering
  -- action, must already exist just before the seam.
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
            nEq? n₁ (proj₂ e₁) nend →-dec
            All.all?
              (λ eᵢ →
                All.all?
                  (λ e₂ →
                    (comm (proj₁ e₂) ≟Comm comm (proj₁ eᵢ))
                      →-dec
                    FinP.all?
                      (λ Q → Recv? (proj₁ eᵢ) Q →-dec (Q ∉α? proj₁ e₁))
                      →-dec
                    findAction (proj₁ e₂) (nedges n₁ (nst n₁ i)))
                  (nedges n₂ (ninit n₂)))
              (nedges n₁ (nst n₁ i)))
          (nedges n₁ (nst n₁ i)))
    where
    from :
      (∀ i →
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
          (nedges n₁ (nst n₁ i)))
      → SeamBranch n₁ n₂
    from as i mβ mᵢ ceq idle m₂ =
      All.lookup (All.lookup (All.lookup (as i) mβ refl) mᵢ) m₂ ceq idle

    to :
      SeamBranch n₁ n₂
      → ∀ i →
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
    (gsb : Stepback (underlying (present (n₁ ⨾ n₂))))
    where

    private
      module W₁ = WellBehaved wb₁
      module W₂ = WellBehaved wb₂

      n⨾ : Net
      n⨾ = n₁ ⨾ n₂

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
      cong (seamTo n₁ n₂) (W₁.step-deterministic st₁ st₁′)
    seqWB .WellBehaved.step-deterministic {live (inj₁ b)} st st′
      with sstep-inv₂ n₁ n₂ {b = b} st | sstep-inv₂ n₁ n₂ {b = b} st′
    ... | _ , st₂ , refl | _ , st₂′ , refl =
      cong injR (W₂.step-deterministic st₂ st₂′)
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

    seqWB .WellBehaved.step-is-prop st st′ =
      cong nstep (T-irrelevant (un st) (un st′))

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

    seqWB .WellBehaved.stepback/~ rel st =
      stepbackG→N n⨾ gsb rel st

    seqWB .WellBehaved.step-diamond {live (inj₂ a)} st st′ ind
      with sstep-inv₁ n₁ n₂ {a = a} st | sstep-inv₁ n₁ n₂ {a = a} st′
    ... | _ , st₁ , refl | _ , st₂ , refl = diamond₁ st₁ st₂ ind
      where
      -- a well-behaved component never has two *independent* actions where
      -- one enters its end: the component diamond would demand a step from
      -- the end, which has none — hence the absurd cases.
      diamond₁ :
        ∀ {a′ α α′} {t₀₁ t₀₂ : NState n₁}
        → NStep n₁ (live a′) α t₀₁
        → NStep n₁ (live a′) α′ t₀₂
        → α ⋄ α′
        → ∃[ u ] NStep n⨾ (seamTo n₁ n₂ t₀₁) α′ u
               × NStep n⨾ (seamTo n₁ n₂ t₀₂) α u
      diamond₁ {t₀₁ = live x} {t₀₂ = live y} st₁ st₂ ind′
        with W₁.step-diamond st₁ st₂ ind′
      ... | u₀ , d₁ , d₂ = seamTo n₁ n₂ u₀ , stepSeq₁ d₁ , stepSeq₁ d₂
      diamond₁ {t₀₁ = nend} st₁ st₂ ind′
        with W₁.step-diamond st₁ st₂ ind′
      ... | u₀ , d₁ , d₂ = ⊥-elim (nstep-nend-⊥ n₁ d₁)
      diamond₁ {t₀₁ = live x} {t₀₂ = nend} st₁ st₂ ind′
        with W₁.step-diamond st₁ st₂ ind′
      ... | u₀ , d₁ , d₂ = ⊥-elim (nstep-nend-⊥ n₁ d₂)
    seqWB .WellBehaved.step-diamond {live (inj₁ b)} st st′ ind
      with sstep-inv₂ n₁ n₂ {b = b} st | sstep-inv₂ n₁ n₂ {b = b} st′
    ... | _ , st₂ , refl | _ , st₂′ , refl = diamond₂ st₂ st₂′ ind
      where
      diamond₂ :
        ∀ {b′ α α′} {c₁ c₂ : NState n₂}
        → NStep n₂ (live b′) α c₁
        → NStep n₂ (live b′) α′ c₂
        → α ⋄ α′
        → ∃[ u ] NStep n⨾ (injR c₁) α′ u × NStep n⨾ (injR c₂) α u
      diamond₂ {c₁ = live x} {c₂ = live y} st₁ st₂ ind′
        with W₂.step-diamond st₁ st₂ ind′
      ... | v , d₁ , d₂ = injR v , stepSeq₂ d₁ , stepSeq₂ d₂
      diamond₂ {c₁ = nend} st₁ st₂ ind′
        with W₂.step-diamond st₁ st₂ ind′
      ... | v , d₁ , d₂ = ⊥-elim (nstep-nend-⊥ n₂ d₁)
      diamond₂ {c₁ = live x} {c₂ = nend} st₁ st₂ ind′
        with W₂.step-diamond st₁ st₂ ind′
      ... | v , d₁ , d₂ = ⊥-elim (nstep-nend-⊥ n₂ d₂)
    seqWB .WellBehaved.step-diamond {nend} st st′ ind =
      ⊥-elim (nstep-nend-⊥ n⨾ st)

  -- ── the synchronous facts ──
  --
  -- `balanced` by inversion (the action of a `⨾` step is a component's);
  -- `no-new-comm/step` is local except at the seam, where `SeamComm`
  -- discharges it.

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
