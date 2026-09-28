{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)

open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Data.Fin.Subset using (_∉_; Nonempty)
open import Data.Sum using (inj₁; inj₂)

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.Any.Properties as AnyProp
import Data.List.Relation.Unary.All.Properties as AllProp

open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; sym; trans)

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

    -- Traces: the single primitive multi-step judgement everything else is
    -- built from.

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

    -- `P ∈T G`: there is a trace out of `G` somewhere along which `P` is
    -- mentioned. `G -[¬ P ]->* G′`: there is a trace from `G` to `G′` none
    -- of whose actions mention `P`. Both are existentials over `_-[_]->_`,
    -- pairing a run with a property of the run's *labels alone*
    -- (`Any`/`All` over `List Action`, independent of which `Behav` states
    -- the run passes through) — that decoupling is what makes bisimulation
    -- transport for both relations reduce to transporting the run and
    -- reusing the label-level witness unchanged (see `tr-transport`/
    -- `stepback/~*` below, and `∈~`/`skip/∈T-back`).

    _∈T_ : Part → Behav → Set
    P ∈T G = ∃[ αs ] ∃[ G′ ] (G -[ αs ]-> G′) × Any (P ∈α_) αs

    _∉T_ : Part → Behav → Set
    P ∉T G = ¬ P ∈T G

    ended : Behav → Set
    ended G = ∀ P → ¬ P ∈T G

    infix 4 _-[¬_]->*_

    _-[¬_]->*_ : Behav → Part → Behav → Set
    G -[¬ P ]->* G′ = ∃[ αs ] (G -[ αs ]-> G′) × All (P ∉α_) αs

    -- Small reusable helpers (kept because each is called at several sites
    -- below, not to mirror any deleted constructor's name/shape).

    in/α : ∀ {P G G′ α} → G -< α >-> G′ → P ∈α α → P ∈T G
    in/α gr px = _ ∷ [] , _ , tr/step gr tr/refl , here px

    in/later : ∀ {P G G′ α} → G -< α >-> G′ → P ∈T G′ → P ∈T G
    in/later gr (αs , G″ , tr , mem) = _ ∷ αs , G″ , tr/step gr tr , there mem

    in/ev : ∀ {P e G α G′} → G -< α >-> G′ → ev α P ≡ just e → P ∈T G
    in/ev gr eq = in/α gr (_ , eq)

    skip/refl : ∀ {G P} → G -[¬ P ]->* G
    skip/refl = [] , tr/refl , []

    tr¬/step :
      ∀ {G G′ G″ P α}
      → G -< α >-> G′ → P ∉α α → G′ -[¬ P ]->* G″ → G -[¬ P ]->* G″
    tr¬/step gr P∉α (αs , tr , allP) = _ ∷ αs , tr/step gr tr , P∉α ∷ allP

    skip/one :
      ∀ {G G′ P α}
      → G -< α >-> G′
      → P ∉α α
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

    -- Trace concatenation, not a bisimulation transport, but the same
    -- "membership witness only depends on the labels" character: the
    -- prefix's trace is prepended via `tr/trans`, and `Q`'s membership
    -- witness in the suffix is lifted across the append via `Any`'s own
    -- append lemma, untouched otherwise.  Unused today; kept for
    -- `FUTURE_WORK.md` §A.
    skip/∈T-back :
      ∀ {G G′ P Q}
      → G -[¬ P ]->* G′
      → Q ∈T G′
      → Q ∈T G
    skip/∈T-back (αs , tr , _) (βs , H , tr′ , mem) =
      αs ++ βs , H , tr/trans tr tr′ , AnyProp.++⁺ʳ αs mem

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

    -- Trace-level bisimulation transport, generalizing `~L` from a single
    -- step to a whole run: if `G ~ G′`, then `G` and `G′` accept exactly
    -- the same traces, with bisimilar endpoints.
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

  record WellBehaved {N : ℕ} (B : BTheory N) : Set₁ where
    open Definitions.Actions N
    open Definitions.Common N
    open BTheory B

    field
      -- Action equality: a receiver of `α` that takes part in `α′` means
      -- the two steps are the same communication.

      -- (`overlap` would be the natural name, but it is an Agda keyword.)
      recv-overlap :
        ∀ {G α α′ G′ G″ Q}
        → G -< α  >-> G′
        → G -< α′ >-> G″
        → Recv α Q
        → Q ∈α α′
        → comm α ≡ comm α′

      step-deterministic :
        ∀ {G α G′ G″}
        → G -< α >-> G′
        → G -< α >-> G″
        → G′ ≡ G″

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

    -- Trace-level backward bisimulation transport, generalizing `stepback/~`
    -- from a single step to a whole run.
    stepback/~* :
      ∀ {αs G₀ G₁ G₁′}
      → G₁ ~ G₁′
      → G₀ -[ αs ]-> G₁
      → ∃[ G₀′ ] (G₀ ~ G₀′) × (G₀′ -[ αs ]-> G₁′)
    stepback/~* G₁~G₁′ tr/refl =
      _ , G₁~G₁′ , tr/refl
    stepback/~* G₁~G₁′ (tr/step gr tr) =
      let _ , H~H′ , tr′   = stepback/~* G₁~G₁′ tr
          _ , G₀~G₀′ , gr′ = stepback/~ H~H′ gr
      in _ , G₀~G₀′ , tr/step gr′ tr′

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

    -- `skip/advance`/`no-new-branch/skip` recurse via `-aux` helpers that
    -- take the run `tr : G -[ αs ]-> G′` as its own curried argument
    -- (rather than re-packing it into a fresh tuple at each recursive
    -- call) so the termination checker sees a plain, single-argument
    -- structural recursion on `_-[_]->_` — bundling `tr` back together
    -- with the `All`-witness into one Σ at the call site (as the public
    -- wrappers below still take) obscures that from the checker, even
    -- though every piece is individually a genuine subterm.

    skip/advance-aux :
      ∀ {G G′ Gα P α αs}
      → G -[ αs ]-> G′
      → All (P ∉α_) αs
      → G -< α >-> Gα
      → P ∈α α
      → ∃[ G′α ] G′ -< α >-> G′α × Gα -[¬ P ]->* G′α
    skip/advance-aux tr/refl [] grα _ =
      _ , grα , skip/refl
    skip/advance-aux (tr/step grβ tr) (P∉β ∷ allP) grα P∈α
      with step-diamond grα grβ (active-inactive/⋄ grα grβ P∈α P∉β)
    ... | G◇ , Gα↝G◇ , Gβ↝G◇
      with skip/advance-aux tr allP Gβ↝G◇ P∈α
    ... | G′α , G′↝G′α , G◇↝G′α =
      G′α , G′↝G′α , tr¬/step Gα↝G◇ P∉β G◇↝G′α

    skip/advance :
      ∀ {G G′ Gα P α}
      → G -[¬ P ]->* G′
      → G -< α >-> Gα
      → P ∈α α
      → ∃[ G′α ] G′ -< α >-> G′α × Gα -[¬ P ]->* G′α
    skip/advance (_ , tr , allP) =
      skip/advance-aux tr allP

    no-new-branch/skip-aux :
      ∀ {G G′ Gᵢ Gⱼ′ γ γ′ Q αs}
      → G -[ αs ]-> G′
      → All (Q ∉α_) αs
      → Recv γ Q
      → G  -< γ  >-> Gᵢ
      → G′ -< γ′ >-> Gⱼ′
      → comm γ′ ≡ comm γ
      → ∃[ Gⱼ ] G -< γ′ >-> Gⱼ
    no-new-branch/skip-aux tr/refl [] rQ grᵢ grⱼ ceq =
      _ , grⱼ
    no-new-branch/skip-aux {γ = γ} {Q = Q}
      (tr/step grβ tr) (Q∉β ∷ allP) rQ grᵢ grⱼ′ ceq
      with step-diamond grᵢ grβ
             (active-inactive/⋄ grᵢ grβ (Recv→∈α {γ} {Q} rQ) Q∉β)
    ... | _ , _ , grᵢ′
      with no-new-branch/skip-aux tr allP rQ grᵢ′ grⱼ′ ceq
    ... | _ , grⱼ =
      no-new-branch/step grβ (recv-idle/all grᵢ grβ rQ Q∉β) grᵢ grⱼ ceq

    no-new-branch/skip :
      ∀ {G G′ Gᵢ Gⱼ′ γ γ′ Q}
      → G -[¬ Q ]->* G′
      → Recv γ Q
      → G  -< γ  >-> Gᵢ
      → G′ -< γ′ >-> Gⱼ′
      → comm γ′ ≡ comm γ
      → ∃[ Gⱼ ] G -< γ′ >-> Gⱼ
    no-new-branch/skip (_ , tr , allP) =
      no-new-branch/skip-aux tr allP

    branch/before :
      ∀ {G G′ Gᵢ Gⱼ′ γ γ′ Q}
      → (tr   : G -[¬ Q ]->* G′)
      → Recv γ Q
      → (grᵢ  : G  -< γ  >-> Gᵢ)
      → (grⱼ′ : G′ -< γ′ >-> Gⱼ′)
      → comm γ′ ≡ comm γ
      → ∃[ Gⱼ ] (G -< γ′ >-> Gⱼ) × (Gⱼ -[¬ Q ]->* Gⱼ′)
    branch/before {γ = γ} {γ′} {Q} tr rQ grᵢ grⱼ′ ceq
      with no-new-branch/skip tr rQ grᵢ grⱼ′ ceq
    ... | Gⱼ , grⱼ
      with skip/advance tr grⱼ
             (comm-∈α {γ} {γ′} {Q} (sym ceq) (Recv→∈α {γ} {Q} rQ))
    ... | _ , grⱼ″ , trⱼ
      rewrite step-deterministic grⱼ″ grⱼ′ =
      Gⱼ , grⱼ , trⱼ

    -- Two receives by `Q`, one before and one after a `Q`-free run, are the
    -- same communication.
    recv/same-comm :
      ∀ {G G′ Gγ Gγ′ γ γ′ Q}
      → G -[¬ Q ]->* G′
      → G -< γ >-> Gγ
      → Recv γ Q
      → G′ -< γ′ >-> Gγ′
      → Recv γ′ Q
      → comm γ′ ≡ comm γ
    recv/same-comm {γ = γ} {Q = Q} tr grγ rQ grγ′ rQ′
      with skip/advance tr grγ (Recv→∈α {γ} {Q} rQ)
    ... | _ , grγ-at-G′ , _ =
      recv-overlap {Q = Q} grγ′ grγ-at-G′ rQ′ (Recv→∈α {γ} {Q} rQ)

  -- Facts of the synchronous instance only; consumed by `Safety/` alone.
  record Synchronous {N : ℕ} (B : BTheory N) : Set₁ where
    open Definitions.Actions N
    open Definitions.Common N
    open BTheory B

    field
      -- Every step is one multicast to somebody, and nobody sends to
      -- themselves.
      balanced :
        ∀ {G G′ α}
        → G -< α >-> G′
        → ∃[ P ] ∃[ Qs ] ∃[ c ] P ∉ Qs × Nonempty Qs × α ≡ P ⟶ Qs # c

      -- Unrelated steps cannot be the first point where a communication
      -- becomes available.
      no-new-comm/step :
        ∀ {G G′ Gγ β γ}
        → G -< β >-> G′
        → (∀ X → X ∈α γ → X ∉α β)
        → G′ -< γ >-> Gγ
        → ∃[ Gγ′ ] G -< γ >-> Gγ′

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

    -- So `P`'s send event determines the action.  This is what `⊢p → ⊢a`
    -- needs at a send (`AlgNorm.sendAt`).
    send-det :
      ∀ {G G′ G″ α α′ P Qs c}
      → G -< α >-> G′
      → G -< α′ >-> G″
      → ev α P ≡ just ((! Qs) # c)
      → ev α′ P ≡ just ((! Qs) # c)
      → α ≡ α′
    send-det gr gr′ eq eq′ =
      trans (proj₂ (send-action gr eq)) (sym (proj₂ (send-action gr′ eq′)))
