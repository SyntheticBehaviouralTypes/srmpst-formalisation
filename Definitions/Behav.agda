{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)

open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.Any.Properties as AnyProp
import Data.List.Relation.Unary.All.Properties as AllProp

open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; sym)

open import Definitions.Expr using (Sort)

module Definitions.Behav where

  import Definitions.Actions
  import Definitions.Common

  record BTheory (N : ℕ) : Set₁ where
    open Definitions.Actions N
    open Action
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

    in/send : ∀ {G α G′} → G -< α >-> G′ → sender α ∈T G
    in/send gr =
      in/α gr (∈S refl)

    in/recv : ∀ {G α G′} → G -< α >-> G′ → receiver α ∈T G
    in/recv gr =
      in/α gr (∈R refl)

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
    -- append lemma, untouched otherwise.
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
    open Action
    open Definitions.Common N
    open BTheory B

    field
      -- Action equality

      recv-overlap⇒same-comm :
        ∀ {G α α′ G′ G″}
        → G -< α  >-> G′
        → G -< α′ >-> G″
        → receiver α ∈α α′
        → comm α ≡ comm α′

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
        ∀ {G G′ G″ α I S T}
          {i : Fin (suc I)}
        → G -< α # i < S > >-> G′
        → G -< α # i < T > >-> G″
        → S ≡ T

      step-arity-deterministic :
        ∀ {G G′ G″ α I J S T}
          {i : Fin (suc I)}
          {j : Fin (suc J)}
        → G -< α # i < S > >-> G′
        → G -< α # j < T > >-> G″
        → I ≡ J

      -- There should be at most one proof term per transition in your LTS
      -- This is not fundamental, just an artifact of having G -< α >-> G' as
      -- argument of lemmas. The best would be to make such proof terms
      -- irrelevant, but I'm concerned that agda will not allow me to pattern
      -- match on it
      step-is-prop :
        ∀ {G β G′}
        → (gr₁ gr₂ : G -< β >-> G′)
        → gr₁ ≡ gr₂

      no-new-branch/step :
        ∀ {G G′ Gᵢ Gⱼ′ β γ cᵢ cⱼ}
        → G -< β >-> G′
        → Comm.receiver γ ∉α β
        → G  -< γ # cᵢ >-> Gᵢ
        → G′ -< γ # cⱼ >-> Gⱼ′
        → ∃[ Gⱼ ] G -< γ # cⱼ >-> Gⱼ

      -- Unrelated steps cannot be the first point where a communication
      -- becomes available.
      no-new-comm/step :
        ∀ {G G′ Gγ β γ}
        → G -< β >-> G′
        → sender γ ∉α β
        → receiver γ ∉α β
        → G′ -< γ >-> Gγ
        → ∃[ Gγ′ ] G -< γ >-> Gγ′

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
      ∀ {G G′ Gᵢ Gⱼ′ γ αs}
        {cᵢ cⱼ : Choice}
      → G -[ αs ]-> G′
      → All (Comm.receiver γ ∉α_) αs
      → G  -< γ # cᵢ >-> Gᵢ
      → G′ -< γ # cⱼ >-> Gⱼ′
      → ∃[ Gⱼ ] G -< γ # cⱼ >-> Gⱼ
    no-new-branch/skip-aux tr/refl [] grᵢ grⱼ =
      _ , grⱼ
    no-new-branch/skip-aux (tr/step grβ tr) (recvγ∉β ∷ allP) grᵢ grⱼ′
      with step-diamond grᵢ grβ (active-inactive/⋄ grᵢ grβ (∈R refl) recvγ∉β)
    ... | _ , _ , grᵢ′
      with no-new-branch/skip-aux tr allP grᵢ′ grⱼ′
    ... | _ , grⱼ =
      no-new-branch/step grβ recvγ∉β grᵢ grⱼ

    no-new-branch/skip :
      ∀ {G G′ Gᵢ Gⱼ′ γ}
        {cᵢ cⱼ : Choice}
      → G -[¬ Comm.receiver γ ]->* G′
      → G  -< γ # cᵢ >-> Gᵢ
      → G′ -< γ # cⱼ >-> Gⱼ′
      → ∃[ Gⱼ ] G -< γ # cⱼ >-> Gⱼ
    no-new-branch/skip (_ , tr , allP) =
      no-new-branch/skip-aux tr allP

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
      with no-new-branch/skip tr grᵢ grⱼ′
    ... | Gⱼ , grⱼ
      with skip/advance tr grⱼ (∈R refl)
    ... | _ , grⱼ″ , trⱼ
      rewrite step-deterministic grⱼ″ grⱼ′ =
      Gⱼ , grⱼ , trⱼ

    step-is-prop/eq :
      ∀ {G G′ G″ α}
      → (gr : G -< α >-> G′)
      → (gr′ : G -< α >-> G″)
      → (eq : G″ ≡ G′)
      → gr ≡ subst (G -< α >->_) eq gr′
    step-is-prop/eq gr gr′ refl = step-is-prop gr gr′

    ~R-L/id′ :
      ∀ {G G′ G″ α}
      → (G~G′ : G ~ G′)
      → (gr : G -< α >-> G″)
      → gr
        ≡ subst
            (G -< α >->_)
            (step-deterministic (~R→ G~G′ (~L→ G~G′ gr)) gr)
            (~R→ G~G′ (~L→ G~G′ gr))
    ~R-L/id′ G~G′ gr =
      step-is-prop/eq
        gr
        (~R→ G~G′ (~L→ G~G′ gr))
        (step-deterministic (~R→ G~G′ (~L→ G~G′ gr)) gr)
