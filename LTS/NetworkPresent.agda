{-# OPTIONS --guardedness #-}

-- Transport of well-behavedness across a network's finite presentation.
--
-- `LTS/Network.agda` gives every net `n` a graph presentation `present n`
-- with a state bijection (`nix`/`nst`, inverse by `nst-nix`/`nix-nst`) and a
-- step correspondence in both directions (`step⇒pres`/`pres⇒step`).  This
-- module lifts that isomorphism of LTSs to the two derived notions the
-- metatheory cares about:
--
--   * bisimilarity   (`~N→G`/`~G→N`, coinductive pairings), and
--   * well-behavedness (`pres→net`/`net→pres`).
--
-- `pres→net` lets a *decided* `wellBehaved?` result on a small presented
-- component enter the compositional network layer; `net→pres` hands the
-- graph-side checker a witness obtained compositionally (e.g. `parWB`)
-- without ever re-sweeping the presented product.
--
-- Implicit-pinning discipline: `GStep` is a bare `T (edge? …)`, so every
-- implicit endpoint of a graph-side step or axiom must be pinned by name at
-- the call site (the goal reduces to `T`-form and the unifier cannot invert
-- `edge?`); the net side (`NStep`) is a record, hence rigid, and infers.

open import Data.Bool using (T)
open import Data.Bool.Properties using (T-irrelevant)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Definitions.Behav using (BTheory; WellBehaved)

module LTS.NetworkPresent (N : ℕ) where

  open import Definitions.Actions N
  open import LTS.Core N
    using (Graph; State; graphTheory; step-is-prop)
    renaming (_-<_>->_ to GStep)
  open import LTS.Algebra N using (RootedGraph; underlying; initial)
  open import LTS.WellBehaved N using (Stepback)
  open import LTS.Network N

  module _ (n : Net) where

    private
      PG : Graph
      PG = underlying (present n)

      module TN = BTheory (netTheory n)
      module TG = BTheory (graphTheory PG)

      -- state coding is injective in both directions
      nix-inj : ∀ {s t} → nix n s ≡ nix n t → s ≡ t
      nix-inj {s} {t} eq =
        trans (sym (nst-nix n s)) (trans (cong (nst n) eq) (nst-nix n t))

      nst-inj : ∀ {i j} → nst n i ≡ nst n j → i ≡ j
      nst-inj {i} {j} eq =
        trans (sym (nix-nst n i)) (trans (cong (nix n) eq) (nix-nst n j))

      -- step correspondences with one endpoint already in coded form
      stepGN' :
        ∀ {s α j}
        → GStep {PG} (nix n s) α j
        → NStep n s α (nst n j)
      stepGN' {s} {α} {j} st =
        subst (λ z → NStep n z α (nst n j)) (nst-nix n s)
          (pres⇒step n {i = nix n s} {α = α} {j = j} st)

      stepNG' :
        ∀ {i α t}
        → NStep n (nst n i) α t
        → GStep {PG} i α (nix n t)
      stepNG' {i} {α} {t} st =
        subst (λ z → GStep {PG} z α (nix n t)) (nix-nst n i)
          (step⇒pres n {s = nst n i} {α = α} {t = t} st)

    -- ── bisimilarity transports (coinductive pairings) ──
    --
    -- The index adjustments (`nix-nst`/`nst-nix`) are carried as *equality
    -- arguments* into the corecursion and matched as `refl` at the next
    -- unfolding: wrapping the corecursive call in a subst-style fix-up
    -- function instead would break guardedness.

    mutual
      ≲N→G/eq :
        ∀ {s t i j}
        → nix n s ≡ i → nix n t ≡ j
        → TN._≲_ s t → TG._≲_ i j
      TG._≲_.simulate (≲N→G/eq {s} {t} refl refl sim) {α} {j₁} gr =
        let u , stU , rel = TN._≲_.simulate sim (stepGN' {s = s} {α = α} {j = j₁} gr)
        in nix n u
         , step⇒pres n {s = t} {α = α} {t = u} stU
         , ~N→G/eq (nix-nst n j₁) refl rel

      ~N→G/eq :
        ∀ {s t i j}
        → nix n s ≡ i → nix n t ≡ j
        → TN._~_ s t → TG._~_ i j
      ~N→G/eq eq₁ eq₂ (l , r) = ≲N→G/eq eq₁ eq₂ l , ≲N→G/eq eq₂ eq₁ r

    mutual
      ≲G→N/eq :
        ∀ {i j s t}
        → nst n i ≡ s → nst n j ≡ t
        → TG._≲_ i j → TN._≲_ s t
      TN._≲_.simulate (≲G→N/eq {i} {j} refl refl sim) {α} {u} stN =
        let j′ , grJ , rel =
              TG._≲_.simulate sim (stepNG' {i = i} {α = α} {t = u} stN)
        in nst n j′
         , pres⇒step n {i = j} {α = α} {j = j′} grJ
         , ~G→N/eq (nst-nix n u) refl rel

      ~G→N/eq :
        ∀ {i j s t}
        → nst n i ≡ s → nst n j ≡ t
        → TG._~_ i j → TN._~_ s t
      ~G→N/eq eq₁ eq₂ (l , r) = ≲G→N/eq eq₁ eq₂ l , ≲G→N/eq eq₂ eq₁ r

    ~N→G : ∀ {s t} → TN._~_ s t → TG._~_ (nix n s) (nix n t)
    ~N→G {s} {t} = ~N→G/eq {s = s} {t = t} refl refl

    ~G→N : ∀ {i j} → TG._~_ i j → TN._~_ (nst n i) (nst n j)
    ~G→N {i} {j} = ~G→N/eq {i = i} {j = j} refl refl

    -- ── well-behavedness transports ──

    pres→net :
      WellBehaved (graphTheory PG)
      → WellBehaved (netTheory n)
    pres→net W = record
      { recv-overlap⇒same-comm =
          λ {G} {α} {α′} {G′} {G″} st₁ st₂ r∈ →
            WG.recv-overlap⇒same-comm
              {G = nix n G} {α = α} {α′ = α′}
              {G′ = nix n G′} {G″ = nix n G″}
              (step⇒pres n {s = G} {α = α} {t = G′} st₁)
              (step⇒pres n {s = G} {α = α′} {t = G″} st₂)
              r∈
      ; sender≢receiver = λ {G} {G′} {α} st →
          WG.sender≢receiver
            {G = nix n G} {G′ = nix n G′} {α = α}
            (step⇒pres n {s = G} {α = α} {t = G′} st)
      ; step-deterministic = λ {G} {α} {G′} {G″} st₁ st₂ →
          nix-inj
            (WG.step-deterministic
              {G = nix n G} {α = α} {G′ = nix n G′} {G″ = nix n G″}
              (step⇒pres n {s = G} {α = α} {t = G′} st₁)
              (step⇒pres n {s = G} {α = α} {t = G″} st₂))
      ; step-sort-deterministic =
          λ {G} {G′} {G″} {α} {I} {S} {T = T₀} {i} st₁ st₂ →
            WG.step-sort-deterministic
              {G = nix n G} {G′ = nix n G′} {G″ = nix n G″}
              {α = α} {S = S} {T = T₀} {i = i}
              (step⇒pres n {s = G} {t = G′} st₁)
              (step⇒pres n {s = G} {t = G″} st₂)
      ; step-arity-deterministic =
          λ {G} {G′} {G″} {α} {I} {J} {S} {T = T₀} {i} {j} st₁ st₂ →
            WG.step-arity-deterministic
              {G = nix n G} {G′ = nix n G′} {G″ = nix n G″}
              {α = α} {S = S} {T = T₀} {i = i} {j = j}
              (step⇒pres n {s = G} {t = G′} st₁)
              (step⇒pres n {s = G} {t = G″} st₂)
      ; step-is-prop = λ st₁ st₂ →
          cong nstep (T-irrelevant (un st₁) (un st₂))
      ; no-new-branch/step =
          λ {G} {G′} {Gᵢ} {Gⱼ′} {β} {γ} {cᵢ} {cⱼ} st r∉ stᵢ stⱼ′ →
            let Gⱼ , grⱼ =
                  WG.no-new-branch/step
                    {G = nix n G} {G′ = nix n G′}
                    {Gᵢ = nix n Gᵢ} {Gⱼ′ = nix n Gⱼ′}
                    {β = β} {γ = γ} {cᵢ = cᵢ} {cⱼ = cⱼ}
                    (step⇒pres n {s = G} {α = β} {t = G′} st)
                    r∉
                    (step⇒pres n {s = G} {t = Gᵢ} stᵢ)
                    (step⇒pres n {s = G′} {t = Gⱼ′} stⱼ′)
            in nst n Gⱼ , stepGN' {s = G} {j = Gⱼ} grⱼ
      ; no-new-comm/step = λ {G} {G′} {Gγ} {β} {γ} st s∉ r∉ stγ →
          let Gγ′ , grγ =
                WG.no-new-comm/step
                  {G = nix n G} {G′ = nix n G′} {Gγ = nix n Gγ}
                  {β = β} {γ = γ}
                  (step⇒pres n {s = G} {α = β} {t = G′} st)
                  s∉ r∉
                  (step⇒pres n {s = G′} {α = γ} {t = Gγ} stγ)
          in nst n Gγ′ , stepGN' {s = G} {α = γ} {j = Gγ′} grγ
      ; stepback/~ = λ {α} {G₀} {G₁} {G₁′} rel st →
          let i₀′ , relG , gr′ =
                WG.stepback/~
                  {α = α} {G₀ = nix n G₀}
                  {G₁ = nix n G₁} {G₁′ = nix n G₁′}
                  (~N→G {s = G₁} {t = G₁′} rel)
                  (step⇒pres n {s = G₀} {α = α} {t = G₁} st)
          in nst n i₀′
           , ~G→N/eq {i = nix n G₀} {j = i₀′} (nst-nix n G₀) refl relG
           , subst (NStep n (nst n i₀′) α) (nst-nix n G₁′)
               (pres⇒step n {i = i₀′} {α = α} {j = nix n G₁′} gr′)
      ; step-diamond = λ {G} {α} {G₁} {α′} {G₂} st₁ st₂ ind →
          let k , gr₁ , gr₂ =
                WG.step-diamond
                  {G = nix n G} {α = α} {G₁ = nix n G₁}
                  {α′ = α′} {G₂ = nix n G₂}
                  (step⇒pres n {s = G} {α = α} {t = G₁} st₁)
                  (step⇒pres n {s = G} {α = α′} {t = G₂} st₂)
                  ind
          in nst n k
           , stepGN' {s = G₁} {α = α′} {j = k} gr₁
           , stepGN' {s = G₂} {α = α} {j = k} gr₂
      }
      where module WG = WellBehaved W

    -- A `Stepback` property *decided* on the presentation (via
    -- `finiteStepback?`/`stepback/sound`) becomes the `stepback/~` axiom of
    -- the network theory.  This is the global ingredient of the sequential-
    -- composition theorem (`LTS/NetworkSeq.agda`): all other axioms of `⨾`
    -- compose locally, and this transport carries the one that cannot.
    stepbackG→N :
      Stepback PG
      → ∀ {α s t t′}
      → BTheory._~_ (netTheory n) t t′
      → NStep n s α t
      → Σ[ s′ ∈ NState n ]
          BTheory._~_ (netTheory n) s s′ × NStep n s′ α t′
    stepbackG→N sbG {α} {s} {t} {t′} rel st =
      let i₀′ , relG , gr′ =
            sbG {α = α} {s = nix n s} {t = nix n t} {t′ = nix n t′}
              (~N→G {s = t} {t = t′} rel)
              (step⇒pres n {s = s} {α = α} {t = t} st)
      in nst n i₀′
       , ~G→N/eq {i = nix n s} {j = i₀′} (nst-nix n s) refl relG
       , subst (NStep n (nst n i₀′) α) (nst-nix n t′)
           (pres⇒step n {i = i₀′} {α = α} {j = nix n t′} gr′)

    net→pres :
      WellBehaved (netTheory n)
      → WellBehaved (graphTheory PG)
    net→pres W = record
      { recv-overlap⇒same-comm =
          λ {i} {α} {α′} {i′} {i″} st₁ st₂ r∈ →
            WN.recv-overlap⇒same-comm
              (pres⇒step n {i = i} {α = α} {j = i′} st₁)
              (pres⇒step n {i = i} {α = α′} {j = i″} st₂)
              r∈
      ; sender≢receiver = λ {i} {i′} {α} st →
          WN.sender≢receiver (pres⇒step n {i = i} {α = α} {j = i′} st)
      ; step-deterministic = λ {i} {α} {i′} {i″} st₁ st₂ →
          nst-inj
            (WN.step-deterministic
              (pres⇒step n {i = i} {α = α} {j = i′} st₁)
              (pres⇒step n {i = i} {α = α} {j = i″} st₂))
      ; step-sort-deterministic =
          λ {i} {i′} {i″} {α} {I} {S} {T = T₀} {i = c} st₁ st₂ →
            WN.step-sort-deterministic
              (pres⇒step n {i = i} {j = i′} st₁)
              (pres⇒step n {i = i} {j = i″} st₂)
      ; step-arity-deterministic =
          λ {i} {i′} {i″} {α} {I} {J} {S} {T = T₀} {i = c} {j = c′} st₁ st₂ →
            WN.step-arity-deterministic
              (pres⇒step n {i = i} {j = i′} st₁)
              (pres⇒step n {i = i} {j = i″} st₂)
      ; step-is-prop = λ {i} {β} {i′} st₁ st₂ →
          step-is-prop {G = PG} {s = i} {α = β} {t = i′} st₁ st₂
      ; no-new-branch/step =
          λ {i} {i′} {iᵢ} {iⱼ′} {β} {γ} {cᵢ} {cⱼ} st r∉ stᵢ stⱼ′ →
            let tⱼ , stⱼ =
                  WN.no-new-branch/step
                    (pres⇒step n {i = i} {α = β} {j = i′} st)
                    r∉
                    (pres⇒step n {i = i} {j = iᵢ} stᵢ)
                    (pres⇒step n {i = i′} {j = iⱼ′} stⱼ′)
            in nix n tⱼ , stepNG' {i = i} {t = tⱼ} stⱼ
      ; no-new-comm/step = λ {i} {i′} {iγ} {β} {γ} st s∉ r∉ stγ →
          let tγ , stγ′ =
                WN.no-new-comm/step
                  (pres⇒step n {i = i} {α = β} {j = i′} st)
                  s∉ r∉
                  (pres⇒step n {i = i′} {α = γ} {j = iγ} stγ)
          in nix n tγ , stepNG' {i = i} {α = γ} {t = tγ} stγ′
      ; stepback/~ = λ {α} {i₀} {i₁} {i₁′} rel st →
          let s₀′ , relN , stN′ =
                WN.stepback/~
                  (~G→N {i = i₁} {j = i₁′} rel)
                  (pres⇒step n {i = i₀} {α = α} {j = i₁} st)
          in nix n s₀′
           , ~N→G/eq {s = nst n i₀} {t = s₀′} (nix-nst n i₀) refl relN
           , subst (λ z → GStep {PG} (nix n s₀′) α z) (nix-nst n i₁′)
               (step⇒pres n {s = s₀′} {α = α} {t = nst n i₁′} stN′)
      ; step-diamond = λ {i} {α} {i₁} {α′} {i₂} st₁ st₂ ind →
          let v , stA , stB =
                WN.step-diamond
                  (pres⇒step n {i = i} {α = α} {j = i₁} st₁)
                  (pres⇒step n {i = i} {α = α′} {j = i₂} st₂)
                  ind
          in nix n v
           , stepNG' {i = i₁} {α = α′} {t = v} stA
           , stepNG' {i = i₂} {α = α} {t = v} stB
      }
      where module WN = WellBehaved W
