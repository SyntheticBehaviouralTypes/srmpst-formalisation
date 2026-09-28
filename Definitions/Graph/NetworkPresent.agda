{-# OPTIONS --guardedness #-}

-- Transport of well-behavedness across a network's finite presentation.
--
-- `Definitions/Graph/Network.agda` gives every net `n` a graph presentation `present n`
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
-- Both step relations are records (`GStep`, `NStep`), so their endpoints
-- are inferred from a step's type.  What still has to be pinned is a state
-- that appears only under `nix`/`nst` (non-injective), as in `stepGN'`'s
-- type and the `~` transports.

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Definitions.Behav using (BTheory; WellBehaved; Synchronous)

module Definitions.Graph.NetworkPresent (N : ℕ) where

  open import Definitions.Actions N
  open import Definitions.Graph.Core N
    using (Graph; State; graphTheory)
    renaming (_-<_>->_ to GStep)
  open import Definitions.Graph.Algebra N using (RootedGraph; underlying; initial)
  open import Definitions.Graph.WellBehaved N using (Stepback)
  open import Definitions.Graph.Network N

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
        subst (λ z → NStep n z α (nst n j)) (nst-nix n s) (pres⇒step n st)

      stepNG' :
        ∀ {i α t}
        → NStep n (nst n i) α t
        → GStep {PG} i α (nix n t)
      stepNG' {i} {α} {t} st =
        subst (λ z → GStep {PG} z α (nix n t)) (nix-nst n i) (step⇒pres n st)

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
        let u , stU , rel = TN._≲_.simulate sim (stepGN' {s = s} gr)
        in nix n u , step⇒pres n stU , ~N→G/eq (nix-nst n j₁) refl rel

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
        let j′ , grJ , rel = TG._≲_.simulate sim (stepNG' {i = i} stN)
        in nst n j′ , pres⇒step n grJ , ~G→N/eq (nst-nix n u) refl rel

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
      { recv-overlap = λ st₁ st₂ →
          WG.recv-overlap (step⇒pres n st₁) (step⇒pres n st₂)
      ; step-deterministic = λ st₁ st₂ →
          nix-inj (WG.step-deterministic (step⇒pres n st₁) (step⇒pres n st₂))
      ; step-sort-det = λ st₁ st₂ →
          WG.step-sort-det (step⇒pres n st₁) (step⇒pres n st₂)
      ; step-arity-det = λ st₁ st₂ →
          WG.step-arity-det (step⇒pres n st₁) (step⇒pres n st₂)
      ; no-new-branch/step = λ {G} st idle stᵢ stⱼ′ ceq →
          let Gⱼ , grⱼ =
                WG.no-new-branch/step (step⇒pres n st) idle
                  (step⇒pres n stᵢ) (step⇒pres n stⱼ′) ceq
          in nst n Gⱼ , stepGN' {s = G} grⱼ
      ; stepback/~ = λ {α} {G₀} {G₁} {G₁′} rel st →
          let i₀′ , relG , gr′ =
                WG.stepback/~ (~N→G {s = G₁} {t = G₁′} rel) (step⇒pres n st)
          in nst n i₀′
           , ~G→N/eq {i = nix n G₀} {j = i₀′} (nst-nix n G₀) refl relG
           , subst (NStep n (nst n i₀′) α) (nst-nix n G₁′) (pres⇒step n gr′)
      ; step-diamond = λ {G} {α} {G₁} {α′} {G₂} st₁ st₂ ind →
          let k , gr₁ , gr₂ =
                WG.step-diamond (step⇒pres n st₁) (step⇒pres n st₂) ind
          in nst n k , stepGN' {s = G₁} gr₁ , stepGN' {s = G₂} gr₂
      }
      where module WG = WellBehaved W

    -- A `Stepback` property *decided* on the presentation (via
    -- `finiteStepback?`/`stepback/sound`) becomes the `stepback/~` axiom of
    -- the network theory.  This is the global ingredient of the sequential-
    -- composition theorem (`Definitions/Graph/NetworkSeq.agda`): all other axioms of `⨾`
    -- compose locally, and this transport carries the one that cannot.
    stepbackG→N :
      Stepback PG
      → ∀ {α s t t′}
      → BTheory._~_ (netTheory n) t t′
      → NStep n s α t
      → Σ[ s′ ∈ NState n ]
          BTheory._~_ (netTheory n) s s′ × NStep n s′ α t′
    stepbackG→N sbG {α} {s} {t} {t′} rel st =
      let i₀′ , relG , gr′ = sbG (~N→G {s = t} {t = t′} rel) (step⇒pres n st)
      in nst n i₀′
       , ~G→N/eq {i = nix n s} {j = i₀′} (nst-nix n s) refl relG
       , subst (NStep n (nst n i₀′) α) (nst-nix n t′) (pres⇒step n gr′)

    net→pres :
      WellBehaved (netTheory n)
      → WellBehaved (graphTheory PG)
    net→pres W = record
      { recv-overlap = λ st₁ st₂ →
          WN.recv-overlap (pres⇒step n st₁) (pres⇒step n st₂)
      ; step-deterministic = λ st₁ st₂ →
          nst-inj (WN.step-deterministic (pres⇒step n st₁) (pres⇒step n st₂))
      ; step-sort-det = λ st₁ st₂ →
          WN.step-sort-det (pres⇒step n st₁) (pres⇒step n st₂)
      ; step-arity-det = λ st₁ st₂ →
          WN.step-arity-det (pres⇒step n st₁) (pres⇒step n st₂)
      ; no-new-branch/step = λ {i} st idle stᵢ stⱼ′ ceq →
          let tⱼ , stⱼ =
                WN.no-new-branch/step (pres⇒step n st) idle
                  (pres⇒step n stᵢ) (pres⇒step n stⱼ′) ceq
          in nix n tⱼ , stepNG' {i = i} stⱼ
      ; stepback/~ = λ {α} {i₀} {i₁} {i₁′} rel st →
          let s₀′ , relN , stN′ =
                WN.stepback/~ (~G→N {i = i₁} {j = i₁′} rel) (pres⇒step n st)
          in nix n s₀′
           , ~N→G/eq {s = nst n i₀} {t = s₀′} (nix-nst n i₀) refl relN
           , subst (λ z → GStep {PG} (nix n s₀′) α z) (nix-nst n i₁′)
               (step⇒pres n stN′)
      ; step-diamond = λ {i} {α} {i₁} {α′} {i₂} st₁ st₂ ind →
          let v , stA , stB =
                WN.step-diamond (pres⇒step n st₁) (pres⇒step n st₂) ind
          in nix n v , stepNG' {i = i₁} stA , stepNG' {i = i₂} stB
      }
      where module WN = WellBehaved W

    -- `Synchronous`, both ways.  `balanced` returns the action unchanged,
    -- so only the step is transported.
    pres→netSync :
      Synchronous (graphTheory PG)
      → Synchronous (netTheory n)
    pres→netSync S = record
      { balanced = λ st → SG.balanced (step⇒pres n st)
      ; no-new-comm/step = λ {G} st idle stγ →
          let Gγ′ , grγ =
                SG.no-new-comm/step (step⇒pres n st) idle (step⇒pres n stγ)
          in nst n Gγ′ , stepGN' {s = G} grγ
      }
      where module SG = Synchronous S

    net→presSync :
      Synchronous (netTheory n)
      → Synchronous (graphTheory PG)
    net→presSync S = record
      { balanced = λ st → SN.balanced (pres⇒step n st)
      ; no-new-comm/step = λ {i} st idle stγ →
          let tγ , stγ′ =
                SN.no-new-comm/step (pres⇒step n st) idle (pres⇒step n stγ)
          in nix n tγ , stepNG' {i = i} stγ′
      }
      where module SN = Synchronous S
