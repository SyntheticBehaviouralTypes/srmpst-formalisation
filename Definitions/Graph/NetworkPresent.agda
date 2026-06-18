{-# OPTIONS --guardedness #-}

-- Bisimilarity (`~N→G`/`~G→N`), `WellBehaved` and `Synchronous`, moved
-- between a net and its presentation `present n`.  States under the
-- non-injective `nix`/`nst` must be pinned.

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)

open import Definitions.Behav using (BTheory; WellBehaved; Synchronous)

module Definitions.Graph.NetworkPresent (N : ℕ) where

  open import Definitions.Actions N
  open import Definitions.Graph.Core N
    using (Graph; graphTheory)
    renaming (_-<_>->_ to GStep)
  open import Definitions.Graph.Algebra N using (underlying)
  open import Definitions.Graph.Network N

  module _ (n : Net) where

    private
      PG : Graph
      PG = underlying (present n)

      module TN = BTheory (netTheory n)
      module TG = BTheory (graphTheory PG)

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
    -- Index equations are arguments matched as `refl`; a `subst` around the
    -- corecursive call would break guardedness.

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
      ; step-deterministic = λ {_} {_} {t₁} {t₂} st₁ st₂ →
          ~G→N/eq {i = nix n t₁} {j = nix n t₂} (nst-nix n t₁) (nst-nix n t₂)
            (WG.step-deterministic (step⇒pres n st₁) (step⇒pres n st₂))
      ; step-sort-det = λ st₁ st₂ →
          WG.step-sort-det (step⇒pres n st₁) (step⇒pres n st₂)
      ; step-arity-det = λ st₁ st₂ →
          WG.step-arity-det (step⇒pres n st₁) (step⇒pres n st₂)
      ; no-new-branch/step = λ {G} st idle stᵢ stⱼ′ ceq →
          let Gⱼ , grⱼ =
                WG.no-new-branch/step (step⇒pres n st) idle
                  (step⇒pres n stᵢ) (step⇒pres n stⱼ′) ceq
          in nst n Gⱼ , stepGN' {s = G} grⱼ
      ; step-diamond = λ {G} {α} {G₁} {α′} {G₂} st₁ st₂ ind →
          let k₁ , k₂ , gr₁ , gr₂ , rel =
                WG.step-diamond (step⇒pres n st₁) (step⇒pres n st₂) ind
          in nst n k₁ , nst n k₂ , stepGN' {s = G₁} gr₁ , stepGN' {s = G₂} gr₂
           , ~G→N {i = k₁} {j = k₂} rel
      }
      where module WG = WellBehaved W

    net→pres :
      WellBehaved (netTheory n)
      → WellBehaved (graphTheory PG)
    net→pres W = record
      { recv-overlap = λ st₁ st₂ →
          WN.recv-overlap (pres⇒step n st₁) (pres⇒step n st₂)
      ; step-deterministic = λ {_} {_} {i₁} {i₂} st₁ st₂ →
          ~N→G/eq {s = nst n i₁} {t = nst n i₂} (nix-nst n i₁) (nix-nst n i₂)
            (WN.step-deterministic (pres⇒step n st₁) (pres⇒step n st₂))
      ; step-sort-det = λ st₁ st₂ →
          WN.step-sort-det (pres⇒step n st₁) (pres⇒step n st₂)
      ; step-arity-det = λ st₁ st₂ →
          WN.step-arity-det (pres⇒step n st₁) (pres⇒step n st₂)
      ; no-new-branch/step = λ {i} st idle stᵢ stⱼ′ ceq →
          let tⱼ , stⱼ =
                WN.no-new-branch/step (pres⇒step n st) idle
                  (pres⇒step n stᵢ) (pres⇒step n stⱼ′) ceq
          in nix n tⱼ , stepNG' {i = i} stⱼ
      ; step-diamond = λ {i} {α} {i₁} {α′} {i₂} st₁ st₂ ind →
          let v , w , stA , stB , rel =
                WN.step-diamond (pres⇒step n st₁) (pres⇒step n st₂) ind
          in nix n v , nix n w , stepNG' {i = i₁} stA , stepNG' {i = i₂} stB
           , ~N→G {s = v} {t = w} rel
      }
      where module WN = WellBehaved W

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
