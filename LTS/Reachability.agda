{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)

module LTS.Reachability (N : ℕ) where

  open import Definitions.Actions N using (Action)
  open import LTS.Core N

  data ReachableBy
    {G : Graph}
    (Allow : Action → Set)
    (s : State G)
    : State G → Set
    where

    reachable/refl :
      ReachableBy Allow s s

    reachable/step :
      ∀ {α u t}
      → _-<_>->_ {G} s α u
      → Allow α
      → ReachableBy {G} Allow u t
      → ReachableBy Allow s t

  Reachable : {G : Graph} → State G → State G → Set
  Reachable {G} = ReachableBy {G} (λ _ → ⊤)

  reachable/map :
    ∀ {G s t}
      {Allow Allow′ : Action → Set}
    → (∀ {α} → Allow α → Allow′ α)
    → ReachableBy {G} Allow s t
    → ReachableBy {G} Allow′ s t
  reachable/map inclusion reachable/refl =
    reachable/refl
  reachable/map inclusion (reachable/step gr allowed path) =
    reachable/step gr (inclusion allowed)
      (reachable/map {G = _} inclusion path)

  reachable/cat :
    ∀ {G s u t Allow}
    → ReachableBy {G} Allow s u
    → ReachableBy {G} Allow u t
    → ReachableBy {G} Allow s t
  reachable/cat reachable/refl right =
    right
  reachable/cat (reachable/step gr allowed left) right =
    reachable/step gr allowed (reachable/cat {G = _} left right)

  -- TODO: Compute the least fixed point of one-step expansion as a
  -- `Vec Bool (size G)`. Prove that matrix membership is equivalent to
  -- `ReachableBy`. The proof should use the number of unvisited states as
  -- fuel, not the length of arbitrary paths.
