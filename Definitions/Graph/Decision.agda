{-# OPTIONS --guardedness #-}

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open All using (All)
import Data.List.Relation.Unary.AllPairs as Pairs
open Pairs using (AllPairs)
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (map′)

module Definitions.Graph.Decision (N : ℕ) where

  open import Definitions.Actions N
  open import Definitions.Behav using (WellBehaved; Synchronous)
  open import Definitions.Graph.Bisimulation N
  open import Definitions.Graph.Core N
  open import Definitions.Graph.WellBehaved N

  allPairs/tabulate :
    ∀ {A : Set}
      {_R_ : A → A → Set}
      {xs : List A}
    → (∀ {x y} → x ∈ xs → y ∈ xs → x R y)
    → AllPairs _R_ xs
  allPairs/tabulate {xs = []} related =
    Pairs.[]
  allPairs/tabulate {xs = x ∷ xs} related =
    All.tabulate
      (λ y∈ → related (Any.here refl) (Any.there y∈))
      Pairs.∷
    allPairs/tabulate
      (λ x∈ y∈ → related (Any.there x∈) (Any.there y∈))

  listed⇒available :
    ∀ {n α t}
      {xs : List (Edge n)}
    → (α , t) ∈ xs
    → Available α xs
  listed⇒available (Any.here refl) =
    Any.here refl
  listed⇒available (Any.there member) =
    Any.there (listed⇒available member)

  deterministic/complete :
    ∀ {G}
    → BisimulationCorrect G
    → WellBehaved (graphTheory G)
    → ∀ s → AllPairs (SameTarget G) (edges G s)
  deterministic/complete {G} correct well-behaved s =
    allPairs/tabulate deterministic-pair
    where
      deterministic-pair :
        ∀ {α α′ t t′}
        → (α , t) ∈ edges G s
        → (α′ , t′) ∈ edges G s
        → SameTarget G (α , t) (α′ , t′)
      deterministic-pair left right refl =
        complete correct
          (WellBehaved.step-deterministic well-behaved
            (listed⇒step left)
            (listed⇒step right))

  -- Every pair of steps out of `s` satisfies `R` (both ways round), given
  -- that every pair of STEPS does.
  pairs/complete :
    ∀ {G}{R : Edge (size G) → Edge (size G) → Set} s
    → (∀ {α α′ t t′} → _-<_>->_ {G} s α t → _-<_>->_ {G} s α′ t′
       → R (α , t) (α′ , t′))
    → AllPairs (Both R) (edges G s)
  pairs/complete {G} s r =
    allPairs/tabulate λ left right →
      r (listed⇒step left) (listed⇒step right)
      , r (listed⇒step right) (listed⇒step left)

  recv/complete :
    ∀ {G}
    → WellBehaved (graphTheory G)
    → ∀ s → AllPairs (Both RecvCoherent) (edges G s)
  recv/complete {G} well-behaved s =
    pairs/complete {G = G} s λ gr gr′ Q rQ inc →
      WellBehaved.recv-overlap well-behaved {Q = Q} gr gr′ rQ inc

  -- `AgreeOn F` for two steps out of `s`, from `F` on each pair of
  -- same-sender receives.
  agreeOn/complete :
    ∀ {G}{F : Choice → Choice → Set} s
    → (∀ {α α′ t t′ Q P} c c′
       → _-<_>->_ {G} s α t → _-<_>->_ {G} s α′ t′
       → ev α Q ≡ just ((？ P) # c) → ev α′ Q ≡ just ((？ P) # c′)
       → F c c′)
    → AllPairs (Both (SameOn F)) (edges G s)
  agreeOn/complete {G} {F} s f = pairs/complete {G = G} s agree
    where
      agree :
        ∀ {α α′ t t′}
        → _-<_>->_ {G} s α t
        → _-<_>->_ {G} s α′ t′
        → ∀ Q → AgreeOn F (ev α Q) (ev α′ Q)
      agree {α} {α′} gr gr′ Q with ev α Q in eq | ev α′ Q in eq′
      ... | just ((？ _) # c) | just ((？ _) # c′) =
        λ { refl → f c c′ gr gr′ eq eq′ }
      ... | nothing            | _                  = tt
      ... | just ((! _) # _)   | _                  = tt
      ... | just ((？ _) # _)   | nothing            = tt
      ... | just ((？ _) # _)   | just ((! _) # _)   = tt

  arity/complete :
    ∀ {G}
    → WellBehaved (graphTheory G)
    → ∀ s → AllPairs (Both SameArity) (edges G s)
  arity/complete {G} well-behaved s =
    agreeOn/complete {G = G} s λ { (_ < _ >) (_ < _ >) gr gr′ eq eq′ →
      WellBehaved.step-arity-det well-behaved gr gr′ eq eq′ }

  sort/complete :
    ∀ {G}
    → WellBehaved (graphTheory G)
    → ∀ s → AllPairs (Both SameSort) (edges G s)
  sort/complete {G} well-behaved s =
    agreeOn/complete {G = G} s λ { (_ < _ >) (_ < _ >) gr gr′ eq eq′ refl →
      WellBehaved.step-sort-det well-behaved gr gr′ eq eq′ }

  noNewBranch/complete :
    ∀ {G}
    → WellBehaved (graphTheory G)
    → ∀ s → All (NoNewBranchAfter G s) (edges G s)
  noNewBranch/complete {G} well-behaved s =
    All.tabulate no-new-edge
    where
      no-new-target :
        ∀ {β t γ γ′ u v}
        → (β , t) ∈ edges G s
        → (γ , u) ∈ edges G s
        → (∀ Q → Recv γ Q → Q ∉α β)
        → (γ′ , v) ∈ edges G t
        → comm γ′ ≡ comm γ
        → Available γ′ (edges G s)
      no-new-target β∈ source∈ idle target∈ ceq =
        let _ , grⱼ =
              WellBehaved.no-new-branch/step well-behaved
                (listed⇒step β∈)
                idle
                (listed⇒step source∈)
                (listed⇒step target∈)
                ceq
        in listed⇒available (step⇒listed grⱼ)

      no-new-source :
        ∀ {β t γ u}
        → (β , t) ∈ edges G s
        → (γ , u) ∈ edges G s
        → (∀ Q → Recv γ Q → Q ∉α β)
        → All
            (λ where
              (α′ , _) →
                comm α′ ≡ comm γ
                  → Available α′ (edges G s))
            (edges G t)
      no-new-source β∈ source∈ idle =
        All.tabulate
          (no-new-target β∈ source∈ idle)

      no-new-edge :
        ∀ {β t}
        → (β , t) ∈ edges G s
        → NoNewBranchAfter G s (β , t)
      no-new-edge β∈ =
        All.tabulate (no-new-source β∈)

  diamond/complete :
    ∀ {G}
    → BisimulationCorrect G
    → WellBehaved (graphTheory G)
    → ∀ s → AllPairs (Both (Commutes G)) (edges G s)
  diamond/complete {G} correct well-behaved s =
    pairs/complete {G = G} s λ grα grβ independent →
      let _ , _ , grv , grw , vw =
            WellBehaved.step-diamond well-behaved grα grβ independent
      in completion/complete grv grw (complete correct vw)

  localConditions/complete :
    ∀ {G}
    → BisimulationCorrect G
    → WellBehaved (graphTheory G)
    → LocalConditions G
  localConditions/complete {G} correct well-behaved =
    record
      { deterministic = deterministic/complete {G = G} correct well-behaved
      ; recv-coherent = recv/complete {G = G} well-behaved
      ; same-arity = arity/complete {G = G} well-behaved
      ; same-sort = sort/complete {G = G} well-behaved
      ; no-new-branch = noNewBranch/complete {G = G} well-behaved
      ; diamond = diamond/complete {G = G} correct well-behaved
      }

  -- `map′`, not `with`: a `with` forces the sub-decisions' proofs even when
  -- only `⌊_⌋` is inspected.
  wellBehavedWith? :
    (G : Graph)
    → BisimulationCorrect G
    → Dec (WellBehaved (graphTheory G))
  wellBehavedWith? G correct =
    map′
      (wellBehaved G correct)
      (localConditions/complete correct)
      (localConditions? G)

  wellBehaved? :
    (G : Graph) → Dec (WellBehaved (graphTheory G))
  wellBehaved? G =
    wellBehavedWith? G (bisimulationCorrect G)

  -- ══════════════════════════════════════════════════════════════════
  --  The synchronous instance
  -- ══════════════════════════════════════════════════════════════════

  balanced/complete :
    ∀ {G}
    → Synchronous (graphTheory G)
    → ∀ s → All BalancedEdge (edges G s)
  balanced/complete {G} sync s =
    All.tabulate λ member →
      Synchronous.balanced sync (listed⇒step member)

  noNewComm/complete :
    ∀ {G}
    → Synchronous (graphTheory G)
    → ∀ s → All (NoNewAfter G s) (edges G s)
  noNewComm/complete {G} sync s =
    All.tabulate no-new-edge
    where
      no-new-target :
        ∀ {β t γ u}
        → (β , t) ∈ edges G s
        → (γ , u) ∈ edges G t
        → (∀ X → X ∈α γ → X ∉α β)
        → Available γ (edges G s)
      no-new-target β∈ γ∈ idle =
        let _ , grγ =
              Synchronous.no-new-comm/step sync
                (listed⇒step β∈)
                idle
                (listed⇒step γ∈)
        in listed⇒available (step⇒listed grγ)

      no-new-edge :
        ∀ {β t}
        → (β , t) ∈ edges G s
        → NoNewAfter G s (β , t)
      no-new-edge β∈ =
        All.tabulate (no-new-target β∈)

  syncConditions/complete :
    ∀ {G}
    → Synchronous (graphTheory G)
    → SyncConditions G
  syncConditions/complete {G} sync =
    record
      { balanced = balanced/complete {G = G} sync
      ; no-new-comm = noNewComm/complete {G = G} sync
      }

  synchronous? :
    (G : Graph) → Dec (Synchronous (graphTheory G))
  synchronous? G =
    map′ (synchronous G) (syncConditions/complete {G = G}) (syncConditions? G)
