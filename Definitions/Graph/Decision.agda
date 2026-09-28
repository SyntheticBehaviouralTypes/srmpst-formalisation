{-# OPTIONS --guardedness #-}

open import Data.Fin using (Fin)
import Data.Fin.Properties as Fin
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open All using (All)
import Data.List.Relation.Unary.AllPairs as Pairs
open Pairs using (AllPairs)
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Function using (_∘_)
open import Data.Bool using (T)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable
  using (T?; _×-dec_; _→-dec_; map′)

module Definitions.Graph.Decision (N : ℕ) where

  open import Definitions.Actions N
  open import Definitions.Behav using (WellBehaved; Synchronous)
  open import Definitions.Graph.Bisimulation N
  open import Definitions.Graph.Core N
  open import Definitions.Graph.WellBehaved N

  StepbackAt :
    (G : Graph) → State G → Edge (size G) → State G → Set
  StepbackAt G s (α , t) t′ =
    Bisimilar G t t′
      → Σ[ s′ ∈ State G ]
          Bisimilar G s s′ × _-<_>->_ {G} s′ α t′

  FiniteStepback : Graph → Set
  FiniteStepback G =
    ∀ s
    → All
        (λ edge → ∀ t′ → StepbackAt G s edge t′)
        (edges G s)

  -- `finiteStepback?` queries `bisim?` O(size² · edges) times, and every
  -- `bisim?` application re-runs the whole `approximation` fixed point (the
  -- evaluator shares argument thunks, never definition applications) — this
  -- dominated `wellBehaved?` on medium graphs.  So the matrix is computed
  -- once and passed as a *bound argument*, so every query is a lookup into the one
  -- shared thunk; the pointwise equation (instantiated with `refl`, since
  -- `bisim? G = related G (approximation G)` definitionally) transports each
  -- decision back to the `Bisimilar`-phrased proposition.
  finiteStepback? : (G : Graph) → Dec (FiniteStepback G)
  finiteStepback? G =
    go (approximation G) (λ _ _ → refl)
    where
    go :
      (mat : Matrix G)
      → (∀ s t → related G mat s t ≡ bisim? G s t)
      → Dec (FiniteStepback G)
    go mat eqv =
      Fin.all? λ s →
        All.all?
          (λ edge → Fin.all? (stepbackAt′ s edge))
          (edges G s)
      where
        bisimT? : ∀ s t → Dec (Bisimilar G s t)
        bisimT? s t =
          subst (λ b → Dec (T b)) (eqv s t) (T? (related G mat s t))

        stepbackAt′ :
          (s : State G) (edge : Edge (size G)) (t′ : State G)
          → Dec (StepbackAt G s edge t′)
        stepbackAt′ s (α , t) t′ =
          bisimT? t t′ →-dec
            Fin.any? λ s′ →
              bisimT? s s′ ×-dec step? G s′ α t′

  stepback/sound :
    ∀ {G}
    → BisimulationCorrect G
    → FiniteStepback G
    → Stepback G
  stepback/sound {G} correct finite {s = s} equivalent gr =
    let at =
          All.lookup finiteStep (step⇒listed gr)
        s′ , s~s′ , gr′ =
          at _ (complete correct equivalent)
    in s′ , sound correct s~s′ , gr′
    where
      finiteStep = finite s

  record Conditions (G : Graph) : Set where
    field
      local    : LocalConditions G
      stepback : FiniteStepback G

  open Conditions

  -- `conditions?`/`wellBehavedWith?` are `map′`-based rather than `with`-
  -- based: a `with` on the sub-decisions forces their `proof` fields (the
  -- whole witness-construction pass) even when the caller only inspects
  -- `⌊_⌋` — e.g. discharging `buildG`'s `T ⌊ wellBehaved? … ⌋` obligation.
  -- With `map′` the `does` chain alone decides, and witnesses are built
  -- lazily, only if someone actually extracts the `WellBehaved` record.
  conditions? : (G : Graph) → Dec (Conditions G)
  conditions? G =
    map′
      (λ (local′ , stepback′) →
        record { local = local′ ; stepback = stepback′ })
      (λ conditions → local conditions , stepback conditions)
      (localConditions? G ×-dec finiteStepback? G)

  conditions/sound :
    ∀ {G}
    → BisimulationCorrect G
    → Conditions G
    → WellBehaved (graphTheory G)
  conditions/sound correct conditions =
    wellBehaved _
      (local conditions)
      (stepback/sound correct (stepback conditions))

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
    → WellBehaved (graphTheory G)
    → ∀ s → AllPairs SameTarget (edges G s)
  deterministic/complete {G} well-behaved s =
    allPairs/tabulate deterministic-pair
    where
      deterministic-pair :
        ∀ {α α′ t t′}
        → (α , t) ∈ edges G s
        → (α′ , t′) ∈ edges G s
        → SameTarget (α , t) (α′ , t′)
      deterministic-pair left right refl =
        WellBehaved.step-deterministic well-behaved
          (listed⇒step left)
          (listed⇒step right)

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
    → WellBehaved (graphTheory G)
    → ∀ s → AllPairs (Both (Commutes G)) (edges G s)
  diamond/complete {G} well-behaved s =
    pairs/complete {G = G} s (WellBehaved.step-diamond well-behaved)

  localConditions/complete :
    ∀ {G}
    → WellBehaved (graphTheory G)
    → LocalConditions G
  localConditions/complete {G} well-behaved =
    record
      { deterministic = deterministic/complete {G = G} well-behaved
      ; recv-coherent = recv/complete {G = G} well-behaved
      ; same-arity = arity/complete {G = G} well-behaved
      ; same-sort = sort/complete {G = G} well-behaved
      ; no-new-branch = noNewBranch/complete {G = G} well-behaved
      ; diamond = diamond/complete {G = G} well-behaved
      }

  finiteStepback/complete :
    ∀ {G}
    → BisimulationCorrect G
    → WellBehaved (graphTheory G)
    → FiniteStepback G
  finiteStepback/complete {G} correct well-behaved s =
    All.tabulate λ member t′ equivalent →
      let s′ , s~s′ , gr′ =
            WellBehaved.stepback/~ well-behaved
              (sound correct equivalent)
              (listed⇒step member)
      in s′ , complete correct s~s′ , gr′

  conditions/complete :
    ∀ {G}
    → BisimulationCorrect G
    → WellBehaved (graphTheory G)
    → Conditions G
  conditions/complete {G} correct well-behaved =
    record
      { local = localConditions/complete {G = G} well-behaved
      ; stepback =
          finiteStepback/complete {G = G} correct well-behaved
      }

  wellBehavedWith? :
    (G : Graph)
    → BisimulationCorrect G
    → Dec (WellBehaved (graphTheory G))
  wellBehavedWith? G correct =
    map′
      (conditions/sound correct)
      (conditions/complete correct)
      (conditions? G)

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
    → ∀ s → All Balanced (edges G s)
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

  -- `map′`-based for the same reason as `wellBehavedWith?`.
  synchronous? :
    (G : Graph) → Dec (Synchronous (graphTheory G))
  synchronous? G =
    map′ (synchronous G) (syncConditions/complete {G = G}) (syncConditions? G)
