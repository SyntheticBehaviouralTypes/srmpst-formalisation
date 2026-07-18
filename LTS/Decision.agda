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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable
  using (T?; _×-dec_; _→-dec_; map′)

module LTS.Decision (N : ℕ) where

  open import Definitions.Actions N
  open import Definitions.Behav using (WellBehaved)
  open import LTS.Bisimulation N
  open import LTS.Core N
  open import LTS.WellBehaved N

  StepbackAt :
    (G : Graph) → State G → Edge (size G) → State G → Set
  StepbackAt G s (α , t) t′ =
    Bisimilar G t t′
      → Σ[ s′ ∈ State G ]
          Bisimilar G s s′ × _-<_>->_ {G} s′ α t′

  stepbackAt? :
    (G : Graph) (s : State G)
    (edge : Edge (size G)) (t′ : State G)
    → Dec (StepbackAt G s edge t′)
  stepbackAt? G s (α , t) t′ =
    T? (bisim? G t t′) →-dec
      Fin.any? λ s′ →
        T? (bisim? G s s′) ×-dec step? G s′ α t′

  FiniteStepback : Graph → Set
  FiniteStepback G =
    ∀ s
    → All
        (λ edge → ∀ t′ → StepbackAt G s edge t′)
        (edges G s)

  -- `finiteStepback?` queries `bisim?` O(size² · edges) times, and every
  -- `bisim?` application re-runs the whole `approximation` fixed point (the
  -- evaluator shares argument thunks, never definition applications) — this
  -- dominated `wellBehaved?` on medium graphs.  As with `SkipDecide.semSkip?`
  -- (Definitions/TypeChecker/Core.agda), the matrix is computed once and
  -- passed as a *bound argument*, so every query is a lookup into the one
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
          All.lookup finiteStep (step⇒listed {G = G} gr)
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

  proper/complete :
    ∀ {G}
    → WellBehaved (graphTheory G)
    → ∀ s → All Proper (edges G s)
  proper/complete {G} well-behaved s =
    All.tabulate λ member →
      WellBehaved.sender≢receiver well-behaved
        (listed⇒step {G = G} member)

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
          (listed⇒step {G = G} left)
          (listed⇒step {G = G} right)

  recv/complete :
    ∀ {G}
    → WellBehaved (graphTheory G)
    → ∀ s → AllPairs BothRecvCoherent (edges G s)
  recv/complete {G} well-behaved s =
    allPairs/tabulate recv-pair
    where
      recv-pair :
        ∀ {α α′ t t′}
        → (α , t) ∈ edges G s
        → (α′ , t′) ∈ edges G s
        → BothRecvCoherent (α , t) (α′ , t′)
      recv-pair left right =
        WellBehaved.recv-overlap⇒same-comm well-behaved gr gr′
        , WellBehaved.recv-overlap⇒same-comm well-behaved gr′ gr
        where
          gr = listed⇒step {G = G} left
          gr′ = listed⇒step {G = G} right

  arity/complete :
    ∀ {G}
    → WellBehaved (graphTheory G)
    → ∀ s → AllPairs BothSameArity (edges G s)
  arity/complete {G} well-behaved s =
    allPairs/tabulate arity-pair
    where
      arity-pair :
        ∀ {γ γ′ I J S T t t′}
          {i : Fin (suc I)}
          {j : Fin (suc J)}
        → ((γ # (i < S >)) , t) ∈ edges G s
        → ((γ′ # (j < T >)) , t′) ∈ edges G s
        → BothSameArity
            ((γ # (i < S >)) , t)
            ((γ′ # (j < T >)) , t′)
      arity-pair left right =
        (λ { refl →
          WellBehaved.step-arity-deterministic well-behaved gr gr′ })
        , (λ { refl →
          WellBehaved.step-arity-deterministic well-behaved gr′ gr })
        where
          gr = listed⇒step {G = G} left
          gr′ = listed⇒step {G = G} right

  sort/complete :
    ∀ {G}
    → WellBehaved (graphTheory G)
    → ∀ s → AllPairs BothSameSort (edges G s)
  sort/complete {G} well-behaved s =
    allPairs/tabulate sort-pair
    where
      sort-pair :
        ∀ {γ γ′ I J S T t t′}
          {i : Fin (suc I)}
          {j : Fin (suc J)}
        → ((γ # (i < S >)) , t) ∈ edges G s
        → ((γ′ # (j < T >)) , t′) ∈ edges G s
        → BothSameSort
            ((γ # (i < S >)) , t)
            ((γ′ # (j < T >)) , t′)
      sort-pair left right =
        (λ { refl refl →
          WellBehaved.step-sort-deterministic well-behaved gr gr′ })
        , (λ { refl refl →
          WellBehaved.step-sort-deterministic well-behaved gr′ gr })
        where
          gr = listed⇒step {G = G} left
          gr′ = listed⇒step {G = G} right

  noNewComm/complete :
    ∀ {G}
    → WellBehaved (graphTheory G)
    → ∀ s → All (NoNewAfter G s) (edges G s)
  noNewComm/complete {G} well-behaved s =
    All.tabulate no-new-edge
    where
      no-new-target :
        ∀ {β t γ u}
        → (β , t) ∈ edges G s
        → (γ , u) ∈ edges G t
        → sender γ ∉α β × receiver γ ∉α β
        → Available γ (edges G s)
      no-new-target β∈ γ∈ (sender∉ , receiver∉) =
        let _ , grγ =
              WellBehaved.no-new-comm/step well-behaved
                (listed⇒step {G = G} β∈)
                sender∉
                receiver∉
                (listed⇒step {G = G} γ∈)
        in listed⇒available (step⇒listed {G = G} grγ)

      no-new-edge :
        ∀ {β t}
        → (β , t) ∈ edges G s
        → NoNewAfter G s (β , t)
      no-new-edge β∈ =
        All.tabulate (no-new-target β∈)

  noNewBranch/complete :
    ∀ {G}
    → WellBehaved (graphTheory G)
    → ∀ s → All (NoNewBranchAfter G s) (edges G s)
  noNewBranch/complete {G} well-behaved s =
    All.tabulate no-new-edge
    where
      no-new-target :
        ∀ {β t γ γ′ cᵢ cⱼ u v}
        → (β , t) ∈ edges G s
        → ((γ # cᵢ) , u) ∈ edges G s
        → Comm.receiver γ ∉α β
        → ((γ′ # cⱼ) , v) ∈ edges G t
        → γ ≡ γ′
        → Available (γ′ # cⱼ) (edges G s)
      no-new-target β∈ source∈ receiver∉ target∈ refl =
        let _ , grⱼ =
              WellBehaved.no-new-branch/step well-behaved
                (listed⇒step {G = G} β∈)
                receiver∉
                (listed⇒step {G = G} source∈)
                (listed⇒step {G = G} target∈)
        in listed⇒available (step⇒listed {G = G} grⱼ)

      no-new-source :
        ∀ {β t γ cᵢ u}
        → (β , t) ∈ edges G s
        → ((γ # cᵢ) , u) ∈ edges G s
        → Comm.receiver γ ∉α β
        → All
            (λ where
              (α′ , _) →
                γ ≡ Action.comm α′
                  → Available α′ (edges G s))
            (edges G t)
      no-new-source β∈ source∈ receiver∉ =
        All.tabulate
          (no-new-target β∈ source∈ receiver∉)

      no-new-edge :
        ∀ {β t}
        → (β , t) ∈ edges G s
        → NoNewBranchAfter G s (β , t)
      no-new-edge β∈ =
        All.tabulate (no-new-source β∈)

  diamond/complete :
    ∀ {G}
    → WellBehaved (graphTheory G)
    → ∀ s → AllPairs (BothCommute G) (edges G s)
  diamond/complete {G} well-behaved s =
    allPairs/tabulate diamond-pair
    where
      diamond-pair :
        ∀ {α β t u}
        → (α , t) ∈ edges G s
        → (β , u) ∈ edges G s
        → BothCommute G (α , t) (β , u)
      diamond-pair α∈ β∈ =
        WellBehaved.step-diamond well-behaved grα grβ
        , WellBehaved.step-diamond well-behaved grβ grα
        where
          grα = listed⇒step {G = G} α∈
          grβ = listed⇒step {G = G} β∈

  localConditions/complete :
    ∀ {G}
    → WellBehaved (graphTheory G)
    → LocalConditions G
  localConditions/complete {G} well-behaved =
    record
      { proper = proper/complete {G = G} well-behaved
      ; deterministic = deterministic/complete {G = G} well-behaved
      ; recv-coherent = recv/complete {G = G} well-behaved
      ; same-arity = arity/complete {G = G} well-behaved
      ; same-sort = sort/complete {G = G} well-behaved
      ; no-new-comm = noNewComm/complete {G = G} well-behaved
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
              (listed⇒step {G = G} member)
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
