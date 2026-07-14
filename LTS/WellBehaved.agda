{-# OPTIONS --guardedness #-}

open import Data.Fin using (Fin)
  renaming (_≟_ to _≟Fin_)
import Data.Fin.Properties as Fin
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open All using (All)
import Data.List.Relation.Unary.AllPairs as Pairs
open Pairs using (AllPairs)
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (ℕ; suc)
import Data.Nat.Properties as Nat
open import Data.Product
  using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym)
open import Relation.Nullary using (Dec; yes; no; ¬?)
open import Relation.Nullary.Decidable using (_×-dec_; _→-dec_)

open import Definitions.Behav using (BTheory; WellBehaved)

module LTS.WellBehaved (N : ℕ) where

  open import Definitions.Actions N
  open import LTS.Action N
  open import LTS.Core N

  private
    variable
      n : ℕ

  EdgeAction : Edge n → Action
  EdgeAction = proj₁

  EdgeTarget : Edge n → Fin n
  EdgeTarget = proj₂

  Proper : Edge n → Set
  Proper (α , _) = sender α ≢ receiver α

  proper? : (edge : Edge n) → Dec (Proper edge)
  proper? (α , _) = ¬? (sender α ≟Fin receiver α)

  SameTarget : Edge n → Edge n → Set
  SameTarget (α , t) (α′ , t′) = α ≡ α′ → t ≡ t′

  sameTarget? : (left right : Edge n) → Dec (SameTarget left right)
  sameTarget? (α , t) (α′ , t′) =
    (α ≟Action α′) →-dec (t ≟Fin t′)

  sameTarget/refl :
    ∀ {n} (edge : Edge n) → SameTarget edge edge
  sameTarget/refl _ refl = refl

  sameTarget/sym :
    ∀ {n} {left right : Edge n}
    → SameTarget left right
    → SameTarget right left
  sameTarget/sym same eq = sym (same (sym eq))

  RecvCoherent : Edge n → Edge n → Set
  RecvCoherent (α , _) (α′ , _) =
    receiver α ∈α α′ → Action.comm α ≡ Action.comm α′

  recvCoherent? :
    (left right : Edge n) → Dec (RecvCoherent left right)
  recvCoherent? (α , _) (α′ , _) =
    (_∈α?_ (receiver α) α′) →-dec
      (Action.comm α ≟Comm Action.comm α′)

  BothRecvCoherent : Edge n → Edge n → Set
  BothRecvCoherent left right =
    RecvCoherent left right × RecvCoherent right left

  bothRecvCoherent? :
    (left right : Edge n) → Dec (BothRecvCoherent left right)
  bothRecvCoherent? left right =
    recvCoherent? left right ×-dec recvCoherent? right left

  recvCoherent/refl :
    ∀ {n} (edge : Edge n) → BothRecvCoherent edge edge
  recvCoherent/refl _ = (λ _ → refl) , (λ _ → refl)

  recvCoherent/sym :
    ∀ {n} {left right : Edge n}
    → BothRecvCoherent left right
    → BothRecvCoherent right left
  recvCoherent/sym (left , right) = right , left

  SameArity : Edge n → Edge n → Set
  SameArity (α , _) (α′ , _) =
    Action.comm α ≡ Action.comm α′
      → nchoices α ≡ nchoices α′

  sameArity? : (left right : Edge n) → Dec (SameArity left right)
  sameArity? (α , _) (α′ , _) =
    (Action.comm α ≟Comm Action.comm α′) →-dec
      (nchoices α Nat.≟ nchoices α′)

  BothSameArity : Edge n → Edge n → Set
  BothSameArity left right =
    SameArity left right × SameArity right left

  bothSameArity? :
    (left right : Edge n) → Dec (BothSameArity left right)
  bothSameArity? left right =
    sameArity? left right ×-dec sameArity? right left

  sameArity/refl :
    ∀ {n} (edge : Edge n) → BothSameArity edge edge
  sameArity/refl _ = (λ _ → refl) , (λ _ → refl)

  sameArity/sym :
    ∀ {n} {left right : Edge n}
    → BothSameArity left right
    → BothSameArity right left
  sameArity/sym (left , right) = right , left

  SameSort : Edge n → Edge n → Set
  SameSort (α , _) (α′ , _) =
    Action.comm α ≡ Action.comm α′
      → choiceKey (Action.choice α) ≡ choiceKey (Action.choice α′)
      → sort α ≡ sort α′

  sameSort? : (left right : Edge n) → Dec (SameSort left right)
  sameSort? (α , _) (α′ , _) =
    (Action.comm α ≟Comm Action.comm α′) →-dec
      ((choiceKey (Action.choice α)
          ≟ChoiceKey choiceKey (Action.choice α′)) →-dec
        (sort α ≟Sort sort α′))

  BothSameSort : Edge n → Edge n → Set
  BothSameSort left right =
    SameSort left right × SameSort right left

  bothSameSort? :
    (left right : Edge n) → Dec (BothSameSort left right)
  bothSameSort? left right =
    sameSort? left right ×-dec sameSort? right left

  sameSort/refl :
    ∀ {n} (edge : Edge n) → BothSameSort edge edge
  sameSort/refl _ =
    (λ _ _ → refl) , (λ _ _ → refl)

  sameSort/sym :
    ∀ {n} {left right : Edge n}
    → BothSameSort left right
    → BothSameSort right left
  sameSort/sym (left , right) = right , left

  Available : ∀ {n} → Action → List (Edge n) → Set
  Available α = Any.Any (λ edge → EdgeAction edge ≡ α)

  available? :
    ∀ {n} (α : Action) (xs : List (Edge n)) → Dec (Available α xs)
  available? α =
    Any.any? λ where
      (β , _) → β ≟Action α

  available/target :
    ∀ {n α}
      {xs : List (Edge n)}
    → Available α xs
    → Σ[ t ∈ Fin n ] (α , t) ∈ xs
  available/target {xs = []} ()
  available/target {xs = (β , t) ∷ xs} (Any.here β≡α)
    rewrite β≡α =
    t , Any.here refl
  available/target {xs = _ ∷ xs} (Any.there available)
    with available/target available
  ... | t , member = t , Any.there member

  NoNewAfter :
    (G : Graph) → State G → Edge (size G) → Set
  NoNewAfter G s (β , t) =
    All
      (λ where
        (γ , _) →
          sender γ ∉α β
            × receiver γ ∉α β
            → Available γ (edges G s))
      (edges G t)

  noNewAfter? :
    (G : Graph) (s : State G) (edge : Edge (size G))
    → Dec (NoNewAfter G s edge)
  noNewAfter? G s (β , t) =
    All.all?
      (λ where
        (γ , _) →
          ((_∉α?_ (sender γ) β)
            ×-dec (_∉α?_ (receiver γ) β))
          →-dec available? γ (edges G s))
      (edges G t)

  NoNewBranchAfter :
    (G : Graph) → State G → Edge (size G) → Set
  NoNewBranchAfter G s (β , t) =
    All
      (λ where
        (α , _) →
          receiver α ∉α β
            → All
                (λ where
                  (α′ , _) →
                    Action.comm α ≡ Action.comm α′
                      → Available α′ (edges G s))
                (edges G t))
      (edges G s)

  noNewBranchAfter? :
    (G : Graph) (s : State G) (edge : Edge (size G))
    → Dec (NoNewBranchAfter G s edge)
  noNewBranchAfter? G s (β , t) =
    All.all?
      (λ where
        (α , _) →
          (_∉α?_ (receiver α) β) →-dec
            All.all?
              (λ where
                (α′ , _) →
                  (Action.comm α ≟Comm Action.comm α′) →-dec
                    available? α′ (edges G s))
              (edges G t))
      (edges G s)

  Completion :
    (G : Graph) → Edge (size G) → Edge (size G) → Set
  Completion G (α , t) (β , u) =
    Σ[ v ∈ State G ]
      _-<_>->_ {G} t β v × _-<_>->_ {G} u α v

  completion? :
    (G : Graph) (left right : Edge (size G))
    → Dec (Completion G left right)
  completion? G (α , t) (β , u) =
    Fin.any? λ v →
      step? G t β v ×-dec step? G u α v

  Commutes :
    (G : Graph) → Edge (size G) → Edge (size G) → Set
  Commutes G (α , t) (β , u) =
    α ⋄ β → Completion G (α , t) (β , u)

  commutes? :
    (G : Graph) (left right : Edge (size G))
    → Dec (Commutes G left right)
  commutes? G left@(α , _) right@(β , _) =
    (α ⋄? β) →-dec completion? G left right

  BothCommute :
    (G : Graph) → Edge (size G) → Edge (size G) → Set
  BothCommute G left right =
    Commutes G left right × Commutes G right left

  bothCommute? :
    (G : Graph) (left right : Edge (size G))
    → Dec (BothCommute G left right)
  bothCommute? G left right =
    commutes? G left right ×-dec commutes? G right left

  commutes/refl :
    ∀ {G} (edge : Edge (size G)) → BothCommute G edge edge
  commutes/refl {G} edge@(α , _) = impossible , impossible
    where
      impossible : Commutes G edge edge
      impossible (receiver∉ , _) =
        ⊥-elim (∉c→¬∈c receiver∉ (∈R refl))

  commutes/sym :
    ∀ {G} {left right : Edge (size G)}
    → BothCommute G left right
    → BothCommute G right left
  commutes/sym {G} {left} {right} (forward , backward) =
    backward , forward

  allPairs/member :
    ∀ {A : Set}
      {_R_ : A → A → Set}
      {xs : List A}
      {x y : A}
    → (∀ z → z R z)
    → (∀ {u v} → u R v → v R u)
    → AllPairs _R_ xs
    → x ∈ xs
    → y ∈ xs
    → x R y
  allPairs/member reflexive symmetric Pairs.[] ()
  allPairs/member reflexive symmetric
    (head Pairs.∷ pairs)
    (Any.here refl)
    (Any.here refl) =
    reflexive _
  allPairs/member reflexive symmetric
    (head Pairs.∷ pairs)
    (Any.here refl)
    (Any.there y∈) =
    All.lookup head y∈
  allPairs/member reflexive symmetric
    (head Pairs.∷ pairs)
    (Any.there x∈)
    (Any.here refl) =
    symmetric (All.lookup head x∈)
  allPairs/member reflexive symmetric
    (head Pairs.∷ pairs)
    (Any.there x∈)
    (Any.there y∈) =
    allPairs/member reflexive symmetric pairs x∈ y∈

  record LocalConditions (G : Graph) : Set where
    field
      proper :
        ∀ s → All Proper (edges G s)

      deterministic :
        ∀ s → AllPairs SameTarget (edges G s)

      recv-coherent :
        ∀ s → AllPairs BothRecvCoherent (edges G s)

      same-arity :
        ∀ s → AllPairs BothSameArity (edges G s)

      same-sort :
        ∀ s → AllPairs BothSameSort (edges G s)

      no-new-comm :
        ∀ s → All (NoNewAfter G s) (edges G s)

      no-new-branch :
        ∀ s → All (NoNewBranchAfter G s) (edges G s)

      diamond :
        ∀ s → AllPairs (BothCommute G) (edges G s)

  open LocalConditions

  properConditions? :
    (G : Graph) → Dec (∀ s → All Proper (edges G s))
  properConditions? G =
    Fin.all? (λ s → All.all? proper? (edges G s))

  deterministicConditions? :
    (G : Graph) → Dec (∀ s → AllPairs SameTarget (edges G s))
  deterministicConditions? G =
    Fin.all? (λ s → Pairs.allPairs? sameTarget? (edges G s))

  recvConditions? :
    (G : Graph)
    → Dec (∀ s → AllPairs BothRecvCoherent (edges G s))
  recvConditions? G =
    Fin.all?
      (λ s → Pairs.allPairs? bothRecvCoherent? (edges G s))

  arityConditions? :
    (G : Graph) → Dec (∀ s → AllPairs BothSameArity (edges G s))
  arityConditions? G =
    Fin.all?
      (λ s → Pairs.allPairs? bothSameArity? (edges G s))

  sortConditions? :
    (G : Graph) → Dec (∀ s → AllPairs BothSameSort (edges G s))
  sortConditions? G =
    Fin.all?
      (λ s → Pairs.allPairs? bothSameSort? (edges G s))

  noNewCommConditions? :
    (G : Graph) → Dec (∀ s → All (NoNewAfter G s) (edges G s))
  noNewCommConditions? G =
    Fin.all?
      (λ s → All.all? (noNewAfter? G s) (edges G s))

  noNewBranchConditions? :
    (G : Graph)
    → Dec (∀ s → All (NoNewBranchAfter G s) (edges G s))
  noNewBranchConditions? G =
    Fin.all?
      (λ s → All.all? (noNewBranchAfter? G s) (edges G s))

  diamondConditions? :
    (G : Graph)
    → Dec (∀ s → AllPairs (BothCommute G) (edges G s))
  diamondConditions? G =
    Fin.all?
      (λ s → Pairs.allPairs? (bothCommute? G) (edges G s))

  localConditions? : (G : Graph) → Dec (LocalConditions G)
  localConditions? G
    with properConditions? G
       | deterministicConditions? G
       | recvConditions? G
       | arityConditions? G
       | sortConditions? G
       | noNewCommConditions? G
       | noNewBranchConditions? G
       | diamondConditions? G
  ... | yes proper′ | yes deterministic′ | yes recv′ | yes arity′
      | yes sort′ | yes no-new′ | yes no-branch′ | yes diamond′ =
    yes record
      { proper = proper′
      ; deterministic = deterministic′
      ; recv-coherent = recv′
      ; same-arity = arity′
      ; same-sort = sort′
      ; no-new-comm = no-new′
      ; no-new-branch = no-branch′
      ; diamond = diamond′
      }
  ... | no ¬proper | _ | _ | _ | _ | _ | _ | _ =
    no (¬proper ∘ proper)
  ... | _ | no ¬deterministic | _ | _ | _ | _ | _ | _ =
    no (¬deterministic ∘ deterministic)
  ... | _ | _ | no ¬recv | _ | _ | _ | _ | _ =
    no (¬recv ∘ recv-coherent)
  ... | _ | _ | _ | no ¬arity | _ | _ | _ | _ =
    no (¬arity ∘ same-arity)
  ... | _ | _ | _ | _ | no ¬sort | _ | _ | _ =
    no (¬sort ∘ same-sort)
  ... | _ | _ | _ | _ | _ | no ¬no-new | _ | _ =
    no (¬no-new ∘ no-new-comm)
  ... | _ | _ | _ | _ | _ | _ | no ¬no-branch | _ =
    no (¬no-branch ∘ no-new-branch)
  ... | _ | _ | _ | _ | _ | _ | _ | no ¬diamond =
    no (¬diamond ∘ diamond)

  sender≢receiver/sound :
    ∀ {G s α t}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s α t
    → sender α ≢ receiver α
  sender≢receiver/sound {G = G} {s = s} conditions gr =
    All.lookup
      (proper conditions s)
      (step⇒listed {G = G} gr)

  step-deterministic/sound :
    ∀ {G s α t t′}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s α t
    → _-<_>->_ {G} s α t′
    → t ≡ t′
  step-deterministic/sound {G = G} {s = s} conditions gr gr′ =
    allPairs/member
      sameTarget/refl
      sameTarget/sym
      (deterministic conditions s)
      (step⇒listed {G = G} gr)
      (step⇒listed {G = G} gr′)
      refl

  recv-coherent/sound :
    ∀ {G s α α′ t t′}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s α t
    → _-<_>->_ {G} s α′ t′
    → receiver α ∈α α′
    → Action.comm α ≡ Action.comm α′
  recv-coherent/sound
    {G = G} {s = s} conditions gr gr′ included =
    proj₁
      (allPairs/member
        {A = Edge (size G)}
        {_R_ = BothRecvCoherent}
        recvCoherent/refl
        (λ {u} {v} coherent →
          recvCoherent/sym
            {n = size G} {left = u} {right = v} coherent)
        (recv-coherent conditions s)
        (step⇒listed {G = G} gr)
        (step⇒listed {G = G} gr′))
      included

  arity-deterministic/sound :
    ∀ {G s α α′ t t′}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s α t
    → _-<_>->_ {G} s α′ t′
    → Action.comm α ≡ Action.comm α′
    → nchoices α ≡ nchoices α′
  arity-deterministic/sound
    {G = G} {s = s} conditions gr gr′ same-comm =
    proj₁
      (allPairs/member
        {A = Edge (size G)}
        {_R_ = BothSameArity}
        sameArity/refl
        (λ {u} {v} coherent →
          sameArity/sym
            {n = size G} {left = u} {right = v} coherent)
        (same-arity conditions s)
        (step⇒listed {G = G} gr)
        (step⇒listed {G = G} gr′))
      same-comm

  sort-deterministic/sound :
    ∀ {G s α α′ t t′}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s α t
    → _-<_>->_ {G} s α′ t′
    → Action.comm α ≡ Action.comm α′
    → choiceKey (Action.choice α) ≡ choiceKey (Action.choice α′)
    → sort α ≡ sort α′
  sort-deterministic/sound
    {G = G} {s = s} conditions gr gr′ same-comm same-choice =
    proj₁
      (allPairs/member
        {A = Edge (size G)}
        {_R_ = BothSameSort}
        sameSort/refl
        (λ {u} {v} coherent →
          sameSort/sym
            {n = size G} {left = u} {right = v} coherent)
        (same-sort conditions s)
        (step⇒listed {G = G} gr)
        (step⇒listed {G = G} gr′))
      same-comm
      same-choice

  step-sort-deterministic/sound :
    ∀ {G s t t′ γ I S T}
      {i : Fin (suc I)}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s (γ # i < S >) t
    → _-<_>->_ {G} s (γ # i < T >) t′
    → S ≡ T
  step-sort-deterministic/sound conditions gr gr′ =
    sort-deterministic/sound conditions gr gr′ refl refl

  step-arity-deterministic/sound :
    ∀ {G s t t′ γ I J S T}
      {i : Fin (suc I)}
      {j : Fin (suc J)}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s (γ # i < S >) t
    → _-<_>->_ {G} s (γ # j < T >) t′
    → I ≡ J
  step-arity-deterministic/sound conditions gr gr′ =
    arity-deterministic/sound conditions gr gr′ refl

  no-new-comm/sound :
    ∀ {G s t u β γ}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s β t
    → sender γ ∉α β
    → receiver γ ∉α β
    → _-<_>->_ {G} t γ u
    → Σ[ v ∈ State G ] _-<_>->_ {G} s γ v
  no-new-comm/sound
    {G = G} {s = s} conditions grβ sender∉ receiver∉ grγ =
    let after =
          All.lookup
            (no-new-comm conditions s)
            (step⇒listed {G = G} grβ)
        available =
          All.lookup after (step⇒listed {G = G} grγ)
            (sender∉ , receiver∉)
        target , member = available/target available
    in target , listed⇒step {G = G} member

  no-new-branch/sound :
    ∀ {G s t u v β γ cᵢ cⱼ}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s β t
    → Comm.receiver γ ∉α β
    → _-<_>->_ {G} s (γ # cᵢ) u
    → _-<_>->_ {G} t (γ # cⱼ) v
    → Σ[ w ∈ State G ] _-<_>->_ {G} s (γ # cⱼ) w
  no-new-branch/sound
    {G = G} {s = s} conditions grβ receiver∉ grᵢ grⱼ =
    let after =
          All.lookup
            (no-new-branch conditions s)
            (step⇒listed {G = G} grβ)
        branches =
          All.lookup after (step⇒listed {G = G} grᵢ) receiver∉
        available =
          All.lookup branches (step⇒listed {G = G} grⱼ) refl
        target , member = available/target available
    in target , listed⇒step {G = G} member

  step-diamond/sound :
    ∀ {G s t u α β}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s α t
    → _-<_>->_ {G} s β u
    → α ⋄ β
    → Σ[ v ∈ State G ]
        _-<_>->_ {G} t β v × _-<_>->_ {G} u α v
  step-diamond/sound {G = G} {s = s} conditions grα grβ independent =
    proj₁
      (allPairs/member
        {A = Edge (size G)}
        {_R_ = BothCommute G}
        (commutes/refl {G = G})
        (commutes/sym {G = G})
        (diamond conditions s)
        (step⇒listed {G = G} grα)
        (step⇒listed {G = G} grβ))
      independent

  Stepback : Graph → Set
  Stepback G =
    ∀ {α s t t′}
    → BTheory._~_ (graphTheory G) t t′
    → _-<_>->_ {G} s α t
    → Σ[ s′ ∈ State G ]
        BTheory._~_ (graphTheory G) s s′
          × _-<_>->_ {G} s′ α t′

  wellBehaved :
    (G : Graph) → LocalConditions G → Stepback G
    → WellBehaved (graphTheory G)
  wellBehaved G conditions stepback =
    record
      { recv-overlap⇒same-comm = recv-coherent/sound conditions
      ; sender≢receiver = sender≢receiver/sound conditions
      ; step-deterministic = step-deterministic/sound conditions
      ; step-sort-deterministic =
          step-sort-deterministic/sound conditions
      ; step-arity-deterministic =
          step-arity-deterministic/sound conditions
      ; step-is-prop = λ gr gr′ →
          step-is-prop {G = G} gr gr′
      ; no-new-branch/step = no-new-branch/sound conditions
      ; no-new-comm/step = no-new-comm/sound conditions
      ; stepback/~ = stepback
      ; step-diamond = step-diamond/sound conditions
      }
