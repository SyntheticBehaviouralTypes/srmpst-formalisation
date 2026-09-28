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
open import Data.Fin.Subset using (_∉_; Nonempty)
open import Data.Fin.Subset.Properties using (_∈?_; nonempty?)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; subst₂)
open import Relation.Nullary using (Dec; yes; no; ¬?)
open import Relation.Nullary.Decidable using (_×-dec_; _→-dec_)

open import Definitions.Behav using (BTheory; WellBehaved; Synchronous)
open import Definitions.Expr using (_≟Sort_)

module Definitions.Graph.WellBehaved (N : ℕ) where

  open import Definitions.Common N using (PartSet)
  open import Definitions.Actions N
  open import Definitions.Graph.Action N
  open import Definitions.Graph.Core N

  private
    variable
      n : ℕ

  EdgeAction : Edge n → Action
  EdgeAction = proj₁

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
    ∀ Q → Recv α Q → Q ∈α α′ → comm α ≡ comm α′

  recvCoherent? :
    (left right : Edge n) → Dec (RecvCoherent left right)
  recvCoherent? (α , _) (α′ , _) =
    Fin.all? λ Q →
      Recv? α Q →-dec (Q ∈α? α′) →-dec (comm α ≟Comm comm α′)

  BothRecvCoherent : Edge n → Edge n → Set
  BothRecvCoherent left right =
    RecvCoherent left right × RecvCoherent right left

  bothRecvCoherent? :
    (left right : Edge n) → Dec (BothRecvCoherent left right)
  bothRecvCoherent? left right =
    recvCoherent? left right ×-dec recvCoherent? right left

  recvCoherent/refl :
    ∀ {n} (edge : Edge n) → BothRecvCoherent edge edge
  recvCoherent/refl _ = (λ _ _ _ → refl) , (λ _ _ _ → refl)

  recvCoherent/sym :
    ∀ {n} {left right : Edge n}
    → BothRecvCoherent left right
    → BothRecvCoherent right left
  recvCoherent/sym (left , right) = right , left

  -- Two receive events from the same sender agree on the arity.
  AgreeArity : Maybe Event → Maybe Event → Set
  AgreeArity (just ((？ P) # c)) (just ((？ P′) # c′)) =
    P ≡ P′ → Choice.nchoices c ≡ Choice.nchoices c′
  AgreeArity _ _ = ⊤

  agreeArity? : ∀ x y → Dec (AgreeArity x y)
  agreeArity? (just ((？ P) # c)) (just ((？ P′) # c′)) =
    (P ≟Fin P′) →-dec (Choice.nchoices c Nat.≟ Choice.nchoices c′)
  agreeArity? nothing            _                   = yes tt
  agreeArity? (just ((! _) # _)) _                   = yes tt
  agreeArity? (just ((？ _) # _)) nothing             = yes tt
  agreeArity? (just ((？ _) # _)) (just ((! _) # _))  = yes tt

  agreeArity/refl : ∀ x → AgreeArity x x
  agreeArity/refl nothing            = tt
  agreeArity/refl (just ((! _) # _)) = tt
  agreeArity/refl (just ((？ _) # _)) = λ _ → refl

  SameArity : Edge n → Edge n → Set
  SameArity (α , _) (α′ , _) = ∀ Q → AgreeArity (ev α Q) (ev α′ Q)

  sameArity? : (left right : Edge n) → Dec (SameArity left right)
  sameArity? (α , _) (α′ , _) =
    Fin.all? λ Q → agreeArity? (ev α Q) (ev α′ Q)

  BothSameArity : Edge n → Edge n → Set
  BothSameArity left right =
    SameArity left right × SameArity right left

  bothSameArity? :
    (left right : Edge n) → Dec (BothSameArity left right)
  bothSameArity? left right =
    sameArity? left right ×-dec sameArity? right left

  sameArity/refl :
    ∀ {n} (edge : Edge n) → BothSameArity edge edge
  sameArity/refl (α , _) =
    (λ Q → agreeArity/refl (ev α Q)) , (λ Q → agreeArity/refl (ev α Q))

  sameArity/sym :
    ∀ {n} {left right : Edge n}
    → BothSameArity left right
    → BothSameArity right left
  sameArity/sym (left , right) = right , left

  -- Two receive events from the same sender with the same label agree on
  -- the sort.
  AgreeSort : Maybe Event → Maybe Event → Set
  AgreeSort (just ((？ P) # c)) (just ((？ P′) # c′)) =
    P ≡ P′ → choiceKey c ≡ choiceKey c′ → Choice.sort c ≡ Choice.sort c′
  AgreeSort _ _ = ⊤

  agreeSort? : ∀ x y → Dec (AgreeSort x y)
  agreeSort? (just ((？ P) # c)) (just ((？ P′) # c′)) =
    (P ≟Fin P′) →-dec
      ((choiceKey c ≟ChoiceKey choiceKey c′) →-dec
        (Choice.sort c ≟Sort Choice.sort c′))
  agreeSort? nothing            _                   = yes tt
  agreeSort? (just ((! _) # _)) _                   = yes tt
  agreeSort? (just ((？ _) # _)) nothing             = yes tt
  agreeSort? (just ((？ _) # _)) (just ((! _) # _))  = yes tt

  agreeSort/refl : ∀ x → AgreeSort x x
  agreeSort/refl nothing            = tt
  agreeSort/refl (just ((! _) # _)) = tt
  agreeSort/refl (just ((？ _) # _)) = λ _ _ → refl

  SameSort : Edge n → Edge n → Set
  SameSort (α , _) (α′ , _) = ∀ Q → AgreeSort (ev α Q) (ev α′ Q)

  sameSort? : (left right : Edge n) → Dec (SameSort left right)
  sameSort? (α , _) (α′ , _) =
    Fin.all? λ Q → agreeSort? (ev α Q) (ev α′ Q)

  BothSameSort : Edge n → Edge n → Set
  BothSameSort left right =
    SameSort left right × SameSort right left

  bothSameSort? :
    (left right : Edge n) → Dec (BothSameSort left right)
  bothSameSort? left right =
    sameSort? left right ×-dec sameSort? right left

  sameSort/refl :
    ∀ {n} (edge : Edge n) → BothSameSort edge edge
  sameSort/refl (α , _) =
    (λ Q → agreeSort/refl (ev α Q)) , (λ Q → agreeSort/refl (ev α Q))

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
          (∀ X → X ∈α γ → X ∉α β)
            → Available γ (edges G s))
      (edges G t)

  noNewAfter? :
    (G : Graph) (s : State G) (edge : Edge (size G))
    → Dec (NoNewAfter G s edge)
  noNewAfter? G s (β , t) =
    All.all?
      (λ where
        (γ , _) →
          Fin.all? (λ X → (X ∈α? γ) →-dec (X ∉α? β))
          →-dec available? γ (edges G s))
      (edges G t)

  NoNewBranchAfter :
    (G : Graph) → State G → Edge (size G) → Set
  NoNewBranchAfter G s (β , t) =
    All
      (λ where
        (α , _) →
          (∀ Q → Recv α Q → Q ∉α β)
            → All
                (λ where
                  (α′ , _) →
                    comm α′ ≡ comm α
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
          Fin.all? (λ Q → Recv? α Q →-dec (Q ∉α? β)) →-dec
            All.all?
              (λ where
                (α′ , _) →
                  (comm α′ ≟Comm comm α) →-dec
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
      impossible (α≢α , _) = ⊥-elim (α≢α refl)

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
      deterministic :
        ∀ s → AllPairs SameTarget (edges G s)

      recv-coherent :
        ∀ s → AllPairs BothRecvCoherent (edges G s)

      same-arity :
        ∀ s → AllPairs BothSameArity (edges G s)

      same-sort :
        ∀ s → AllPairs BothSameSort (edges G s)

      no-new-branch :
        ∀ s → All (NoNewBranchAfter G s) (edges G s)

      diamond :
        ∀ s → AllPairs (BothCommute G) (edges G s)

  open LocalConditions

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
    with deterministicConditions? G
       | recvConditions? G
       | arityConditions? G
       | sortConditions? G
       | noNewBranchConditions? G
       | diamondConditions? G
  ... | yes deterministic′ | yes recv′ | yes arity′
      | yes sort′ | yes no-branch′ | yes diamond′ =
    yes record
      { deterministic = deterministic′
      ; recv-coherent = recv′
      ; same-arity = arity′
      ; same-sort = sort′
      ; no-new-branch = no-branch′
      ; diamond = diamond′
      }
  ... | no ¬deterministic | _ | _ | _ | _ | _ =
    no (¬deterministic ∘ deterministic)
  ... | _ | no ¬recv | _ | _ | _ | _ =
    no (¬recv ∘ recv-coherent)
  ... | _ | _ | no ¬arity | _ | _ | _ =
    no (¬arity ∘ same-arity)
  ... | _ | _ | _ | no ¬sort | _ | _ =
    no (¬sort ∘ same-sort)
  ... | _ | _ | _ | _ | no ¬no-branch | _ =
    no (¬no-branch ∘ no-new-branch)
  ... | _ | _ | _ | _ | _ | no ¬diamond =
    no (¬diamond ∘ diamond)

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
    → ∀ {Q} → Recv α Q → Q ∈α α′
    → comm α ≡ comm α′
  recv-coherent/sound
    {G = G} {s = s} conditions gr gr′ {Q} rQ included =
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
      Q rQ included

  same-arity/sound :
    ∀ {G s α α′ t t′}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s α t
    → _-<_>->_ {G} s α′ t′
    → ∀ Q → AgreeArity (ev α Q) (ev α′ Q)
  same-arity/sound
    {G = G} {s = s} conditions gr gr′ =
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

  same-sort/sound :
    ∀ {G s α α′ t t′}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s α t
    → _-<_>->_ {G} s α′ t′
    → ∀ Q → AgreeSort (ev α Q) (ev α′ Q)
  same-sort/sound
    {G = G} {s = s} conditions gr gr′ =
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

  step-sort-det/sound :
    ∀ {G s t t′ α α′ P Q I S T}
      {i : Fin (suc I)}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s α t
    → _-<_>->_ {G} s α′ t′
    → ev α Q ≡ just ((？ P) # i < S >)
    → ev α′ Q ≡ just ((？ P) # i < T >)
    → S ≡ T
  step-sort-det/sound {Q = Q} conditions gr gr′ eq eq′ =
    subst₂ AgreeSort eq eq′ (same-sort/sound conditions gr gr′ Q) refl refl

  step-arity-det/sound :
    ∀ {G s t t′ α α′ P Q I J S T}
      {i : Fin (suc I)}
      {j : Fin (suc J)}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s α t
    → _-<_>->_ {G} s α′ t′
    → ev α Q ≡ just ((？ P) # i < S >)
    → ev α′ Q ≡ just ((？ P) # j < T >)
    → I ≡ J
  step-arity-det/sound {Q = Q} conditions gr gr′ eq eq′ =
    subst₂ AgreeArity eq eq′ (same-arity/sound conditions gr gr′ Q) refl

  no-new-branch/sound :
    ∀ {G s t u v β γ γ′}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s β t
    → (∀ Q → Recv γ Q → Q ∉α β)
    → _-<_>->_ {G} s γ u
    → _-<_>->_ {G} t γ′ v
    → comm γ′ ≡ comm γ
    → Σ[ w ∈ State G ] _-<_>->_ {G} s γ′ w
  no-new-branch/sound
    {G = G} {s = s} conditions grβ idle grᵢ grⱼ ceq =
    let after =
          All.lookup
            (no-new-branch conditions s)
            (step⇒listed {G = G} grβ)
        branches =
          All.lookup after (step⇒listed {G = G} grᵢ) idle
        available =
          All.lookup branches (step⇒listed {G = G} grⱼ) ceq
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
      { recv-overlap = λ gr gr′ → recv-coherent/sound conditions gr gr′
      ; step-deterministic = step-deterministic/sound conditions
      ; step-sort-det = step-sort-det/sound conditions
      ; step-arity-det = step-arity-det/sound conditions
      ; step-is-prop = λ gr gr′ →
          step-is-prop {G = G} gr gr′
      ; no-new-branch/step = no-new-branch/sound conditions
      ; stepback/~ = stepback
      ; step-diamond = step-diamond/sound conditions
      }

  -- ══════════════════════════════════════════════════════════════════
  --  The synchronous instance
  -- ══════════════════════════════════════════════════════════════════

  -- `α` is `P`'s multicast to a nonempty set not containing `P`.  The `ev`
  -- equation is redundant (it follows from the last one) but is what the
  -- decision reads.
  SendsAt : Action → Fin N → Set
  SendsAt α P =
    Σ[ Qs ∈ PartSet ] Σ[ c ∈ Choice ]
      ev α P ≡ just ((! Qs) # c)
      × P ∉ Qs × Nonempty Qs × α ≡ P ⟶ Qs # c

  sendsAt? : ∀ α P → Dec (SendsAt α P)
  sendsAt? α P with ev α P
  ... | nothing            = no λ { (_ , _ , () , _) }
  ... | just ((？ _) # _)   = no λ { (_ , _ , () , _) }
  ... | just ((! Qs) # c)
    with ¬? (P ∈? Qs) ×-dec nonempty? Qs ×-dec (α ≟Action (P ⟶ Qs # c))
  ...   | yes b = yes (Qs , c , refl , b)
  ...   | no ¬b = no λ { (_ , _ , refl , b) → ¬b b }

  Balanced : Edge n → Set
  Balanced (α , _) = Σ[ P ∈ Fin N ] SendsAt α P

  balanced? : (edge : Edge n) → Dec (Balanced edge)
  balanced? (α , _) = Fin.any? (sendsAt? α)

  record SyncConditions (G : Graph) : Set where
    field
      balanced :
        ∀ s → All Balanced (edges G s)

      no-new-comm :
        ∀ s → All (NoNewAfter G s) (edges G s)

  open SyncConditions

  syncConditions? : (G : Graph) → Dec (SyncConditions G)
  syncConditions? G
    with Fin.all? (λ s → All.all? balanced? (edges G s))
       | noNewCommConditions? G
  ... | yes balanced′ | yes no-new′ =
    yes record { balanced = balanced′ ; no-new-comm = no-new′ }
  ... | no ¬balanced | _ =
    no (¬balanced ∘ balanced)
  ... | _ | no ¬no-new =
    no (¬no-new ∘ no-new-comm)

  balanced/sound :
    ∀ {G s α t}
    → (conditions : SyncConditions G)
    → _-<_>->_ {G} s α t
    → Σ[ P ∈ Fin N ] Σ[ Qs ∈ PartSet ] Σ[ c ∈ Choice ]
        P ∉ Qs × Nonempty Qs × α ≡ P ⟶ Qs # c
  balanced/sound {G = G} {s = s} conditions gr
    with All.lookup (balanced conditions s) (step⇒listed {G = G} gr)
  ... | P , Qs , c , _ , rest = P , Qs , c , rest

  no-new-comm/sound :
    ∀ {G s t u β γ}
    → (conditions : SyncConditions G)
    → _-<_>->_ {G} s β t
    → (∀ X → X ∈α γ → X ∉α β)
    → _-<_>->_ {G} t γ u
    → Σ[ v ∈ State G ] _-<_>->_ {G} s γ v
  no-new-comm/sound
    {G = G} {s = s} conditions grβ idle grγ =
    let after =
          All.lookup
            (no-new-comm conditions s)
            (step⇒listed {G = G} grβ)
        available =
          All.lookup after (step⇒listed {G = G} grγ) idle
        target , member = available/target available
    in target , listed⇒step {G = G} member

  synchronous :
    (G : Graph) → SyncConditions G → Synchronous (graphTheory G)
  synchronous G conditions =
    record
      { balanced = balanced/sound conditions
      ; no-new-comm/step = no-new-comm/sound conditions
      }
