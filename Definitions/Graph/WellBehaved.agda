{-# OPTIONS --guardedness #-}

open import Data.Fin using (Fin)
  renaming (_≟_ to _≟Fin_)
import Data.Fin.Properties as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; find; lose)
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
open import Data.Bool using (T)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; subst; subst₂)
open import Relation.Nullary using (Dec; yes; no; ¬?)
open import Relation.Nullary.Decidable using (map′; T?; _×?_; _→?_)

open import Definitions.Behav using (BTheory; WellBehaved; Synchronous)
open import Definitions.Expr using (_≟Sort_)

module Definitions.Graph.WellBehaved (N : ℕ) where

  open import Definitions.Common N using (PartSet)
  open import Definitions.Actions N
  open import Definitions.Graph.Action N
  open import Definitions.Graph.Core N
  open import Definitions.Graph.Bisimulation N

  private
    variable
      n : ℕ

  -- Decisions take bisimilarity as an argument, so one matrix is shared.
  BisimDec : Graph → Set
  BisimDec G = ∀ s t → Dec (Bisimilar G s t)

  -- Up to `~`, as `WellBehaved.step-deterministic` is.
  SameTarget : (G : Graph) → Edge (size G) → Edge (size G) → Set
  SameTarget G (α , t) (α′ , t′) = α ≡ α′ → Bisimilar G t t′

  sameTarget? :
    ∀ {G} → BisimDec G
    → (left right : Edge (size G)) → Dec (SameTarget G left right)
  sameTarget? bisimT? (α , t) (α′ , t′) =
    (α ≟Action α′) →? bisimT? t t′

  -- `AllPairs` sees each pair once, so conditions use `Both R`.
  Both : {A : Set} → (A → A → Set) → A → A → Set
  Both R x y = R x y × R y x

  both? :
    ∀ {A : Set}{R : A → A → Set}
    → (∀ x y → Dec (R x y)) → ∀ x y → Dec (Both R x y)
  both? R? x y = R? x y ×? R? y x

  both/refl : ∀ {A : Set}{R : A → A → Set} → (∀ x → R x x) → ∀ x → Both R x x
  both/refl r x = r x , r x

  RecvCoherent : Edge n → Edge n → Set
  RecvCoherent (α , _) (α′ , _) =
    ∀ Q → Recv α Q → Q ∈α α′ → comm α ≡ comm α′

  recvCoherent? :
    (left right : Edge n) → Dec (RecvCoherent left right)
  recvCoherent? (α , _) (α′ , _) =
    Fin.all? λ Q →
      Recv? α Q →? (Q ∈α? α′) →? (comm α ≟Comm comm α′)

  recvCoherent/refl : ∀ {n} (edge : Edge n) → RecvCoherent edge edge
  recvCoherent/refl _ _ _ _ = refl

  -- Two receive events at one participant, from the same sender, agree on
  -- their choices as `F` says; any other pair of events is unconstrained.
  AgreeOn : (Choice → Choice → Set) → Maybe Event → Maybe Event → Set
  AgreeOn F (just ((？ P) # c)) (just ((？ P′) # c′)) = P ≡ P′ → F c c′
  AgreeOn F _ _ = ⊤

  agreeOn? :
    ∀ {F} → (∀ c c′ → Dec (F c c′)) → ∀ x y → Dec (AgreeOn F x y)
  agreeOn? F? (just ((？ P) # c)) (just ((？ P′) # c′)) =
    (P ≟Fin P′) →? F? c c′
  agreeOn? F? nothing            _                   = yes tt
  agreeOn? F? (just ((! _) # _)) _                   = yes tt
  agreeOn? F? (just ((？ _) # _)) nothing             = yes tt
  agreeOn? F? (just ((？ _) # _)) (just ((! _) # _))  = yes tt

  agreeOn/refl : ∀ {F} → (∀ c → F c c) → ∀ x → AgreeOn F x x
  agreeOn/refl r nothing            = tt
  agreeOn/refl r (just ((! _) # _)) = tt
  agreeOn/refl r (just ((？ _) # c)) = λ _ → r c

  SameOn : (Choice → Choice → Set) → Edge n → Edge n → Set
  SameOn F (α , _) (α′ , _) = ∀ Q → AgreeOn F (ev α Q) (ev α′ Q)

  sameOn? :
    ∀ {F} → (∀ c c′ → Dec (F c c′))
    → (left right : Edge n) → Dec (SameOn F left right)
  sameOn? F? (α , _) (α′ , _) =
    Fin.all? λ Q → agreeOn? F? (ev α Q) (ev α′ Q)

  sameOn/refl : ∀ {F} → (∀ c → F c c) → ∀ {n} (edge : Edge n) → SameOn F edge edge
  sameOn/refl r (α , _) Q = agreeOn/refl r (ev α Q)

  -- Same sender: same arity.
  ArityF : Choice → Choice → Set
  ArityF c c′ = Choice.nchoices c ≡ Choice.nchoices c′

  -- Same sender and label: same sort.
  SortF : Choice → Choice → Set
  SortF c c′ = choiceKey c ≡ choiceKey c′ → Choice.sort c ≡ Choice.sort c′

  arityF? : ∀ c c′ → Dec (ArityF c c′)
  arityF? c c′ = Choice.nchoices c Nat.≟ Choice.nchoices c′

  sortF? : ∀ c c′ → Dec (SortF c c′)
  sortF? c c′ =
    (choiceKey c ≟ChoiceKey choiceKey c′) →?
      (Choice.sort c ≟Sort Choice.sort c′)

  SameArity SameSort : Edge n → Edge n → Set
  SameArity = SameOn ArityF
  SameSort  = SameOn SortF

  Available : ∀ {n} → Action → List (Edge n) → Set
  Available α = Any.Any (λ edge → proj₁ edge ≡ α)

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
          Fin.all? (λ X → (X ∈α? γ) →? (X ∉α? β))
          →? available? γ (edges G s))
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
          Fin.all? (λ Q → Recv? α Q →? (Q ∉α? β)) →?
            All.all?
              (λ where
                (α′ , _) →
                  (comm α′ ≟Comm comm α) →?
                    available? α′ (edges G s))
              (edges G t))
      (edges G s)

  -- Both closings exist and their targets are bisimilar.
  Completion :
    (G : Graph) → Edge (size G) → Edge (size G) → Set
  Completion G (α , t) (β , u) =
    Any.Any
      (λ x → proj₁ x ≡ β ×
        Any.Any (λ y → proj₁ y ≡ α × Bisimilar G (proj₂ x) (proj₂ y))
          (edges G u))
      (edges G t)

  completion? :
    (G : Graph) → BisimDec G → (left right : Edge (size G))
    → Dec (Completion G left right)
  completion? G bisimT? (α , t) (β , u) =
    Any.any? (λ x → (proj₁ x ≟Action β) ×?
      Any.any? (λ y → (proj₁ y ≟Action α) ×? bisimT? (proj₂ x) (proj₂ y))
        (edges G u))
      (edges G t)

  completion/sound :
    ∀ {G α t β u}
    → Completion G (α , t) (β , u)
    → Σ[ v ∈ State G ] Σ[ w ∈ State G ]
        _-<_>->_ {G} t β v × _-<_>->_ {G} u α w × Bisimilar G v w
  completion/sound c
    with find c
  ... | (_ , v) , v∈ , refl , c′
    with find c′
  ...   | (_ , w) , w∈ , refl , vw =
    v , w , listed⇒step v∈ , listed⇒step w∈ , vw

  completion/complete :
    ∀ {G α t β u v w}
    → _-<_>->_ {G} t β v → _-<_>->_ {G} u α w → Bisimilar G v w
    → Completion G (α , t) (β , u)
  completion/complete grβ grα vw =
    lose (step⇒listed grβ) (refl , lose (step⇒listed grα) (refl , vw))

  Commutes :
    (G : Graph) → Edge (size G) → Edge (size G) → Set
  Commutes G (α , t) (β , u) =
    α ⋄ β → Completion G (α , t) (β , u)

  commutes? :
    (G : Graph) → BisimDec G → (left right : Edge (size G))
    → Dec (Commutes G left right)
  commutes? G bisimT? left@(α , _) right@(β , _) =
    (α ⋄? β) →? completion? G bisimT? left right

  -- Vacuous: `⋄` includes `≢`.
  commutes/refl : ∀ {G} (edge : Edge (size G)) → Commutes G edge edge
  commutes/refl _ (α≢α , _) = ⊥-elim (α≢α refl)

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

  -- `allPairs/member` at `Both R`, whose symmetry is free.
  allPairs/both :
    ∀ {A : Set}{R : A → A → Set}{xs : List A}{x y : A}
    → (∀ z → R z z) → AllPairs (Both R) xs → x ∈ xs → y ∈ xs → R x y
  allPairs/both {R = R} r pairs x∈ y∈ =
    proj₁
      (allPairs/member {_R_ = Both R} (both/refl {R = R} r) (λ (a , b) → b , a)
        pairs x∈ y∈)

  record LocalConditions (G : Graph) : Set where
    field
      deterministic :
        ∀ s → AllPairs (SameTarget G) (edges G s)

      recv-coherent :
        ∀ s → AllPairs (Both RecvCoherent) (edges G s)

      same-arity :
        ∀ s → AllPairs (Both SameArity) (edges G s)

      same-sort :
        ∀ s → AllPairs (Both SameSort) (edges G s)

      no-new-branch :
        ∀ s → All (NoNewBranchAfter G s) (edges G s)

      diamond :
        ∀ s → AllPairs (Both (Commutes G)) (edges G s)

  open LocalConditions

  deterministicConditions? :
    (G : Graph) → BisimDec G
    → Dec (∀ s → AllPairs (SameTarget G) (edges G s))
  deterministicConditions? G bisimT? =
    Fin.all? (λ s → Pairs.allPairs? (sameTarget? {G} bisimT?) (edges G s))

  recvConditions? :
    (G : Graph)
    → Dec (∀ s → AllPairs (Both RecvCoherent) (edges G s))
  recvConditions? G =
    Fin.all?
      (λ s → Pairs.allPairs? (both? recvCoherent?) (edges G s))

  arityConditions? :
    (G : Graph) → Dec (∀ s → AllPairs (Both SameArity) (edges G s))
  arityConditions? G =
    Fin.all?
      (λ s → Pairs.allPairs? (both? (sameOn? arityF?)) (edges G s))

  sortConditions? :
    (G : Graph) → Dec (∀ s → AllPairs (Both SameSort) (edges G s))
  sortConditions? G =
    Fin.all?
      (λ s → Pairs.allPairs? (both? (sameOn? sortF?)) (edges G s))

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
    (G : Graph) → BisimDec G
    → Dec (∀ s → AllPairs (Both (Commutes G)) (edges G s))
  diamondConditions? G bisimT? =
    Fin.all?
      (λ s → Pairs.allPairs? (both? (commutes? G bisimT?)) (edges G s))

  localConditionsWith? :
    (G : Graph) → BisimDec G → Dec (LocalConditions G)
  localConditionsWith? G bisimT?
    with deterministicConditions? G bisimT?
       | recvConditions? G
       | arityConditions? G
       | sortConditions? G
       | noNewBranchConditions? G
       | diamondConditions? G bisimT?
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

  -- The matrix is computed once, as a bound argument.
  localConditions? : (G : Graph) → Dec (LocalConditions G)
  localConditions? G =
    localConditionsWith? G (shared (approximation G) (λ _ _ → refl))
    where
      shared :
        (mat : Matrix G)
        → (∀ s t → related G mat s t ≡ bisim? G s t)
        → BisimDec G
      shared mat eqv s t =
        subst (λ b → Dec (T b)) (eqv s t) (T? (related G mat s t))

  step-deterministic/sound :
    ∀ {G s α t t′}
    → BisimulationCorrect G
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s α t
    → _-<_>->_ {G} s α t′
    → BTheory._~_ (graphTheory G) t t′
  step-deterministic/sound {G = G} {s = s} correct conditions gr gr′ =
    sound correct
      (allPairs/member
        (λ _ _ → complete correct ~refl)
        (λ same eq → complete correct (~sym (sound correct (same (sym eq)))))
        (deterministic conditions s)
        (step⇒listed gr)
        (step⇒listed gr′)
        refl)
    where open BTheory (graphTheory G) using (~refl; ~sym)

  recv-coherent/sound :
    ∀ {G s α α′ t t′}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s α t
    → _-<_>->_ {G} s α′ t′
    → ∀ {Q} → Recv α Q → Q ∈α α′
    → comm α ≡ comm α′
  recv-coherent/sound
    {G = G} {s = s} conditions gr gr′ {Q} rQ included =
    allPairs/both {R = RecvCoherent} recvCoherent/refl
      (recv-coherent conditions s)
      (step⇒listed gr) (step⇒listed gr′)
      Q rQ included

  same-arity/sound :
    ∀ {G s α α′ t t′}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s α t
    → _-<_>->_ {G} s α′ t′
    → ∀ Q → AgreeOn ArityF (ev α Q) (ev α′ Q)
  same-arity/sound {G = G} {s = s} conditions gr gr′ =
    allPairs/both {R = SameArity} (sameOn/refl λ _ → refl)
      (same-arity conditions s)
      (step⇒listed gr) (step⇒listed gr′)

  same-sort/sound :
    ∀ {G s α α′ t t′}
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s α t
    → _-<_>->_ {G} s α′ t′
    → ∀ Q → AgreeOn SortF (ev α Q) (ev α′ Q)
  same-sort/sound {G = G} {s = s} conditions gr gr′ =
    allPairs/both {R = SameSort} (sameOn/refl λ _ _ → refl)
      (same-sort conditions s)
      (step⇒listed gr) (step⇒listed gr′)

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
    subst₂ (AgreeOn SortF) eq eq′ (same-sort/sound conditions gr gr′ Q) refl refl

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
    subst₂ (AgreeOn ArityF) eq eq′ (same-arity/sound conditions gr gr′ Q) refl

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
            (step⇒listed grβ)
        branches =
          All.lookup after (step⇒listed grᵢ) idle
        available =
          All.lookup branches (step⇒listed grⱼ) ceq
        target , member = available/target available
    in target , listed⇒step member

  step-diamond/sound :
    ∀ {G s t u α β}
    → BisimulationCorrect G
    → (conditions : LocalConditions G)
    → _-<_>->_ {G} s α t
    → _-<_>->_ {G} s β u
    → α ⋄ β
    → Σ[ v ∈ State G ] Σ[ w ∈ State G ]
        _-<_>->_ {G} t β v × _-<_>->_ {G} u α w
          × BTheory._~_ (graphTheory G) v w
  step-diamond/sound {G = G} {s = s} correct conditions grα grβ independent =
    let v , w , grv , grw , vw =
          completion/sound
            (allPairs/both {R = Commutes G} (commutes/refl {G = G})
              (diamond conditions s)
              (step⇒listed grα) (step⇒listed grβ)
              independent)
    in v , w , grv , grw , sound correct vw

  wellBehaved :
    (G : Graph) → BisimulationCorrect G → LocalConditions G
    → WellBehaved (graphTheory G)
  wellBehaved G correct conditions =
    record
      { recv-overlap = λ gr gr′ → recv-coherent/sound conditions gr gr′
      ; step-deterministic = step-deterministic/sound correct conditions
      ; step-sort-det = step-sort-det/sound conditions
      ; step-arity-det = step-arity-det/sound conditions
      ; no-new-branch/step = no-new-branch/sound conditions
      ; step-diamond = step-diamond/sound correct conditions
      }

  -- ══════════════════════════════════════════════════════════════════
  --  The synchronous instance
  -- ══════════════════════════════════════════════════════════════════

  -- `α` is `P`'s multicast to a nonempty set not containing `P`.
  SendsAt : Action → Fin N → Set
  SendsAt α P =
    Σ[ Qs ∈ PartSet ] Σ[ c ∈ Choice ]
      P ∉ Qs × Nonempty Qs × α ≡ P ⟶ Qs # c

  sendsAt? : ∀ α P → Dec (SendsAt α P)
  sendsAt? α P with ev α P in eq
  ... | nothing =
    no λ { (Qs , c , _ , _ , refl) → bad (trans (sym eq) (ev-sender {P} {Qs} {c})) }
    where bad : ∀ {e} → nothing ≡ just e → ⊥
          bad ()
  ... | just ((？ _) # _) =
    no λ { (Qs , c , _ , _ , refl) → bad (trans (sym eq) (ev-sender {P} {Qs} {c})) }
    where bad : ∀ {R c Qs c′} → just ((？ R) # c) ≡ just ((! Qs) # c′) → ⊥
          bad ()
  ... | just ((! Qs) # c) =
    map′ (λ b → Qs , c , b) from
      (¬? (P ∈? Qs) ×? nonempty? Qs ×? (α ≟Action (P ⟶ Qs # c)))
    where
      from : SendsAt α P → P ∉ Qs × Nonempty Qs × α ≡ P ⟶ Qs # c
      from (Qs′ , c′ , b@(_ , _ , refl))
        with trans (sym eq) (ev-sender {P} {Qs′} {c′})
      ... | refl = b

  -- Literally `Synchronous.balanced`'s conclusion.
  BalancedEdge : Edge n → Set
  BalancedEdge (α , _) = Σ[ P ∈ Fin N ] SendsAt α P

  balanced? : (edge : Edge n) → Dec (BalancedEdge edge)
  balanced? (α , _) = Fin.any? (sendsAt? α)

  record SyncConditions (G : Graph) : Set where
    field
      balanced :
        ∀ s → All BalancedEdge (edges G s)

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
  balanced/sound {G = G} {s = s} conditions gr =
    All.lookup (balanced conditions s) (step⇒listed gr)

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
            (step⇒listed grβ)
        available =
          All.lookup after (step⇒listed grγ) idle
        target , member = available/target available
    in target , listed⇒step member

  synchronous :
    (G : Graph) → SyncConditions G → Synchronous (graphTheory G)
  synchronous G conditions =
    record
      { balanced = balanced/sound conditions
      ; no-new-comm/step = no-new-comm/sound conditions
      }
