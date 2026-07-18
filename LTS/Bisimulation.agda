{-# OPTIONS --guardedness #-}

open import Data.Bool
  using (Bool; T; false; true; _∧_; _∨_)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; all; any)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.Any as Any
open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as Nat
open import Data.Product
  using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; lookup; replicate; tabulate)
import Data.Vec as V
import Data.Vec.Properties as Vec
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; subst; sym; trans)
open import Relation.Nullary.Decidable
  using (⌊_⌋; fromWitness; toWitness)
open import Relation.Nullary using (Dec; yes; no)

open import Definitions.Behav using (BTheory)

module LTS.Bisimulation (N : ℕ) where

  open import Definitions.Actions N using (Action)
  open import LTS.Action N
  open import LTS.Core N

  module Semantic (G : Graph) where
    open BTheory (graphTheory G)

    forth :
      ∀ {s t α u}
      → s ~ t
      → BTheory._-<_>->_ (graphTheory G) s α u
      → Σ[ v ∈ State G ]
          BTheory._-<_>->_ (graphTheory G) t α v × (u ~ v)
    forth equivalent gr = ~L equivalent gr

    symmetric : ∀ {s t} → s ~ t → t ~ s
    symmetric = ~sym

  Matrix : Graph → Set
  Matrix G = Vec (Vec Bool (size G)) (size G)

  top : (G : Graph) → Matrix G
  top G = replicate (size G) (replicate (size G) true)

  related :
    (G : Graph) → Matrix G → State G → State G → Bool
  related G relation s t = lookup (lookup relation s) t

  actionMatches : Action → Action → Bool
  actionMatches α α′ = ⌊ α ≟Action α′ ⌋

  edgeMatches :
    ∀ {G}
    → Matrix G
    → Edge (size G)
    → Edge (size G)
    → Bool
  edgeMatches {G} relation left right =
    actionMatches (proj₁ left) (proj₁ right)
      ∧ related G relation (proj₂ left) (proj₂ right)

  simulates :
    (G : Graph)
    → Matrix G
    → State G
    → State G
    → Bool
  simulates G relation s t =
    all
      (λ left → any (edgeMatches {G} relation left) (edges G t))
      (edges G s)

  refineAt :
    (G : Graph)
    → Matrix G
    → State G
    → State G
    → Bool
  refineAt G relation s t =
    related G relation s t
      ∧ simulates G relation s t
      ∧ simulates G relation t s

  refine : (G : Graph) → Matrix G → Matrix G
  refine G relation =
    tabulate λ s → tabulate λ t → refineAt G relation s t

  iterate : ∀ {A : Set} → ℕ → (A → A) → A → A
  iterate zero f x = x
  iterate (suc fuel) f x = iterate fuel f (f x)

  -- `approximation` used to run the full `size²` pigeonhole bound of
  -- refinement rounds unconditionally; the fixed point is virtually always
  -- reached after a handful, so the *computational* iteration stops as soon
  -- as a round is stable (`iterateFix`), with `iterateFix/iterate` bridging
  -- back to the fuel-only `iterate` the correctness lemmas are stated
  -- against.  (The nested `with` binds `f x` once, so the equality test and
  -- the recursive call share the one computed round.)
  iterateFix :
    ∀ {A : Set}
    → ((x y : A) → Dec (x ≡ y))
    → ℕ → (A → A) → A → A
  iterateFix eq? zero f x = x
  iterateFix eq? (suc fuel) f x with f x
  ... | fx with eq? fx x
  ...   | yes _ = x
  ...   | no  _ = iterateFix eq? fuel f fx

  iterate/stable :
    ∀ {A : Set} fuel (f : A → A) x
    → f x ≡ x
    → iterate fuel f x ≡ x
  iterate/stable zero f x eq = refl
  iterate/stable (suc fuel) f x eq =
    trans (cong (iterate fuel f) eq) (iterate/stable fuel f x eq)

  iterateFix/iterate :
    ∀ {A : Set}
      (eq? : (x y : A) → Dec (x ≡ y))
      fuel (f : A → A) x
    → iterateFix eq? fuel f x ≡ iterate fuel f x
  iterateFix/iterate eq? zero f x = refl
  iterateFix/iterate eq? (suc fuel) f x with f x in fxeq
  ... | fx with eq? fx x
  ...   | yes eq =
    sym (trans (cong (iterate fuel f) eq)
               (iterate/stable fuel f x (trans fxeq eq)))
  ...   | no _ = iterateFix/iterate eq? fuel f fx

  matrix≟ :
    (G : Graph) → (left right : Matrix G) → Dec (left ≡ right)
  matrix≟ G = Vec.≡-dec (Vec.≡-dec Bool._≟_)

  approximation : (G : Graph) → Matrix G
  approximation G =
    iterateFix (matrix≟ G) (size G * size G) (refine G) (top G)

  approximation/iterate :
    ∀ {G}
    → approximation G ≡ iterate (size G * size G) (refine G) (top G)
  approximation/iterate {G} =
    iterateFix/iterate (matrix≟ G) (size G * size G) (refine G) (top G)

  bisim? : (G : Graph) → State G → State G → Bool
  bisim? G = related G (approximation G)

  Bisimilar : (G : Graph) → State G → State G → Set
  Bisimilar G s t = T (bisim? G s t)

  T∧-left : ∀ {a b} → T (a ∧ b) → T a
  T∧-left {false} ()
  T∧-left {true} _ = tt

  T∧-right : ∀ {a b} → T (a ∧ b) → T b
  T∧-right {false} ()
  T∧-right {true} proof = proof

  T∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
  T∧-intro {false} ()
  T∧-intro {true} left right = right

  T∨-cases : ∀ {a b} → T (a ∨ b) → T a ⊎ T b
  T∨-cases {false} {false} ()
  T∨-cases {false} {true} _ = inj₂ tt
  T∨-cases {true} _ = inj₁ tt

  T∨-intro : ∀ {a b} → T a ⊎ T b → T (a ∨ b)
  T∨-intro {false} (inj₁ ())
  T∨-intro {false} (inj₂ right) = right
  T∨-intro {true} _ = tt

  all/mono :
    ∀ {A : Set}
      {p q : A → Bool}
      {xs : List A}
    → (∀ x → T (p x) → T (q x))
    → T (all p xs)
    → T (all q xs)
  all/mono {xs = []} implication proof =
    tt
  all/mono {p = p} {q} {xs = x ∷ xs} implication proof =
    T∧-intro
      (implication x (T∧-left proof))
      (all/mono {p = p} {q} {xs} implication (T∧-right proof))

  any/mono :
    ∀ {A : Set}
      {p q : A → Bool}
      {xs : List A}
    → (∀ x → T (p x) → T (q x))
    → T (any p xs)
    → T (any q xs)
  any/mono {xs = []} implication ()
  any/mono {p = p} {q} {xs = x ∷ xs} implication proof
    with T∨-cases proof
  ... | inj₁ here =
    T∨-intro (inj₁ (implication x here))
  ... | inj₂ later =
    T∨-intro
      (inj₂ (any/mono {p = p} {q} {xs} implication later))

  all/intro :
    ∀ {A : Set}
      {p : A → Bool}
      {xs : List A}
    → (∀ x → x ∈ xs → T (p x))
    → T (all p xs)
  all/intro {xs = []} member =
    tt
  all/intro {p = p} {xs = x ∷ xs} member =
    T∧-intro
      (member x (Any.here refl))
      (all/intro {p = p} {xs} λ y y∈ →
        member y (Any.there y∈))

  any/intro :
    ∀ {A : Set}
      {p : A → Bool}
      {x : A}
      {xs : List A}
    → x ∈ xs
    → T (p x)
    → T (any p xs)
  any/intro (Any.here refl) proof =
    T∨-intro (inj₁ proof)
  any/intro {p = p} {xs = _ ∷ xs}
    (Any.there member) proof =
    T∨-intro
      (inj₂ (any/intro {p = p} {xs = xs} member proof))

  all/member :
    ∀ {A : Set}
      {p : A → Bool}
      {x : A}
      {xs : List A}
    → T (all p xs)
    → x ∈ xs
    → T (p x)
  all/member {xs = _ ∷ _} proof (Any.here refl) =
    T∧-left proof
  all/member {p = p} {xs = _ ∷ xs}
    proof (Any.there member) =
    all/member {p = p} {xs = xs}
      (T∧-right proof) member

  any/witness :
    ∀ {A : Set}
      {p : A → Bool}
      {xs : List A}
    → T (any p xs)
    → Σ[ x ∈ A ] x ∈ xs × T (p x)
  any/witness {xs = []} ()
  any/witness {xs = x ∷ xs} proof
    with T∨-cases proof
  ... | inj₁ here =
    x , Any.here refl , here
  ... | inj₂ later =
    let y , member , holds = any/witness later
    in y , Any.there member , holds

  related/refine :
    ∀ {G} (relation : Matrix G) (s t : State G)
    → related G (refine G relation) s t
        ≡ refineAt G relation s t
  related/refine {G} relation s t =
    trans
      (cong
        (λ row → lookup row t)
        (Vec.lookup∘tabulate
          (λ s′ → tabulate (refineAt G relation s′)) s))
      (Vec.lookup∘tabulate (refineAt G relation s) t)

  refine⇒at :
    ∀ {G}
      {relation : Matrix G}
      {s t : State G}
    → T (related G (refine G relation) s t)
    → T (refineAt G relation s t)
  refine⇒at {G} {relation} {s} {t} =
    subst T (related/refine {G = G} relation s t)

  at⇒refine :
    ∀ {G}
      {relation : Matrix G}
      {s t : State G}
    → T (refineAt G relation s t)
    → T (related G (refine G relation) s t)
  at⇒refine {G} {relation} {s} {t} =
    subst T (sym (related/refine {G = G} relation s t))

  Included : (G : Graph) → Matrix G → Matrix G → Set
  Included G left right =
    ∀ s t
    → T (related G left s t)
    → T (related G right s t)

  refine/descending :
    ∀ {G} {relation : Matrix G}
    → Included G (refine G relation) relation
  refine/descending {G} {relation} s t refined =
    T∧-left
      (refine⇒at {G = G} {relation = relation} refined)

  edgeMatches/mono :
    ∀ {G}
      {left right : Matrix G}
    → Included G left right
    → ∀ (edge edge′ : Edge (size G))
    → T (edgeMatches {G} left edge edge′)
    → T (edgeMatches {G} right edge edge′)
  edgeMatches/mono {G} inclusion (α , t) (β , u) matches =
    T∧-intro
      (T∧-left matches)
      (inclusion t u (T∧-right matches))

  simulates/mono :
    ∀ {G}
      {left right : Matrix G}
    → Included G left right
    → ∀ s t
    → T (simulates G left s t)
    → T (simulates G right s t)
  simulates/mono {G} {left} {right} inclusion s t =
    all/mono
      {p = λ edge →
        any (edgeMatches {G} left edge) (edges G t)}
      {q = λ edge →
        any (edgeMatches {G} right edge) (edges G t)}
      {xs = edges G s}
      (λ edge →
        any/mono
          {p = edgeMatches {G} left edge}
          {q = edgeMatches {G} right edge}
          {xs = edges G t}
          (edgeMatches/mono
            {G} {left} {right} inclusion edge))

  refine/mono :
    ∀ {G}
      {left right : Matrix G}
    → Included G left right
    → Included G (refine G left) (refine G right)
  refine/mono {G} {left} {right} inclusion s t refined =
    let at =
          refine⇒at {G = G} {relation = left} refined
        simulations =
          T∧-right
            {a = related G left s t}
            {b = simulates G left s t ∧ simulates G left t s}
            at
        forward = T∧-left simulations
        backward = T∧-right simulations
    in
    at⇒refine {G = G} {relation = right}
      (T∧-intro
        (inclusion s t (T∧-left at))
        (T∧-intro
          (simulates/mono
            {G} {left} {right} inclusion s t
            forward)
          (simulates/mono
            {G} {left} {right} inclusion t s
            backward)))

  Symmetric : (G : Graph) → Matrix G → Set
  Symmetric G relation =
    ∀ s t
    → T (related G relation s t)
    → T (related G relation t s)

  refine/symmetric :
    ∀ {G}
      {relation : Matrix G}
    → Symmetric G relation
    → Symmetric G (refine G relation)
  refine/symmetric {G} {relation} symmetric s t refined =
    let at =
          refine⇒at {G = G} {relation = relation} refined
        simulations =
          T∧-right
            {a = related G relation s t}
            {b = simulates G relation s t
              ∧ simulates G relation t s}
            at
    in
    at⇒refine {G = G} {relation = relation}
      (T∧-intro
        {a = related G relation t s}
        {b = simulates G relation t s
          ∧ simulates G relation s t}
        (symmetric s t (T∧-left at))
        (T∧-intro
          {a = simulates G relation t s}
          {b = simulates G relation s t}
          (T∧-right simulations)
          (T∧-left simulations)))

  iterate/symmetric :
    ∀ {G} fuel
      {relation : Matrix G}
    → Symmetric G relation
    → Symmetric G (iterate fuel (refine G) relation)
  iterate/symmetric zero symmetric =
    symmetric
  iterate/symmetric {G} (suc fuel) {relation} symmetric =
    iterate/symmetric {G} fuel
      {relation = refine G relation}
      (refine/symmetric {G} {relation} symmetric)

  related/top :
    ∀ {G} (s t : State G)
    → related G (top G) s t ≡ true
  related/top {G} s t =
    trans
      (cong
        (λ row → lookup row t)
        (Vec.lookup-replicate s
          (replicate (size G) true)))
      (Vec.lookup-replicate t true)

  SemanticContained : (G : Graph) → Matrix G → Set
  SemanticContained G relation =
    ∀ {s t}
    → BTheory._~_ (graphTheory G) s t
    → T (related G relation s t)

  top/contains : ∀ {G} → SemanticContained G (top G)
  top/contains {G} {s} {t} equivalent =
    subst T (sym (related/top {G} s t)) tt

  top/symmetric : ∀ {G} → Symmetric G (top G)
  top/symmetric {G} s t related =
    subst T (sym (related/top {G} t s)) tt

  approximation/symmetric :
    ∀ {G} → Symmetric G (approximation G)
  approximation/symmetric {G} =
    subst (Symmetric G) (sym (approximation/iterate {G}))
      (iterate/symmetric {G} (size G * size G)
        (top/symmetric {G = G}))

  bit : Bool → ℕ
  bit false = zero
  bit true = suc zero

  rowWeight : ∀ {n} → Vec Bool n → ℕ
  rowWeight V.[] = zero
  rowWeight (b V.∷ row) = bit b + rowWeight row

  matrixWeight : ∀ {m n} → Vec (Vec Bool n) m → ℕ
  matrixWeight V.[] = zero
  matrixWeight (row V.∷ rows) =
    rowWeight row + matrixWeight rows

  RowIncluded :
    ∀ {n} → Vec Bool n → Vec Bool n → Set
  RowIncluded left right =
    ∀ i → T (lookup left i) → T (lookup right i)

  RowsIncluded :
    ∀ {m n}
    → Vec (Vec Bool n) m
    → Vec (Vec Bool n) m
    → Set
  RowsIncluded left right =
    ∀ i → RowIncluded (lookup left i) (lookup right i)

  bit/mono :
    ∀ left right
    → (T left → T right)
    → bit left ≤ bit right
  bit/mono false right included = z≤n
  bit/mono true false included = ⊥-elim (included tt)
  bit/mono true true included = s≤s z≤n

  rowWeight/mono :
    ∀ {n}
      {left right : Vec Bool n}
    → RowIncluded left right
    → rowWeight left ≤ rowWeight right
  rowWeight/mono {left = V.[]} {V.[]} included =
    z≤n
  rowWeight/mono
    {left = left V.∷ lefts}
    {right V.∷ rights}
    included =
    Nat.+-mono-≤
      (bit/mono left right (included Fin.zero))
      (rowWeight/mono {left = lefts} {right = rights} λ i →
        included (Fin.suc i))

  rowWeight/strict :
    ∀ {n}
      {left right : Vec Bool n}
    → RowIncluded left right
    → left ≢ right
    → rowWeight left < rowWeight right
  rowWeight/strict {left = V.[]} {V.[]} included unequal =
    ⊥-elim (unequal refl)
  rowWeight/strict
    {left = false V.∷ lefts}
    {false V.∷ rights}
    included unequal =
    rowWeight/strict
      {left = lefts} {right = rights}
      (λ i → included (Fin.suc i))
      (λ equal → unequal (cong (false V.∷_) equal))
  rowWeight/strict
    {left = false V.∷ lefts}
    {true V.∷ rights}
    included unequal =
    s≤s
      (rowWeight/mono {left = lefts} {right = rights} λ i →
        included (Fin.suc i))
  rowWeight/strict
    {left = true V.∷ lefts}
    {false V.∷ rights}
    included unequal =
    ⊥-elim (included Fin.zero tt)
  rowWeight/strict
    {left = true V.∷ lefts}
    {true V.∷ rights}
    included unequal =
    s≤s
      (rowWeight/strict
        {left = lefts} {right = rights}
        (λ i → included (Fin.suc i))
        (λ equal → unequal (cong (true V.∷_) equal)))

  matrixWeight/mono :
    ∀ {m n}
      {left right : Vec (Vec Bool n) m}
    → RowsIncluded left right
    → matrixWeight left ≤ matrixWeight right
  matrixWeight/mono {left = V.[]} {V.[]} included =
    z≤n
  matrixWeight/mono
    {left = left V.∷ lefts}
    {right V.∷ rights}
    included =
    Nat.+-mono-≤
      (rowWeight/mono {left = left} {right = right}
        (included Fin.zero))
      (matrixWeight/mono {left = lefts} {right = rights} λ i →
        included (Fin.suc i))

  matrixWeight/strict :
    ∀ {m n}
      {left right : Vec (Vec Bool n) m}
    → RowsIncluded left right
    → left ≢ right
    → matrixWeight left < matrixWeight right
  matrixWeight/strict {left = V.[]} {V.[]} included unequal =
    ⊥-elim (unequal refl)
  matrixWeight/strict
    {left = left V.∷ lefts}
    {right V.∷ rights}
    included unequal
    with Vec.≡-dec Bool._≟_ left right
  ... | yes refl =
    Nat.+-monoʳ-< (rowWeight right)
      (matrixWeight/strict
        {left = lefts} {right = rights}
        (λ i → included (Fin.suc i))
        (λ equal → unequal (cong (right V.∷_) equal)))
  ... | no row≢ =
    Nat.+-mono-<-≤
      (rowWeight/strict
        {left = left} {right = right}
        (included Fin.zero) row≢)
      (matrixWeight/mono {left = lefts} {right = rights} λ i →
        included (Fin.suc i))

  refine/weight≤ :
    ∀ {G} {relation : Matrix G}
    → matrixWeight (refine G relation) ≤ matrixWeight relation
  refine/weight≤ {G} {relation} =
    matrixWeight/mono
      {left = refine G relation} {right = relation}
      (refine/descending {G} {relation})

  refine/weight< :
    ∀ {G} {relation : Matrix G}
    → refine G relation ≢ relation
    → matrixWeight (refine G relation) < matrixWeight relation
  refine/weight< {G} {relation} unequal =
    matrixWeight/strict
      {left = refine G relation} {right = relation}
      (refine/descending {G} {relation}) unequal

  rowWeight/true :
    ∀ n → rowWeight (replicate n true) ≡ n
  rowWeight/true zero = refl
  rowWeight/true (suc n) =
    cong suc (rowWeight/true n)

  matrixWeight/replicate :
    ∀ {n} m (row : Vec Bool n)
    → matrixWeight (replicate m row) ≡ m * rowWeight row
  matrixWeight/replicate zero row = refl
  matrixWeight/replicate (suc m) row =
    cong (rowWeight row +_) (matrixWeight/replicate m row)

  top/weight :
    ∀ {G} → matrixWeight (top G) ≡ size G * size G
  top/weight {G} =
    trans
      (matrixWeight/replicate (size G)
        (replicate (size G) true))
      (cong (size G *_) (rowWeight/true (size G)))

  Stable : (G : Graph) → Matrix G → Set
  Stable G relation = refine G relation ≡ relation

  iterate/fixed :
    ∀ {G} fuel
      {relation : Matrix G}
    → Stable G relation
    → iterate fuel (refine G) relation ≡ relation
  iterate/fixed zero stable = refl
  iterate/fixed {G} (suc fuel) {relation} stable
    rewrite stable =
    iterate/fixed {G} fuel stable

  stable/iterate :
    ∀ {G} fuel
      {relation : Matrix G}
    → Stable G relation
    → Stable G (iterate fuel (refine G) relation)
  stable/iterate {G} fuel {relation} stable =
    let fixed = iterate/fixed {G} fuel stable
    in
    trans
      (cong (refine G) fixed)
      (trans stable (sym fixed))

  <zero-elim : ∀ {n} → n < zero → ⊥
  <zero-elim ()

  stabilize :
    ∀ {G} fuel
      {relation : Matrix G}
    → matrixWeight relation ≤ fuel
    → Stable G (iterate fuel (refine G) relation)
  stabilize {G} zero {relation} bounded
    with matrix≟ G (refine G relation) relation
  ... | yes stable = stable
  ... | no unstable =
    ⊥-elim
      (<zero-elim
        (Nat.<-≤-trans
          (refine/weight< {G} {relation} unstable)
          bounded))
  stabilize {G} (suc fuel) {relation} bounded
    with matrix≟ G (refine G relation) relation
  ... | yes stable =
    stable/iterate {G} (suc fuel) stable
  ... | no unstable =
    stabilize {G} fuel
      {relation = refine G relation}
      (Nat.≤-pred
        (Nat.<-≤-trans
          (refine/weight< {G} {relation} unstable)
          bounded))

  approximation/stable :
    ∀ {G} → Stable G (approximation G)
  approximation/stable {G} =
    subst (Stable G) (sym (approximation/iterate {G}))
      (stabilize {G} (size G * size G)
        {relation = top G}
        (subst
          (λ weight → weight ≤ size G * size G)
          (sym (top/weight {G}))
          Nat.≤-refl))

  stable⇒refined :
    ∀ {G}
      {relation : Matrix G}
      {s t : State G}
    → Stable G relation
    → T (related G relation s t)
    → T (refineAt G relation s t)
  stable⇒refined {G} {relation} {s} {t} stable holds =
    refine⇒at {G = G} {relation = relation}
      (subst T
        (sym
          (cong
            (λ candidate → related G candidate s t)
            stable))
        holds)

  actionMatches/refl : ∀ α → T (actionMatches α α)
  actionMatches/refl α = fromWitness refl

  actionMatches⇒equal :
    ∀ {α β} → T (actionMatches α β) → α ≡ β
  actionMatches⇒equal = toWitness

  semantic/forth :
    ∀ {G}
      {relation : Matrix G}
      {s t : State G}
    → SemanticContained G relation
    → BTheory._~_ (graphTheory G) s t
    → T (simulates G relation s t)
  semantic/forth {G} {relation} {s} {t} contained equivalent =
    all/intro
      {p = λ edge →
        any (edgeMatches {G} relation edge) (edges G t)}
      {xs = edges G s}
      λ where
      (α , u) member →
        let v , gr , later =
              Semantic.forth G equivalent
                (listed⇒step {G = G} member)
        in
        any/intro
          {p = edgeMatches {G} relation (α , u)}
          (step⇒listed {G = G} gr)
          (T∧-intro
            (actionMatches/refl α)
            (contained later))

  semantic/back :
    ∀ {G}
      {relation : Matrix G}
      {s t : State G}
    → SemanticContained G relation
    → BTheory._~_ (graphTheory G) s t
    → T (simulates G relation t s)
  semantic/back {G} {relation} {s} {t} contained equivalent =
    semantic/forth
      {G} {relation} {s = t} {t = s}
      contained
      (Semantic.symmetric G equivalent)

  semantic/refine :
    ∀ {G}
      {relation : Matrix G}
    → SemanticContained G relation
    → SemanticContained G (refine G relation)
  semantic/refine {G} {relation} contained
    {s} {t} equivalent =
    at⇒refine {G = G} {relation = relation}
      (T∧-intro
        {a = related G relation s t}
        {b = simulates G relation s t
          ∧ simulates G relation t s}
        (contained equivalent)
        (T∧-intro
          {a = simulates G relation s t}
          {b = simulates G relation t s}
          (semantic/forth
            {G} {relation} {s} {t} contained equivalent)
          (semantic/back
            {G} {relation} {s} {t} contained equivalent)))

  iterate/contains :
    ∀ {G} fuel
      {relation : Matrix G}
    → SemanticContained G relation
    → SemanticContained G
        (iterate fuel (refine G) relation)
  iterate/contains zero contained =
    contained
  iterate/contains {G} (suc fuel) {relation} contained =
    iterate/contains {G} fuel
      {relation = refine G relation}
      (semantic/refine {G} {relation} contained)

  approximation/complete :
    ∀ {G} → SemanticContained G (approximation G)
  approximation/complete {G} =
    subst (SemanticContained G) (sym (approximation/iterate {G}))
      (iterate/contains {G} (size G * size G)
        (top/contains {G = G}))

  semantic⇒bisimilar :
    ∀ {G s t}
    → BTheory._~_ (graphTheory G) s t
    → Bisimilar G s t
  semantic⇒bisimilar {G} = approximation/complete {G = G}

  module Sound (G : Graph) where
    open BTheory (graphTheory G)
    open _≲_

    match :
      ∀ (relation : Matrix G)
        {s t : State G}
        {α : Action}
        {u : State G}
      → Stable G relation
      → T (related G relation s t)
      → BTheory._-<_>->_ (graphTheory G) s α u
      → Σ[ v ∈ State G ]
          BTheory._-<_>->_ (graphTheory G) t α v
            × T (related G relation u v)
    match relation {s} {t} {α} {u} stable holds gr =
      find
        (any/witness
          (all/member forward
            (step⇒listed {G = G} gr)))
      where
        refined =
          stable⇒refined
            {G} {relation} {s} {t} stable holds

        simulations =
          T∧-right
            {a = related G relation s t}
            {b = simulates G relation s t
              ∧ simulates G relation t s}
            refined

        forward : T (simulates G relation s t)
        forward = T∧-left simulations

        find :
          Σ[ edge ∈ Edge (size G) ]
            edge ∈ edges G t
              × T (edgeMatches {G} relation (α , u) edge)
          → Σ[ v ∈ State G ]
              BTheory._-<_>->_ (graphTheory G) t α v
                × T (related G relation u v)
        find ((β , v) , member , matches) =
          let equal =
                actionMatches⇒equal (T∧-left matches)
          in
          v
          , subst
              (λ action →
                BTheory._-<_>->_
                  (graphTheory G) t action v)
              (sym equal)
              (listed⇒step {G = G} member)
          , T∧-right matches

    mutual
      fromStable :
        ∀ (relation : Matrix G)
        → Stable G relation
        → Symmetric G relation
        → ∀ {s t}
        → T (related G relation s t)
        → s ~ t
      fromStable relation stable symmetric {s} {t} holds =
        fromStable/forward relation stable symmetric holds
        , fromStable/forward relation stable symmetric
            (symmetric s t holds)

      fromStable/forward :
        ∀ (relation : Matrix G)
        → Stable G relation
        → Symmetric G relation
        → ∀ {s t}
        → T (related G relation s t)
        → s ≲ t
      simulate
        (fromStable/forward relation stable symmetric holds)
        gr
        with match relation stable holds gr
      ... | v , gr′ , later =
        v , gr′
          , fromStable relation stable symmetric later

  approximation/sound :
    ∀ {G s t}
    → Bisimilar G s t
    → BTheory._~_ (graphTheory G) s t
  approximation/sound {G} =
    Sound.fromStable G
      (approximation G)
      (approximation/stable {G})
      (approximation/symmetric {G})

  record BisimulationCorrect (G : Graph) : Set where
    field
      sound :
        ∀ {s t}
        → Bisimilar G s t
        → BTheory._~_ (graphTheory G) s t

      complete :
        ∀ {s t}
        → BTheory._~_ (graphTheory G) s t
        → Bisimilar G s t

  open BisimulationCorrect public

  bisimulationCorrect : (G : Graph) → BisimulationCorrect G
  bisimulationCorrect G =
    record
      { sound = approximation/sound {G = G}
      ; complete = semantic⇒bisimilar {G = G}
      }
