{-# OPTIONS --guardedness #-}

open import Data.Bool using (Bool; T)
open import Data.Fin using (Fin)
  renaming (_≟_ to _≟Fin_)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.DecPropositional as Membership
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
import Data.Product.Properties as Product
open import Data.Vec using (Vec; lookup)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable
  using (⌊_⌋; T?; map′; fromWitness; toWitness)

open import Definitions.Behav using (BTheory)

module Definitions.Graph.Core (N : ℕ) where

  open import Definitions.Actions N
  open import Definitions.Graph.Action N

  Edge : ℕ → Set
  Edge n = Action × Fin n

  _≟Edge_ : ∀ {n} → DecidableEquality (Edge n)
  _≟Edge_ =
    Product.≡-dec _≟Action_ (λ {_} → _≟Fin_)

  record Graph : Set where
    constructor graph
    field
      size     : ℕ
      outgoing : Vec (List (Edge size)) size

  open Graph public

  State : Graph → Set
  State G = Fin (size G)

  edges : (G : Graph) → State G → List (Edge (size G))
  edges G s = lookup (outgoing G) s

  edge? : (G : Graph) → State G → Action → State G → Bool
  edge? G s α t =
    ⌊ Membership._∈?_ _≟Edge_ (α , t) (edges G s) ⌋

  infix 4 _-<_>->_

  -- Edge membership, in a record so the graph and endpoints are inferred.
  record _-<_>->_ {G : Graph} (s : State G) (α : Action) (t : State G) : Set where
    constructor gstep
    field is-edge : T (edge? G s α t)

  open _-<_>->_ public

  step? :
    (G : Graph) (s : State G) (α : Action) (t : State G)
    → Dec (_-<_>->_ {G} s α t)
  step? G s α t = map′ gstep is-edge (T? (edge? G s α t))

  listed⇒step :
    ∀ {G s α t}
    → (α , t) ∈ edges G s
    → _-<_>->_ {G} s α t
  listed⇒step m = gstep (fromWitness m)

  step⇒listed :
    ∀ {G s α t}
    → _-<_>->_ {G} s α t
    → (α , t) ∈ edges G s
  step⇒listed gr = toWitness (is-edge gr)

  graphTheory : Graph → BTheory N
  graphTheory G .BTheory.Behav = State G
  graphTheory G .BTheory._-<_>->_ = _-<_>->_ {G}
