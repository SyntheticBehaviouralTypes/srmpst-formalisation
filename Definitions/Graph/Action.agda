open import Data.Bool using (Bool; true; false; T; _∧_)
open import Data.Bool.Properties using (T-∧)
open import Data.Fin using (Fin; toℕ)
  renaming (_≟_ to _≟Fin_)
import Data.Fin.Properties as FinP
open import Data.Nat using (ℕ; suc; _≡ᵇ_)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ; _,_)
import Data.Product.Properties as Product
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (T?; map′)

open import Definitions.Expr using (Sort; s/bool; s/nat; s/unit; _≟Sort_)

module Definitions.Graph.Action (N : ℕ) where

  open import Definitions.Actions N

  _≟Comm_ : DecidableEquality Comm
  (P ⟶ Q) ≟Comm (P′ ⟶ Q′) with P ≟Fin P′
  ... | no P≢P′ = no (P≢P′ ∘ cong Comm.sender)
  ... | yes refl with Q ≟Fin Q′
  ...   | no Q≢Q′ = no (Q≢Q′ ∘ cong Comm.receiver)
  ...   | yes refl = yes refl

  ChoiceCode : Set
  ChoiceCode = Σ ℕ λ I → Σ (Fin (suc I)) λ _ → Sort

  ChoiceKey : Set
  ChoiceKey = Σ ℕ λ I → Fin (suc I)

  choiceCode : Choice → ChoiceCode
  choiceCode c =
    Choice.nchoices c , Choice.label c , Choice.sort c

  choiceKey : Choice → ChoiceKey
  choiceKey c = Choice.nchoices c , Choice.label c

  choiceFromCode : ChoiceCode → Choice
  choiceFromCode (_ , i , S) = i < S >

  choice-roundtrip : ∀ c → choiceFromCode (choiceCode c) ≡ c
  choice-roundtrip _ = refl

  choiceCode-injective :
    ∀ {c c′} → choiceCode c ≡ choiceCode c′ → c ≡ c′
  choiceCode-injective {c} {c′} eq =
    trans
      (sym (choice-roundtrip c))
      (trans (cong choiceFromCode eq) (choice-roundtrip c′))

  _≟ChoiceCode_ : DecidableEquality ChoiceCode
  _≟ChoiceCode_ =
    Product.≡-dec Nat._≟_
      (Product.≡-dec _≟Fin_ (λ _ _ → _≟Sort_ _ _))

  _≟ChoiceKey_ : DecidableEquality ChoiceKey
  _≟ChoiceKey_ = Product.≡-dec Nat._≟_ _≟Fin_

  _≟Choice_ : DecidableEquality Choice
  c ≟Choice c′ =
    map′ choiceCode-injective (cong choiceCode)
      (choiceCode c ≟ChoiceCode choiceCode c′)

  -- Structural on purpose: `Bisimulation.agda`'s `actionMatches` is
  -- `⌊ _≟Action_ ⌋`, and defining this through the bit `eqAction` below
  -- made that module 10× slower to check (10 s → 110 s, 0.6 → 14 GB,
  -- measured 2026-09-25).
  _≟Action_ : DecidableEquality Action
  (γ # c) ≟Action (γ′ # c′) with γ ≟Comm γ′
  ... | no γ≢γ′ = no (γ≢γ′ ∘ cong Action.comm)
  ... | yes refl with c ≟Choice c′
  ...   | no c≢c′ = no (c≢c′ ∘ cong Action.choice)
  ...   | yes refl = yes refl

  -- Action equality as a BIT, for the checker.  `_≟Action_` matches
  -- `yes refl`, so even its yes/no tag forces the equality PROOFS (through
  -- `ℕ`, `Fin`, `Σ`); in the checker's hot loops that was most of the
  -- running time.  Here the tag is the bit, and the proof is only built if
  -- asked for (`_≟Actionᵇ_`).
  eqFin : ∀ {m} → Fin m → Fin m → Bool
  eqFin i j = toℕ i ≡ᵇ toℕ j

  eqFin-sound : ∀ {m}{i j : Fin m} → T (eqFin i j) → i ≡ j
  eqFin-sound {i = i}{j} x = FinP.toℕ-injective (Nat.≡ᵇ⇒≡ (toℕ i) (toℕ j) x)

  eqFin-refl : ∀ {m}(i : Fin m) → T (eqFin i i)
  eqFin-refl i = Nat.≡⇒≡ᵇ (toℕ i) (toℕ i) refl

  eqSort : Sort → Sort → Bool
  eqSort s/bool s/bool = true
  eqSort s/nat  s/nat  = true
  eqSort s/unit s/unit = true
  eqSort _      _      = false

  eqSort-sound : ∀ {S S′} → T (eqSort S S′) → S ≡ S′
  eqSort-sound {s/bool} {s/bool} _ = refl
  eqSort-sound {s/nat}  {s/nat}  _ = refl
  eqSort-sound {s/unit} {s/unit} _ = refl

  eqSort-refl : ∀ S → T (eqSort S S)
  eqSort-refl s/bool = tt
  eqSort-refl s/nat  = tt
  eqSort-refl s/unit = tt

  eqAction : Action → Action → Bool
  eqAction ((P ⟶ Q) # (_<_> {I} i S)) ((P′ ⟶ Q′) # (_<_> {I′} i′ S′)) =
    eqFin P P′ ∧ eqFin Q Q′ ∧ (I ≡ᵇ I′) ∧ (toℕ i ≡ᵇ toℕ i′) ∧ eqSort S S′

  eqAction-sound : ∀ α β → T (eqAction α β) → α ≡ β
  eqAction-sound ((P ⟶ Q) # (_<_> {I} i S)) ((P′ ⟶ Q′) # (_<_> {I′} i′ S′)) x
    with Equivalence.to T-∧ x
  ... | p , x₁ with Equivalence.to T-∧ x₁
  ... | q , x₂ with Equivalence.to T-∧ x₂
  ... | m , x₃ with Equivalence.to T-∧ x₃
  ... | l , s
    with eqFin-sound {i = P} {P′} p | eqFin-sound {i = Q} {Q′} q | Nat.≡ᵇ⇒≡ I I′ m
  ... | refl | refl | refl
    with FinP.toℕ-injective {i = i} {i′} (Nat.≡ᵇ⇒≡ (toℕ i) (toℕ i′) l)
       | eqSort-sound {S} {S′} s
  ... | refl | refl = refl

  eqAction-refl : ∀ α → T (eqAction α α)
  eqAction-refl ((P ⟶ Q) # (_<_> {I} i S)) =
    Equivalence.from T-∧ (eqFin-refl P ,
    Equivalence.from T-∧ (eqFin-refl Q ,
    Equivalence.from T-∧ (Nat.≡⇒≡ᵇ I I refl ,
    Equivalence.from T-∧ (Nat.≡⇒≡ᵇ (toℕ i) (toℕ i) refl , eqSort-refl S))))

  _≟Actionᵇ_ : DecidableEquality Action
  α ≟Actionᵇ β =
    map′ (eqAction-sound α β) (λ { refl → eqAction-refl α }) (T? (eqAction α β))
