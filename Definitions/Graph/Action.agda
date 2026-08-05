open import Data.Fin using (Fin)
  renaming (_≟_ to _≟Fin_)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties
  renaming (_≟_ to _≟Nat_)
open import Data.Product using (Σ; _,_)
import Data.Product.Properties as Product
open import Function using (_∘_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (yes; no)
import Relation.Nullary.Decidable as Dec

open import Definitions.Expr using (Sort; s/bool; s/nat; s/unit)

module Definitions.Graph.Action (N : ℕ) where

  open import Definitions.Actions N

  _≟Sort_ : DecidableEquality Sort
  s/bool ≟Sort s/bool = yes refl
  s/bool ≟Sort s/nat = no λ ()
  s/bool ≟Sort s/unit = no λ ()
  s/nat ≟Sort s/bool = no λ ()
  s/nat ≟Sort s/nat = yes refl
  s/nat ≟Sort s/unit = no λ ()
  s/unit ≟Sort s/bool = no λ ()
  s/unit ≟Sort s/nat = no λ ()
  s/unit ≟Sort s/unit = yes refl

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
    Product.≡-dec _≟Nat_
      (Product.≡-dec _≟Fin_ (λ _ _ → _≟Sort_ _ _))

  _≟ChoiceKey_ : DecidableEquality ChoiceKey
  _≟ChoiceKey_ = Product.≡-dec _≟Nat_ _≟Fin_

  _≟Choice_ : DecidableEquality Choice
  c ≟Choice c′ =
    Dec.map′ choiceCode-injective (cong choiceCode)
      (choiceCode c ≟ChoiceCode choiceCode c′)

  _≟Action_ : DecidableEquality Action
  (γ # c) ≟Action (γ′ # c′) with γ ≟Comm γ′
  ... | no γ≢γ′ = no (γ≢γ′ ∘ cong Action.comm)
  ... | yes refl with c ≟Choice c′
  ...   | no c≢c′ = no (c≢c′ ∘ cong Action.choice)
  ...   | yes refl = yes refl
