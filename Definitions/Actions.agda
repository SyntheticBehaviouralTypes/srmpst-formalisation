open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc) renaming (_≟_ to _≟f_)
open import Data.Fin.Subset using (Subset)
open import Data.Nat using (ℕ ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec ; []; _∷_; lookup ; map; tabulate; _[_]≔_)
open import Data.Vec.Properties using (lookup-map; lookup∘update;
  lookup∘update′; lookup∘tabulate)
open import Function  using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong;
  cong₂; sym; subst; ≢-sym)
open import Relation.Nullary using (Dec; ¬_; ¬?; yes; no; contraposition)
open import Relation.Nullary.Decidable using (False; toWitnessFalse; True;
  toWitness)

open import Utils.Fin

open import Definitions.Guard
open import Definitions.Expr

module Definitions.Actions (N : ℕ) where
  open import Definitions.Common(N)

  record Comm : Set where
    constructor _⟶_
    field
      sender : Part
      receiver : Part
  
  infix 5 _⟶_

  record Choice : Set where
    constructor _<_>
    field
      {nchoices} : ℕ
      label : Fin (suc nchoices)
      sort : Sort

  infix 5 _<_>
  
  record Action : Set where
    constructor _#_
    field
      comm : Comm
      choice : Choice
  
  infix 4 _#_

  sender : Action → Part
  sender α = Comm.sender (Action.comm α)

  receiver : Action → Part
  receiver α = Comm.receiver (Action.comm α)

  nchoices : Action → ℕ
  nchoices α = Choice.nchoices (Action.choice α)

  label : (α : Action) → Fin (suc (nchoices α))
  label α = Choice.label (Action.choice α)

  sort : Action → Sort
  sort α = Choice.sort (Action.choice α)

  infix 4 _∈α_
  infix 4 _∈c_
  infix 4 _∉c_
  infix 4 _∉α_

  data _∈c_ : Part → Comm → Set where
    ∈S : ∀ {P : Part} {α : Comm} → P ≡ Comm.sender α   → P ∈c α
    ∈R : ∀ {P : Part} {α : Comm} → P ≡ Comm.receiver α → P ∈c α

  record _∉c_ (P : Part) (α : Comm) : Set where
    constructor _,_
    field
      ∉S : P ≢ Comm.sender α
      ∉R : P ≢ Comm.receiver α

  _∈α_ : Part → Action → Set
  P ∈α α = P ∈c Action.comm α

  _∉α_ : Part → Action → Set
  P ∉α α = P ∉c Action.comm α

  ∉c→¬∈c : ∀ {P α} → P ∉c α → ¬ (P ∈c α)
  ∉c→¬∈c (P≢s , P≢r) (∈S P≡s) = P≢s P≡s
  ∉c→¬∈c (P≢s , P≢r) (∈R P≡r) = P≢r P≡r

  ¬∈c→∉c : ∀ {P α} → ¬ (P ∈c α) → P ∉c α
  ¬∈c→∉c P∉ = (λ P≡s → P∉ (∈S P≡s)) , (λ P≡r → P∉ (∈R P≡r))

  infix 4 _⋄c_
  infix 4 _⋄_

  _⋄c_ : Comm → Comm → Set
  γ₁ ⋄c γ₂ =
    Comm.receiver γ₁ ∉c γ₂ ×
    Comm.receiver γ₂ ∉c γ₁

  _⋄_ : Action → Action → Set
  α₁ ⋄ α₂ = Action.comm α₁ ⋄c Action.comm α₂

  _∉c?_ : (P : Part) → (γ : Comm) → Dec (P ∉c γ)
  _∉c?_ P γ with ¬? (P ≟f Comm.sender γ) | ¬? (P ≟f Comm.receiver γ)
  ... | yes P≢s | yes P≢r = yes (P≢s , P≢r)
  ... | no ¬P≢s | _        = no  (λ { (P≢s , _) → ¬P≢s P≢s })
  ... | _        | no ¬P≢r = no  (λ { (_ , P≢r) → ¬P≢r P≢r })

  _∈c?_ : (P : Part) → (γ : Comm) → Dec (P ∈c γ)
  _∈c?_ P γ with P ≟f Comm.sender γ
  ... | yes P≡s = yes (∈S P≡s)
  ... | no P≢s with P ≟f Comm.receiver γ
  ...   | yes P≡r = yes (∈R P≡r)
  ...   | no P≢r = no λ where
          (∈S P≡s) → P≢s P≡s
          (∈R P≡r) → P≢r P≡r

  _∈α?_ : (P : Part) → (α : Action) → Dec (P ∈α α)
  _∈α?_ P α = _∈c?_ P (Action.comm α)

  _∉α?_ : (P : Part) → (α : Action) → Dec (P ∉α α)
  _∉α?_ P α = _∉c?_ P (Action.comm α)

  _⋄c?_ : (γ₁ γ₂ : Comm) → Dec (γ₁ ⋄c γ₂)
  _⋄c?_ γ₁ γ₂ with _∉c?_ (Comm.receiver γ₁) γ₂
  ... | no ¬r₁∉γ₂ = no (λ { (r₁∉γ₂ , _) → ¬r₁∉γ₂ r₁∉γ₂ })
  ... | yes r₁∉γ₂ with _∉c?_ (Comm.receiver γ₂) γ₁
  ...   | yes r₂∉γ₁ = yes (r₁∉γ₂ , r₂∉γ₁)
  ...   | no ¬r₂∉γ₁ = no (λ { (_ , r₂∉γ₁) → ¬r₂∉γ₁ r₂∉γ₁ })

  _⋄?_ : (α₁ α₂ : Action) → Dec (α₁ ⋄ α₂)
  _⋄?_ α₁ α₂ = _⋄c?_ (Action.comm α₁) (Action.comm α₂)
