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

  -- open HeadAct

  -- choice : HeadAct → Set
  -- choice x = Fin (suc (x .nchoices))

  -- data _∈pr_ P (α : HeadAct) : Set where
  --   ∈S : psender   α ≡ P → P ∈pr α
  --   ∈R : preceiver α ≡ P → P ∈pr α

  -- _∉pr_ : Part → HeadAct → Set
  -- P ∉pr α = ¬ (P ∈pr α)

  -- _∈pr?_ : ∀ P α → Dec (P ∈pr α)
  -- P ∈pr? α with psender α ≟f P
  -- ... | yes x = yes (∈S x)
  -- ... | no  x with preceiver α ≟f P
  -- ...         | yes y = yes (∈R y)
  -- ...         | no  y = no λ{ (∈S z) → x z ; (∈R z) → y z }

  -- _∉pr?_ : ∀ P α → Dec (¬ (P ∈pr α))
  -- P ∉pr? α = ¬? (P ∈pr? α)

  -- _⋏_ : HeadAct → HeadAct → Set
  -- α ⋏ α' = psender α ∈pr α' ⊎ preceiver α ∈pr α'

  -- _⋏?_ : ∀ α α' → Dec (α ⋏ α')
  -- (P ⟶ Q # _) ⋏? α with P ∈pr? α
  -- ... | yes p = yes (inj₁ p)
  -- ... | no ¬p with Q ∈pr? α
  -- ... | yes q = yes (inj₂ q)
  -- ... | no ¬q = no (λ{ (inj₁ x) → ¬p x ; (inj₂ y) → ¬q y })

  -- ⋏sym : ∀ {α α'} → α ⋏ α' → α' ⋏ α
  -- ⋏sym (inj₁ (∈S x)) = inj₁ (∈S (sym x))
  -- ⋏sym (inj₁ (∈R x)) = inj₂ (∈S (sym x))
  -- ⋏sym (inj₂ (∈S x)) = inj₁ (∈R (sym x))
  -- ⋏sym (inj₂ (∈R x)) = inj₂ (∈R (sym x))

  -- _⋔_ : ∀ (α α' : HeadAct) → Set
  -- α ⋔ α' = ¬ (α ⋏ α')

  -- data _∥ₕ_ (α α' : HeadAct) : Set where
  --   ii-≡snd : psender α ≡ psender α' → preceiver α ≢ preceiver α' → α ∥ₕ α'
  --   ii-disj : α ⋔ α' → α ∥ₕ α'

  -- ii-snd? : ∀ {α α'}
  --   → {t1 : True (psender α ≟f psender α')}
  --   → {t2 : False (preceiver α ≟f preceiver α')}
  --   → α ∥ₕ α'
  -- ii-snd? {α}{_} {t}{t'} = ii-≡snd (toWitness t) (toWitnessFalse t')

  -- ii-disj? : ∀ {α α'} → {t : False (α ⋏? α')} → α ∥ₕ α'
  -- ii-disj? {α} {α′} {t} = ii-disj (toWitnessFalse t)

  -- disj?f : ∀ α α' → {t : False (α ⋏? α')} → α ⋔ α'
  -- disj?f α α′ {t} = toWitnessFalse t

  -- _∥h?_ : ∀ α α' → Dec (α ∥ₕ α')
  -- α ∥h? α' with psender α ≟f psender α'
  -- α ∥h? α' | yes refl with preceiver α ≟f preceiver α'
  -- ... | yes refl
  --   = no (λ{ (ii-≡snd refl x₁) → x₁ refl ; (ii-disj x) → x (inj₂ (∈R refl)) })
  -- ... | no ¬eq = yes (ii-≡snd refl ¬eq)
  -- α ∥h? α' | no S≢S with psender α ≟f preceiver α'
  -- ... | yes refl
  --   = no (λ{ (ii-≡snd refl x₁) → S≢S refl ; (ii-disj x) → x (inj₁ (∈R refl)) })
  -- ... | no S≢R with preceiver α ∈pr? α'
  -- ... | yes R∈α' = no (λ{ (ii-≡snd x x₁) → S≢S x ; (ii-disj x) → x (inj₂ R∈α')})
  -- ... | no R∉α' = yes (ii-disj (λ{ (inj₁ (∈S x)) → S≢S (sym x)
  --                                ; (inj₁ (∈R x)) → S≢R (sym x)
  --                                ; (inj₂ y) → R∉α' y }))

  -- ⋔sym : ∀ {p p'} → p ⋔ p' → p' ⋔ p
  -- ⋔sym d (inj₁ (∈S x)) = d (inj₁ (∈S (sym x)))
  -- ⋔sym d (inj₁ (∈R x)) = d (inj₂ (∈S (sym x)))
  -- ⋔sym d (inj₂ (∈S x)) = d (inj₁ (∈R (sym x)))
  -- ⋔sym d (inj₂ (∈R x)) = d (inj₂ (∈R (sym x)))

  -- ∥sym : ∀ {p p'} → p ∥ₕ p' → p' ∥ₕ p
  -- ∥sym (ii-≡snd x x₁) = ii-≡snd (sym x) (≢-sym x₁)
  -- ∥sym (ii-disj x) = ii-disj (⋔sym x)

  -- Action : Set
  -- Action = Σ[ p ∈ HeadAct ] choice p

  -- label : Action → Label
  -- label (p , i) = p .nchoices , i

  -- sender : Action → Part
  -- sender x = (proj₁ x) .psender

  -- receiver : Action → Part
  -- receiver x = (proj₁ x) .preceiver

  -- h/sort : (α : HeadAct) → Fin (suc (nchoices α)) → Sort
  -- h/sort p  i = lookup (sorts p) i

  -- α/sort : Action → Sort
  -- α/sort α = h/sort (proj₁ α) (proj₂ α)

  -- _∈α_ : Part → Action → Set
  -- p ∈α α = p ∈pr proj₁ α

  -- _∉α_ : Part → Action → Set
  -- P ∉α α = ¬ (P ∈pr proj₁ α)

  -- _∈α?_ : ∀ P α → Dec (P ∈α α)
  -- P ∈α? α with sender α ≟f P
  -- ... | yes x = yes (∈S x)
  -- ... | no  x with receiver α ≟f P
  -- ...         | yes y = yes (∈R y)
  -- ...         | no  y = no λ{ (∈S z) → x z ; (∈R z) → y z }

  -- _∥_ : Action → Action → Set
  -- α ∥ α' = (α .proj₁) ∥ₕ (α' .proj₁)

  -- _∦_ : Action → Action → Set
  -- α ∦ α' = ¬ (α .proj₁) ∥ₕ (α' .proj₁)

  -- Indep/gen : ∀{P Q I α}{S : Vec Sort (suc I)} → (P ⟶ Q # S) ∥ₕ α
  --     → ∀{I}{S : Vec Sort (suc I)} → (P ⟶ Q # S) ∥ₕ α
  -- Indep/gen (ii-≡snd x y) = ii-≡snd x y
  -- Indep/gen (ii-disj x) = ii-disj x

  -- -- Indep/in : ∀{P Q α α'} → P ∈pr α → Q ∈pr α → α ∥ₕ α'
  -- --   → ∀ I (i : Fin (suc I)) (S : Vec Sort (suc I)) → (P ⟶ Q # S) ∥ₕ α'

  -- nacts : Action → ℕ
  -- nacts (α , _) = nchoices α

  -- α-sorts : ∀ α → Vec Sort (suc (nacts α))
  -- α-sorts = sorts ∘ proj₁
