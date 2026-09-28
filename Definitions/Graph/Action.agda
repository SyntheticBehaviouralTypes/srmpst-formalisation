open import Data.Bool using (Bool; true; false; T; _∧_)
import Data.Bool as Bool
open import Data.Bool.Properties using (T-∧)
open import Data.Fin using (Fin; toℕ)
  renaming (_≟_ to _≟Fin_)
import Data.Fin.Properties as FinP
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as MaybeP
open import Data.Nat using (ℕ; suc; _≡ᵇ_)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ; _,_)
import Data.Product.Properties as Product
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_)
import Data.Vec.Properties as VecP
open import Function using (_∘_)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)
open import Relation.Nullary using (Dec; yes; no; ¬?)
open import Relation.Nullary.Decidable using (T?; map′; _×-dec_; _→-dec_)

open import Definitions.Expr using (Sort; s/bool; s/nat; s/unit; _≟Sort_)

module Definitions.Graph.Action (N : ℕ) where

  open import Definitions.Common N using (PartSet)
  open import Definitions.Actions N

  _≟Subset_ : DecidableEquality PartSet
  _≟Subset_ = VecP.≡-dec Bool._≟_

  _≟Shape_ : DecidableEquality Shape
  (! p) ≟Shape (! q) with p ≟Subset q
  ... | yes refl = yes refl
  ... | no p≢q   = no λ { refl → p≢q refl }
  (？ P) ≟Shape (？ Q) with P ≟Fin Q
  ... | yes refl = yes refl
  ... | no P≢Q   = no λ { refl → P≢Q refl }
  (! _) ≟Shape (？ _) = no λ ()
  (？ _) ≟Shape (! _) = no λ ()

  _≟Comm_ : DecidableEquality Comm
  _≟Comm_ = VecP.≡-dec (MaybeP.≡-dec _≟Shape_)

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
  -- `⌊ _≟Action_ ⌋`, and defining this through a bit equality (as below)
  -- made that module 10× slower to check (10 s → 110 s, 0.6 → 14 GB,
  -- measured 2026-09-25).
  _≟Event_ : DecidableEquality Event
  (sh # c) ≟Event (sh′ # c′) with sh ≟Shape sh′
  ... | no sh≢sh′ = no (sh≢sh′ ∘ cong Event.shape)
  ... | yes refl with c ≟Choice c′
  ...   | no c≢c′ = no (c≢c′ ∘ cong Event.choice)
  ...   | yes refl = yes refl

  _≟Action_ : DecidableEquality Action
  _≟Action_ = VecP.≡-dec (MaybeP.≡-dec _≟Event_)

  _⋄?_ : (α β : Action) → Dec (α ⋄ β)
  α ⋄? β =
    ¬? (α ≟Action β)
    ×-dec FinP.all? (λ Q → Recv? α Q →-dec Q ∉α? β)
    ×-dec FinP.all? (λ Q → Recv? β Q →-dec Q ∉α? α)

  -- Equalities as BITS, for the checker (`Check/Alg.agda`'s `matchEv`,
  -- `evstep?`).  A `Dec` equality matches `yes refl`, so even its yes/no
  -- tag forces the equality PROOFS (through `ℕ`, `Fin`, `Σ`); in the
  -- checker's hot loops that was most of the running time.  Here the tag
  -- is the bit, and the proof is only built if asked for (`-sound`).
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

  -- Generic bit equalities on `Vec` and `Maybe`, with their two lemmas.
  module _ {A : Set} (eq : A → A → Bool) where

    eqVec : ∀ {n} → Vec A n → Vec A n → Bool
    eqVec []       []       = true
    eqVec (x ∷ xs) (y ∷ ys) = eq x y ∧ eqVec xs ys

    eqMaybe : Maybe A → Maybe A → Bool
    eqMaybe nothing  nothing  = true
    eqMaybe (just x) (just y) = eq x y
    eqMaybe _        _        = false

    module _ (sound : ∀ x y → T (eq x y) → x ≡ y) where

      eqVec-sound : ∀ {n} (xs ys : Vec A n) → T (eqVec xs ys) → xs ≡ ys
      eqVec-sound []       []       _ = refl
      eqVec-sound (x ∷ xs) (y ∷ ys) b
        with Equivalence.to T-∧ b
      ... | bx , bs = cong₂ _∷_ (sound x y bx) (eqVec-sound xs ys bs)

      eqMaybe-sound : ∀ (x y : Maybe A) → T (eqMaybe x y) → x ≡ y
      eqMaybe-sound nothing  nothing  _ = refl
      eqMaybe-sound (just x) (just y) b = cong just (sound x y b)

    module _ (refl′ : ∀ x → T (eq x x)) where

      eqVec-refl : ∀ {n} (xs : Vec A n) → T (eqVec xs xs)
      eqVec-refl []       = tt
      eqVec-refl (x ∷ xs) = Equivalence.from T-∧ (refl′ x , eqVec-refl xs)

      eqMaybe-refl : ∀ (x : Maybe A) → T (eqMaybe x x)
      eqMaybe-refl nothing  = tt
      eqMaybe-refl (just x) = refl′ x

  eqBool : Bool → Bool → Bool
  eqBool true  true  = true
  eqBool false false = true
  eqBool _     _     = false

  eqBool-sound : ∀ x y → T (eqBool x y) → x ≡ y
  eqBool-sound true  true  _ = refl
  eqBool-sound false false _ = refl

  eqBool-refl : ∀ x → T (eqBool x x)
  eqBool-refl true  = tt
  eqBool-refl false = tt

  eqSubset : PartSet → PartSet → Bool
  eqSubset = eqVec eqBool

  eqShape : Shape → Shape → Bool
  eqShape (! p) (! q) = eqSubset p q
  eqShape (？ P) (？ Q) = eqFin P Q
  eqShape _     _     = false

  eqShape-sound : ∀ x y → T (eqShape x y) → x ≡ y
  eqShape-sound (! p) (! q) b = cong !_ (eqVec-sound eqBool eqBool-sound p q b)
  eqShape-sound (？ P) (？ Q) b = cong ？_ (eqFin-sound b)

  eqShape-refl : ∀ x → T (eqShape x x)
  eqShape-refl (! p) = eqVec-refl eqBool eqBool-refl p
  eqShape-refl (？ P) = eqFin-refl P

  eqChoice : Choice → Choice → Bool
  eqChoice (_<_> {I} i S) (_<_> {I′} i′ S′) =
    (I ≡ᵇ I′) ∧ (toℕ i ≡ᵇ toℕ i′) ∧ eqSort S S′

  eqChoice-sound : ∀ c c′ → T (eqChoice c c′) → c ≡ c′
  eqChoice-sound (_<_> {I} i S) (_<_> {I′} i′ S′) x
    with Equivalence.to T-∧ x
  ... | m , x₁ with Equivalence.to T-∧ x₁
  ... | l , s with Nat.≡ᵇ⇒≡ I I′ m
  ... | refl
    with FinP.toℕ-injective {i = i} {i′} (Nat.≡ᵇ⇒≡ (toℕ i) (toℕ i′) l)
       | eqSort-sound {S} {S′} s
  ... | refl | refl = refl

  eqChoice-refl : ∀ c → T (eqChoice c c)
  eqChoice-refl (_<_> {I} i S) =
    Equivalence.from T-∧ (Nat.≡⇒≡ᵇ I I refl ,
    Equivalence.from T-∧ (Nat.≡⇒≡ᵇ (toℕ i) (toℕ i) refl , eqSort-refl S))

  eqEvent : Event → Event → Bool
  eqEvent (sh # c) (sh′ # c′) = eqShape sh sh′ ∧ eqChoice c c′

  eqEvent-sound : ∀ e e′ → T (eqEvent e e′) → e ≡ e′
  eqEvent-sound (sh # c) (sh′ # c′) x
    with Equivalence.to T-∧ x
  ... | a , b = cong₂ _#_ (eqShape-sound sh sh′ a) (eqChoice-sound c c′ b)

  eqEvent-refl : ∀ e → T (eqEvent e e)
  eqEvent-refl (sh # c) =
    Equivalence.from T-∧ (eqShape-refl sh , eqChoice-refl c)

  eqMaybeEvent : Maybe Event → Maybe Event → Bool
  eqMaybeEvent = eqMaybe eqEvent

  eqMaybeEvent-sound : ∀ x y → T (eqMaybeEvent x y) → x ≡ y
  eqMaybeEvent-sound = eqMaybe-sound eqEvent eqEvent-sound

  eqMaybeEvent-refl : ∀ x → T (eqMaybeEvent x x)
  eqMaybeEvent-refl = eqMaybe-refl eqEvent eqEvent-refl
