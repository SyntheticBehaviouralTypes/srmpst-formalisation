open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin) renaming (_≟_ to _≟f_)
open import Data.Fin.Subset using (_∈_; _∉_; ⁅_⁆)
open import Data.Fin.Subset.Properties using (_∈?_; x∈⁅x⁆; x∈⁅y⁆⇒x≡y)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᵐ)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; lookup; tabulate; map)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; ¬_; ¬?; yes; no)
open import Relation.Nullary.Decidable using (_×?_; _→?_)
import Data.Fin.Properties as FinP
open import Definitions.Expr using (Sort)

module Definitions.Actions (N : ℕ) where
  open import Definitions.Common(N)

  record Choice : Set where
    constructor _<_>
    field
      {nchoices} : ℕ
      label : Fin (suc nchoices)
      sort : Sort

  infix 5 _<_>

  -- A send to a set of receivers, or a receive from one sender.  `？` is
  -- U+FF1F.
  data Shape : Set where
    !_ : PartSet → Shape
    ？_ : Part → Shape

  infix 6 !_ ？_

  record Event : Set where
    constructor _#_
    field
      shape : Shape
      choice : Choice

  -- Between _≡_ (4) and _<_> (5), so `e ≡ (! Qs) # i < S >` parses.
  infix 4.5 _#_

  -- One event per participant.
  Action : Set
  Action = Vec (Maybe Event) N

  Comm : Set
  Comm = Vec (Maybe Shape) N

  ev : Action → Part → Maybe Event
  ev α P = lookup α P

  comm : Action → Comm
  comm = map (mapᵐ Event.shape)

  nchoices : Event → ℕ
  nchoices e = Choice.nchoices (Event.choice e)

  private
    nothing≢just : ∀ {A : Set} {x : A} → nothing ≢ just x
    nothing≢just ()

    maybe-cases : ∀ {A : Set} (m : Maybe A) → m ≡ nothing ⊎ ∃[ x ] m ≡ just x
    maybe-cases nothing  = inj₁ refl
    maybe-cases (just x) = inj₂ (x , refl)

  infix 4 _∈α_ _∉α_

  _∈α_ : Part → Action → Set
  P ∈α α = ∃[ e ] ev α P ≡ just e

  _∉α_ : Part → Action → Set
  P ∉α α = ev α P ≡ nothing

  ∉α→¬∈α : ∀ {P α} → P ∉α α → ¬ P ∈α α
  ∉α→¬∈α P∉ (e , eq) = nothing≢just (trans (sym P∉) eq)

  ¬∈α→∉α : ∀ {P α} → ¬ P ∈α α → P ∉α α
  ¬∈α→∉α {P} {α} ¬∈ with maybe-cases (ev α P)
  ... | inj₁ eq = eq
  ... | inj₂ p  = ⊥-elim (¬∈ p)

  _∈α?_ : (P : Part) → (α : Action) → Dec (P ∈α α)
  P ∈α? α with maybe-cases (ev α P)
  ... | inj₁ eq = no (∉α→¬∈α {P} {α} eq)
  ... | inj₂ p  = yes p

  _∉α?_ : (P : Part) → (α : Action) → Dec (P ∉α α)
  P ∉α? α with maybe-cases (ev α P)
  ... | inj₁ eq = yes eq
  ... | inj₂ p  = no (λ eq → ∉α→¬∈α {P} {α} eq p)

  -- A role of `Ps` takes part; no role of `Ps` does.
  _∈αˢ_ : PartSet → Action → Set
  Ps ∈αˢ α = ∃[ P ] P ∈ Ps × P ∈α α

  _∉αˢ_ : PartSet → Action → Set
  Ps ∉αˢ α = ∀ P → P ∈ Ps → P ∉α α

  infix 4 _∈αˢ_ _∉αˢ_

  ∉αˢ→¬∈αˢ : ∀ {Ps α} → Ps ∉αˢ α → ¬ Ps ∈αˢ α
  ∉αˢ→¬∈αˢ {α = α} Ps∉ (P , P∈ , P∈α) = ∉α→¬∈α {P} {α} (Ps∉ P P∈) P∈α

  ¬∈αˢ→∉αˢ : ∀ {Ps α} → ¬ Ps ∈αˢ α → Ps ∉αˢ α
  ¬∈αˢ→∉αˢ {α = α} ¬∈ P P∈ = ¬∈α→∉α {P} {α} λ P∈α → ¬∈ (P , P∈ , P∈α)

  _∈αˢ?_ : (Ps : PartSet) → (α : Action) → Dec (Ps ∈αˢ α)
  Ps ∈αˢ? α = FinP.any? λ P → (P ∈? Ps) ×? (P ∈α? α)

  _∉αˢ?_ : (Ps : PartSet) → (α : Action) → Dec (Ps ∉αˢ α)
  Ps ∉αˢ? α = FinP.all? λ P → (P ∈? Ps) →? (P ∉α? α)

  -- A single role is the singleton set.
  ∈α→∈αˢ⁅⁆ : ∀ {P α} → P ∈α α → ⁅ P ⁆ ∈αˢ α
  ∈α→∈αˢ⁅⁆ {P} P∈α = P , x∈⁅x⁆ P , P∈α

  ∉α→∉αˢ⁅⁆ : ∀ {P α} → P ∉α α → ⁅ P ⁆ ∉αˢ α
  ∉α→∉αˢ⁅⁆ {P} P∉ X X∈ with x∈⁅y⁆⇒x≡y P X∈
  ... | refl = P∉

  -- An action in which `P` acts differs from one in which it does not.
  ∈∉→≢ : ∀ {P α β} → P ∈α α → P ∉α β → α ≢ β
  ∈∉→≢ {P} {α} P∈α P∉β refl = ∉α→¬∈α {P} {α} P∉β P∈α

  Recv : Action → Part → Set
  Recv α Q = ∃[ P ] ∃[ c ] ev α Q ≡ just ((？ P) # c)

  Recv? : (α : Action) → (Q : Part) → Dec (Recv α Q)
  Recv? α Q with ev α Q
  ... | nothing           = no λ { (_ , _ , ()) }
  ... | just ((？ P) # c)  = yes (P , c , refl)
  ... | just ((! Qs) # c) = no λ { (_ , _ , ()) }

  Recv→∈α : ∀ {α Q} → Recv α Q → Q ∈α α
  Recv→∈α (_ , _ , eq) = _ , eq

  Send : Action → Part → Set
  Send α S = ∃[ Qs ] ∃[ c ] ev α S ≡ just ((! Qs) # c)

  Send? : (α : Action) → (S : Part) → Dec (Send α S)
  Send? α S with ev α S
  ... | nothing           = no λ { (_ , _ , ()) }
  ... | just ((! Qs) # c) = yes (Qs , c , refl)
  ... | just ((？ P) # c)  = no λ { (_ , _ , ()) }

  -- `α` is sent by a role outside `Q`.
  Foreign : PartSet → Action → Set
  Foreign Q α = ∃[ S ] S ∉ Q × Send α S

  Foreign? : (Q : PartSet) → (α : Action) → Dec (Foreign Q α)
  Foreign? Q α = FinP.any? λ S → ¬? (S ∈? Q) ×? Send? α S

  infix 4 _⋄_

  -- Independence: distinct actions, no receiver of either taking part in
  -- the other.
  _⋄_ : Action → Action → Set
  α ⋄ β = α ≢ β × (∀ Q → Recv α Q → Q ∉α β) × (∀ Q → Recv β Q → Q ∉α α)

  -- The balanced multicast: P sends c to every Q ∈ Qs, each receives it.
  ⟶-at : Part → PartSet → Choice → Part → Maybe Event
  ⟶-at P Qs c R with R ≟f P
  ... | yes _ = just ((! Qs) # c)
  ... | no _ with R ∈? Qs
  ...   | yes _ = just ((？ P) # c)
  ...   | no _  = nothing

  -- Likewise, so `α ≡ P ⟶ Qs # i < S >` parses.
  infix 4.5 _⟶_#_

  _⟶_#_ : Part → PartSet → Choice → Action
  P ⟶ Qs # c = tabulate (⟶-at P Qs c)

  private
    at-sender : ∀ {P Qs c} → ⟶-at P Qs c P ≡ just ((! Qs) # c)
    at-sender {P} with P ≟f P
    ... | yes _  = refl
    ... | no P≢P = ⊥-elim (P≢P refl)

    at-recv : ∀ {P Qs c R} → R ≢ P → R ∈ Qs → ⟶-at P Qs c R ≡ just ((？ P) # c)
    at-recv {P} {Qs} {R = R} R≢P R∈ with R ≟f P
    ... | yes R≡P = ⊥-elim (R≢P R≡P)
    ... | no _ with R ∈? Qs
    ...   | yes _  = refl
    ...   | no R∉ = ⊥-elim (R∉ R∈)

    at-other : ∀ {P Qs c R} → R ≢ P → R ∉ Qs → ⟶-at P Qs c R ≡ nothing
    at-other {P} {Qs} {R = R} R≢P R∉ with R ≟f P
    ... | yes R≡P = ⊥-elim (R≢P R≡P)
    ... | no _ with R ∈? Qs
    ...   | yes R∈ = ⊥-elim (R∉ R∈)
    ...   | no _   = refl

    at-inv : ∀ {P Qs c R e} → ⟶-at P Qs c R ≡ just e
           → (R ≡ P × e ≡ (! Qs) # c) ⊎ (R ≢ P × R ∈ Qs × e ≡ (？ P) # c)
    at-inv {P} {Qs} {R = R} eq with R ≟f P
    ... | yes R≡P = inj₁ (R≡P , sym (just-injective eq))
    ... | no R≢P with R ∈? Qs
    ...   | yes R∈ = inj₂ (R≢P , R∈ , sym (just-injective eq))
    ...   | no _   = ⊥-elim (nothing≢just eq)

    ev-⟶ : ∀ {P Qs c} R → ev (P ⟶ Qs # c) R ≡ ⟶-at P Qs c R
    ev-⟶ {P} {Qs} {c} R = VecP.lookup∘tabulate (⟶-at P Qs c) R

  ev-sender : ∀ {P Qs c} → ev (P ⟶ Qs # c) P ≡ just ((! Qs) # c)
  ev-sender {P} {Qs} {c} = trans (ev-⟶ P) (at-sender {P} {Qs} {c})

  ev-recv : ∀ {P Qs c R} → R ≢ P → R ∈ Qs
          → ev (P ⟶ Qs # c) R ≡ just ((？ P) # c)
  ev-recv {R = R} R≢P R∈ = trans (ev-⟶ R) (at-recv R≢P R∈)

  ev-other : ∀ {P Qs c R} → R ≢ P → R ∉ Qs → ev (P ⟶ Qs # c) R ≡ nothing
  ev-other {R = R} R≢P R∉ = trans (ev-⟶ R) (at-other R≢P R∉)

  ev-inv : ∀ {P Qs c R e} → ev (P ⟶ Qs # c) R ≡ just e
         → (R ≡ P × e ≡ (! Qs) # c) ⊎ (R ≢ P × R ∈ Qs × e ≡ (？ P) # c)
  ev-inv {R = R} eq = at-inv (trans (sym (ev-⟶ R)) eq)

  private
    shape-just : ∀ (m : Maybe Event) {sh}
               → mapᵐ Event.shape m ≡ just sh → ∃[ c ] m ≡ just (sh # c)
    shape-just (just (sh # c)) refl = c , refl

  comm-ev : ∀ {α α′ Q sh c} → comm α ≡ comm α′ → ev α Q ≡ just (sh # c)
          → ∃[ c′ ] ev α′ Q ≡ just (sh # c′)
  comm-ev {α} {α′} {Q} ceq eq = shape-just (ev α′ Q)
    (trans (sym (VecP.lookup-map Q _ α′))
    (trans (cong (λ v → lookup v Q) (sym ceq))
    (trans (VecP.lookup-map Q _ α)
           (cong (mapᵐ Event.shape) eq))))

  comm-∈α : ∀ {α α′ Q} → comm α ≡ comm α′ → Q ∈α α → Q ∈α α′
  comm-∈α ceq ((sh # c) , eq) with comm-ev ceq eq
  ... | c′ , eq′ = (sh # c′) , eq′
