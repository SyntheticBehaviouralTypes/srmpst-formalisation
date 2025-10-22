{-# OPTIONS --guardedness #-}
open import Data.Bool
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; punchIn; punchOut; fromℕ)
  renaming (_≟_ to _≟f_)
open import Data.Maybe renaming (map to mmap)
open import Data.Nat using (ℕ ; zero; suc)
  renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec ; []; _∷_; lookup ; tabulate; _[_]≔_)
  renaming (map to vmap)
open import Data.Vec.Properties using (lookup-map; lookup∘update;
  lookup∘update′; lookup∘tabulate)
open import Function  using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong;
  cong₂; sym; trans; subst)
open import Relation.Nullary using (Dec; ¬_; ¬?; yes; no; contraposition;
  _because_; True)
open import Relation.Nullary.Reflects
open import Relation.Nullary.Decidable
  using (False; toWitnessFalse; fromWitnessFalse; fromWitness; toWitness)
open import Data.Maybe.Relation.Unary.Any

open import Definitions.Guard
open import Definitions.Expr
open import Definitions.Behav

module Definitions.GlobalTypesWPar (N : ℕ) where
  open import Definitions.Common(N)
  open import Definitions.Actions(N)

  module PreTypes where
    ----------------------------------------------------------------------------
    -- Global Type Syntax
    data Global (δ : ℕ) : Guard → Set where
      end : Global δ ng
      μ : Global (suc δ) mg → Global δ ng
      var : Fin δ → Global δ ng
      _⟶_∶[_]_ : (P Q : Part)
        → {I : ℕ} → Vec Sort (suc I) → Vec (Maybe (Global δ ng)) (suc I)
        → Global δ mg
      >> : Global δ mg → Global δ ng
      par : Global 0 ng → Global 0 ng → Global δ ng -- No outer recursion

    Sorts : ℕ → Set
    Sorts I = Vec Sort I

    Choice : ℕ → ℕ → Set
    Choice δ n = Vec (Maybe (Global δ ng)) n

    ----------------------------------------------------------------------------
    -- Roles in a Global Type
    --

    valid : ∀{n} → Fin n → Vec Bool n → Set
    valid zero (false ∷ v) = ⊥
    valid zero (true ∷ v) = ⊤
    valid (suc f) (x ∷ v) = valid f v

    val-eq : ∀{n}(i : Fin n)(v : Vec Bool n) → (H H' : valid i v) → H ≡ H'
    val-eq zero (true ∷ v) H H' = refl
    val-eq (suc i) (x ∷ v) H H' = val-eq i v H H'

    valid? : ∀{n}(i : Fin n)(v : Vec Bool n) → Dec (valid i v)
    valid? zero (false ∷ v) = no (λ ())
    valid? zero (true ∷ v) = true because ofʸ tt
    valid? (suc i) (x ∷ v) = valid? i v

    dom : ∀{A : Set}{I} → Vec (Maybe A) I → Vec Bool I
    dom = vmap is-just

    get : ∀{A : Set}{I}(i : Fin I)(V : Vec (Maybe A) I) → valid i (dom V) → A
    get {_}{_}(zero)(just x ∷ V) H = x
    get {_}{_}(suc i)(x ∷ V) H = get {_}{_} i V H

    defined : ∀{A I} i → Vec (Maybe A) I  → Set
    defined i v = valid i (dom v)

    -- P is a participant in G
    data _∈G_ {δ} (P : Part) : {g : Guard} → Global δ g →  Set where
      in/mu : ∀{G} → P ∈G G → P ∈G (μ G)
      in/msg/send : ∀{Q I Chs}{S : Sorts (suc I)} → P ∈G (P ⟶ Q ∶[ S ] Chs)
      in/msg/recv : ∀{Q I Chs}{S : Sorts (suc I)} → P ∈G (Q ⟶ P ∶[ S ] Chs)
      in/msg/cont/i : ∀{P' Q' I S Chs} (i : Fin (suc I))
        → (Kg : defined i Chs) → P ∈G get i Chs Kg
        → P ∈G (P' ⟶ Q' ∶[ S ] Chs)
      in/>> : ∀{G} → P ∈G G → P ∈G (>> G)
      in/par/l : ∀{G G'} → P ∈G G → P ∈G (par G G')
      in/par/r : ∀{G G'} → P ∈G G → P ∈G (par G' G)

    RoleSet : Set
    RoleSet = Part → Bool

    union : RoleSet → RoleSet → RoleSet
    union A B R = if A R then true else B R

    intersect : RoleSet → RoleSet → RoleSet
    intersect A B R = if A R then B R else false

    _subset-of_ : ∀{n} → (Fin n → Bool) → (Fin n → Bool) → Bool
    _subset-of_ {zero} P Q = true
    _subset-of_ {suc n} P Q
      = (not (P zero) ∨ Q zero) ∧ ((P ∘ suc) subset-of (Q ∘ suc))

    empty : RoleSet
    empty _ = false

    singleton : Part → RoleSet
    singleton P Q with P ≟f Q
    ... | yes _ = true
    ... | no _ = false

    x-is-x : ∀{n} (f : Fin n) → (f ≟f f) ≡ yes refl
    x-is-x f with f ≟f f
    ... | yes refl = refl
    ... | no ¬eq = ⊥-elim (¬eq refl)

    mutual
      roles : ∀{δ g} → Global δ g → RoleSet
      roles end = empty
      roles (μ G) = roles G
      roles (var x) = empty
      roles (P ⟶ Q ∶[ _ ] K)
        = union (singleton P) (union (singleton Q) (roles-cont K))
      roles (>> G) = roles G
      roles (par G G₁) = union (roles G) (roles G₁)

      roles-cont : ∀ {δ I} (K : Vec (Maybe (Global δ ng)) I) → RoleSet
      roles-cont [] = empty
      roles-cont (just x ∷ K) = union (roles x) (roles-cont K)
      roles-cont (nothing ∷ K) = roles-cont K

    mutual
      reflects-roles : ∀{δ g} (G : Global δ g)
        → ∀ P → Reflects (P ∈G G) (roles G P)
      reflects-roles end P = ofⁿ (λ ())
      reflects-roles (μ G) P with roles G P | reflects-roles G P
      ... | b | ofʸ a = ofʸ (in/mu a)
      ... | b | ofⁿ ¬a = ofⁿ λ{ (in/mu x) → ¬a x }
      reflects-roles (var x) P = ofⁿ λ ()
      reflects-roles (>> G) P with roles G P | reflects-roles G P
      ... | b | ofʸ a = ofʸ (in/>> a)
      ... | b | ofⁿ ¬a = ofⁿ λ{ (in/>> x) → ¬a x }
      reflects-roles (par G G₁) P with roles G P | reflects-roles G P
      ... | b | ofʸ a  = ofʸ (in/par/l a)
      ... | b | ofⁿ ¬a with roles G₁ P | reflects-roles G₁ P
      ... | b' | ofʸ a = ofʸ (in/par/r a)
      ... | b' | ofⁿ ¬a₁ = ofⁿ λ{ (in/par/l x) → ¬a x ; (in/par/r x) → ¬a₁ x }
      reflects-roles (P ⟶ Q ∶[ _ ] K) R with R ≟f P | R ≟f Q
      reflects-roles (P ⟶ Q ∶[ _ ] K) R | yes refl | _ rewrite x-is-x P
        = ofʸ in/msg/send
      reflects-roles (P ⟶ Q ∶[ _ ] K) R | no ¬q | yes refl with P ≟f Q
      ... | yes refl = ⊥-elim (¬q refl)
      ... | no ¬eq rewrite x-is-x Q = ofʸ in/msg/recv
      reflects-roles (P ⟶ Q ∶[ _ ] K) R | no ¬eq | no ¬eq'
        with P ≟f R | Q ≟f R
      ... | yes refl | _ = ⊥-elim (¬eq refl)
      ... | _ | yes refl = ⊥-elim (¬eq' refl)
      ... | no _ | no _ with roles-cont K R | reflects-roles-cont K R
      ... | b | ofʸ (i , j , w) = ofʸ (in/msg/cont/i i j w)
      ... | b | ofⁿ ¬a
        = ofⁿ λ{ in/msg/send → ¬eq refl
               ; in/msg/recv → ¬eq' refl
               ; (in/msg/cont/i i w x) → ¬a (i , w , x) }

      reflects-roles-cont : ∀{δ I} (K : Vec (Maybe (Global δ ng)) I) → ∀ P
        → Reflects (∃[ i ] Σ[ w ∈ defined i K ] P ∈G get i K w)
                   (roles-cont K P)
      reflects-roles-cont [] P = ofⁿ (λ ())
      reflects-roles-cont (just x ∷ K) P
        with roles x P | reflects-roles x P
      reflects-roles-cont (just x ∷ K) P | b | ofʸ a = ofʸ (zero , tt , a)
      reflects-roles-cont (just x ∷ K) P | b | ofⁿ ¬a
        with roles-cont K P | reflects-roles-cont K P
      ... | b' | ofʸ (i , P) = ofʸ (suc i , P)
      ... | b' | ofⁿ ¬a₁
        = ofⁿ (λ{ (zero , tt , w) → ¬a w
                ; (suc i , f , w) → ¬a₁ (i , f , w) })
      reflects-roles-cont (nothing ∷ K) P
        with roles-cont K P | reflects-roles-cont K P
      ... | b | ofʸ (i , P) = ofʸ (suc i , P)
      ... | b | ofⁿ ¬a = ofⁿ (λ{ (suc i , P) → ¬a (i , P) })

    _∈G?_ : ∀{δ g} P (G : Global δ g) → Dec (P ∈G G)
    P ∈G? G = roles G P because reflects-roles G P

    is-empty : ∀ {n} → (Fin n → Bool) → Bool
    is-empty {n = zero} f = true
    is-empty {n = suc n} f = not (f zero) ∧ is-empty (f ∘ suc)

    empty-false : ∀ {n} R → T (is-empty R) → ∀ (P : Fin n) → R P ≡ false
    empty-false f e zero with f zero
    empty-false f () zero | true
    empty-false f e zero | false = refl
    empty-false f e (suc P) with f zero | e
    ... | true | ()
    ... | false | e = empty-false (f ∘ suc) e P

    false-empty : ∀ {n} (R : Fin n → Bool)
      → (∀ P → R P ≡ false) → T (is-empty R)
    false-empty {zero} R f = tt
    false-empty {suc n} R f rewrite (f zero)
      = false-empty {n} (R ∘ suc) (f ∘ suc)

    reflects-empty : ∀ (R : RoleSet) → Reflects (∀ P → R P ≡ false) (is-empty R)
    reflects-empty R = fromEquivalence (empty-false R) (false-empty R)

    subset-implies : ∀ {n} (R S : Fin n → Bool)
      → T (R subset-of S) → ∀ P → T (R P) → T (S P)
    subset-implies {suc n} R S sub zero RP
      with R zero | S zero
    ... | true | true = tt
    subset-implies {suc n} R S sub (suc P) RP
      with R zero | S zero
    ... | false | _ = subset-implies (R ∘ suc) (S ∘ suc) sub P RP
    ... | true | true = subset-implies (R ∘ suc) (S ∘ suc) sub P RP

    implies-subset : ∀ {n} (R S : Fin n → Bool)
      → (∀ P → T (R P) → T (S P)) → T (R subset-of S)
    implies-subset {zero} R S f = tt
    implies-subset {suc n} R S f
      with R zero | S zero | f zero
    ... | false | _ | _ = implies-subset (R ∘ suc) (S ∘ suc) (f ∘ suc)
    ... | true | false | ff = ff tt
    ... | true | true  | _ = implies-subset (R ∘ suc) (S ∘ suc) (f ∘ suc)

    implies-reflect : ∀ (R S : RoleSet)
      → Reflects (∀ P → T (R P) → T (S P)) (R subset-of S)
    implies-reflect R S
      = fromEquivalence (subset-implies R S) (implies-subset R S)

    disj : RoleSet → RoleSet → Bool
    disj f g = is-empty (intersect f g)

    Disj : ∀{δ g δ' g'} → Global δ g → Global δ' g' → Set
    Disj G G' = ∀{P} → P ∈G G → P ∈G G' → ⊥

    Disj-sym : ∀{δ g δ' g'} (G : Global δ g)(G' : Global δ' g')
      → Disj G G' → Disj G' G
    Disj-sym = λ G G' z {P} z₁ z₂ → z z₂ z₁

    in-intersect : ∀{δ g δ' g'}{G : Global δ g}{G' : Global δ' g'} →
      (a : ∀ P → (if roles G P then roles G' P else false) ≡ false)
      → Disj G G'
    in-intersect {G = G} {G' = G'} f {P} P∈G P∈G'
      with roles G P | f P | reflects-roles G P
    ... | _ | fP | ofⁿ ¬a = ¬a P∈G
    ... | _ | fP | ofʸ _
      with roles G' P | fP | reflects-roles G' P
    ... | _ | fP | ofⁿ ¬a = ¬a P∈G'

    intersect-in : ∀{δ g δ' g'}{G : Global δ g}{G' : Global δ' g'}
      → Disj G G'
      → ∀ P → (if roles G P then roles G' P else false) ≡ false
    intersect-in {G = G} {G' = G'} C P
      with roles G P | reflects-roles G P
    ... | _ | ofⁿ ¬a = refl
    ... | _ | ofʸ a with roles G' P | reflects-roles G' P
    ... | _ | ofʸ a₁ = ⊥-elim (C a a₁)
    ... | _ | ofⁿ ¬a = refl

    reflects-disj : ∀ {δ g δ' g'} (G : Global δ g) (G' : Global δ' g')
      → Reflects (Disj G G') (disj (roles G) (roles G'))
    reflects-disj G G'
      with is-empty (intersect (roles G) (roles G'))
         | reflects-empty (intersect (roles G) (roles G'))
    ... | _ | ofʸ a = ofʸ (in-intersect a)
    ... | _ | ofⁿ ¬a = ofⁿ (¬a ∘ intersect-in)

    disj? : ∀ {δ g δ' g'} (G : Global δ g) (G' : Global δ' g') → Dec (Disj G G')
    disj? G G' = disj (roles G) (roles G') because reflects-disj G G'

    ----------------------------------------------------------------------------
    -- Well-formedness

    mutual
      well-formed : ∀{δ g} → Global δ g → Set
      well-formed end = ⊤
      well-formed (μ G) = well-formed G
      well-formed (var x) = ⊤
      -- may require: ∃[ i ] Is-just (lookup K i)
      well-formed (P ⟶ Q ∶[ S ] K) = P ≢ Q × (∃[ i ] defined i K) × wf-conts K
      well-formed (>> G) = well-formed G
      well-formed (par G G₁) = Disj G G₁ × well-formed G × well-formed G₁

      wf-conts : ∀{δ I} → Vec (Maybe (Global δ ng)) I → Set
      wf-conts [] = ⊤
      wf-conts (just x ∷ V) = well-formed x × wf-conts V
      wf-conts (nothing ∷ V) = wf-conts V

    defined? : ∀ {A : Set}{I} (m : Vec (Maybe A) I)
      → Dec (∃[ i ] valid i (dom m))
    defined? [] = no (λ ())
    defined? (just x ∷ m) = yes (zero , tt)
    defined? (nothing ∷ m) with defined? m
    ... | yes (i , j) = yes (suc i , j)
    ... | no pf = no (λ{ (suc fst , snd) → pf (fst , snd) })

    mutual
      wf? : ∀{δ g}(G : Global δ g) → Dec (well-formed G)
      wf? end = true because ofʸ tt
      wf? (μ G) = wf? G
      wf? (var x) = true because ofʸ tt
      wf? (P ⟶ Q ∶[ x ] x₁) with P ≟f Q | defined? x₁ | wf-cont? x₁
      ... | no a | yes b | yes c = true because ofʸ (a , b , c)
      ... | yes a | _ | _  = false because ofⁿ (λ z → z .proj₁ a)
      ... | _ | no a | _  = false because ofⁿ (λ z → a (z .proj₂ .proj₁))
      ... | _ | _ | no a  = false because ofⁿ (λ z → a (z .proj₂ .proj₂))
      wf? (>> G) = wf? G
      wf? (par G G₁) with disj? G G₁ | wf? G | wf? G₁
      ... | yes p | yes b | yes c = true because ofʸ (p , b , c)
      ... | no ¬p | _ | _ = no λ z → ¬p (z .proj₁)
      ... | _ | no ¬p | _ = no (λ z → ¬p (z .proj₂ .proj₁))
      ... | _ | _ | no ¬p = no (λ z → ¬p (z .proj₂ .proj₂))

      wf-cont? : ∀{δ I}(G : Choice δ I) → Dec (wf-conts G)
      wf-cont? [] = true because ofʸ tt
      wf-cont? (just x ∷ G) with wf? x | wf-cont? G
      ... | yes a | yes b = true because ofʸ (a , b)
      ... | no  a | _     = false because ofⁿ (λ z → a (z .proj₁))
      ... | _ |  no  a    = false because ofⁿ (λ z → a (z .proj₂))
      wf-cont? (nothing ∷ G) = wf-cont? G

    wf-lookup : ∀{δ I}
      → ∀ (V : Vec (Maybe (Global δ ng)) I) i (K : valid i (dom V))
      → wf-conts V → well-formed (get i V K)
    wf-lookup (just x₁ ∷ V) zero x (P , _) = P
    wf-lookup (just x₁ ∷ V) (suc i) K (_ , P) = wf-lookup V i K P
    wf-lookup (nothing ∷ V) (suc i) K P = wf-lookup V i K P

    ----------------------------------------------------------------------------
    -- Semantics

    --Substitutions

    ing : ∀{δ g} → Global δ g → Global δ ng
    ing {g = mg} G = >> G
    ing {g = ng} G = G

    ext : ∀ {δ δ'} → (rn : Fin δ → Fin δ') → Fin (suc δ) → Fin (suc δ')
    ext ρ zero = zero
    ext ρ (suc i) = suc (ρ i)

    -- a simultaneous renaming from δ to δ' vars (var for var)
    ren : (δ δ' : ℕ) -> Set
    ren δ δ' = Fin δ -> Fin δ'

    mutual
      rename : ∀ {δ δ' g} → (ρ : ren δ δ') → Global δ g → Global δ' g
      rename ρ end = end
      rename ρ (μ g) = μ (rename (ext ρ) g)
      rename ρ (var x) = var (ρ x)
      rename ρ (P ⟶ Q ∶[ S ] Ch) = P ⟶ Q ∶[ S ] rename/choice ρ Ch
      rename ρ (>> g) = >> (rename ρ g)
      rename ρ (par G G') = par G G'

      rename/choice : ∀ {δ δ' I} → ren δ δ' → Choice δ I → Choice δ' I
      rename/choice ρ [] = []
      rename/choice ρ (just x ∷ K) = just (rename ρ x) ∷ rename/choice ρ K
      rename/choice ρ (nothing ∷ K) = nothing ∷ rename/choice ρ K

    -- a simultaneous substitution from δ to δ' vars (global type for var)
    sub : (δ δ' : ℕ) -> Set
    sub δ δ' = Fin δ -> Global δ' ng

    -- Notes: Variables are ng, so substitution must keep them ng
    exts : ∀ {δ δ'}
      → (σ : sub δ δ')
        ---------------------------------
      →  sub (suc δ) (suc δ')
    exts σ zero     =  var zero
    exts σ (suc x)  =  rename suc (σ x)

    mutual
      [_]G_ : ∀ {δ δ' g} → (ρ : sub δ δ') → Global δ g → Global δ' g
      [ ρ ]G end = end
      [ ρ ]G μ G = μ ([ exts ρ ]G G)
      [ ρ ]G var x =  ρ x
      [ ρ ]G (P ⟶ Q ∶[ S ] Ch) = P ⟶ Q ∶[ S ] ([ ρ ]Ch Ch)
      [ ρ ]G >> G = >> ([ ρ ]G G)
      [ ρ ]G par G G' = par G G'

      [_]Ch_ : ∀ {δ δ' I} → (ρ : sub δ δ') → Choice δ I → Choice δ' I
      [ ρ ]Ch [] = []
      [ ρ ]Ch (just x ∷ Ch) = just ([ ρ ]G x ) ∷ ([ ρ ]Ch Ch)
      [ ρ ]Ch (nothing ∷ Ch) = nothing ∷ [ ρ ]Ch Ch

    -- cons a new type to a substitution
    add-subst : ∀ {δ δ'}
      → (σ : sub δ δ')
      → Global δ' ng
        ---------------------------------
      → sub (suc δ) δ'
    add-subst σ G zero = G
    add-subst σ G (suc i) = σ i

    [_]₀_ : ∀ {δ g} → Global δ ng → Global (suc δ) g → Global δ g
    [_]₀_ {δ} G = [ add-subst var G ]G_

    unfold/global : Global 1 mg → Global 0 mg
    unfold/global G = [ add-subst var (μ G) ]G G

    extsN : ∀ δ {δ₀ δ₁}
      → (σ : sub δ₀ δ₁)
      → sub (δ +ℕ δ₀) (δ +ℕ δ₁)
    extsN zero σ i = σ i
    extsN (suc δ) σ i = exts (extsN δ σ) i

    rename/suc/var : ∀ {δ} {G : Global δ ng} {x : Fin δ} → G ≡ var x
      → rename suc G ≡ var (suc x)
    rename/suc/var refl = refl

    subst/var/id : ∀ {δ} (x : Fin (δ +ℕ 0)) → extsN δ (λ ()) x ≡ var x
    subst/var/id {zero} ()
    subst/var/id {suc δ} zero = refl
    subst/var/id {suc δ} (suc x) = rename/suc/var (subst/var/id x)

    mutual
      subst/id : ∀ {δ g} (G : Global (δ +ℕ 0) g) → [ extsN δ (λ ()) ]G G ≡ G
      subst/id end = refl
      subst/id (μ G) = cong μ (subst/id G)
      subst/id (var x) = subst/var/id x
      subst/id (P ⟶ Q ∶[ S ] Ch) = cong (P ⟶ Q ∶[ _ ]_) (subst/Ch/id Ch)
      subst/id (>> G) = cong >> (subst/id G)
      subst/id (par G G') = refl

      subst/Ch/id : ∀ {δ I} (Ch : Choice (δ +ℕ 0) I)
        → ([ extsN δ (λ ()) ]Ch Ch) ≡ Ch
      subst/Ch/id [] = refl
      subst/Ch/id (just x ∷ Ch)
        = cong₂ _∷_ (cong just (subst/id x)) (subst/Ch/id Ch)
      subst/Ch/id (nothing ∷ Ch) = cong (_ ∷_) (subst/Ch/id Ch)

    extN : ∀ {δ δ'} δ'' → (ρ : ren δ δ')
      → ren (δ'' +ℕ δ) (δ'' +ℕ δ')
    extN zero ρ = ρ
    extN (suc n) ρ = ext (extN n ρ)

    extsN/extN/id : ∀ {δ} {G₀ : Global δ ng} δ₁ (x : Fin (δ₁ +ℕ δ))
      → extsN δ₁ (add-subst var G₀) (extN δ₁ suc x) ≡ var x
    extsN/extN/id zero x = refl
    extsN/extN/id (suc δ₁) zero = refl
    extsN/extN/id {G₀ = G₀} (suc δ₁) (suc x)
      rewrite extsN/extN/id {G₀ = G₀} δ₁ x = refl

    mutual
      subst/rename/suc : ∀ {δ g G₀} δ' (G : Global (δ' +ℕ δ) g)
        → [ extsN δ' (add-subst var G₀) ]G rename (extN δ' suc) G ≡ G
      subst/rename/suc _ end = refl
      subst/rename/suc δ (μ G) = cong μ (subst/rename/suc (suc δ) G)
      subst/rename/suc δ (var x) = extsN/extN/id δ x
      subst/rename/suc δ (_ ⟶ _ ∶[ S ] Ch) =
        cong (_ ⟶ _ ∶[ S ]_) (subst/rename/ch/suc δ Ch)
      subst/rename/suc δ (>> G) = cong >> (subst/rename/suc δ G)
      subst/rename/suc δ (par G G') = refl

      subst/rename/ch/suc : ∀ {δ I} δ₁ {G₀ : Global δ ng}
        → (Ch : Choice (δ₁ +ℕ δ) I)
        → ([ extsN δ₁ (add-subst var G₀) ]Ch rename/choice (extN δ₁ suc) Ch)
          ≡ Ch
      subst/rename/ch/suc δ₁ [] = refl
      subst/rename/ch/suc δ₁ (nothing ∷ Ch)
        = cong (_ ∷_) (subst/rename/ch/suc δ₁ Ch)
      subst/rename/ch/suc δ₁ (just x ∷ Ch)
        = cong₂ _∷_ (cong just (subst/rename/suc δ₁ x))
                    (subst/rename/ch/suc δ₁ Ch)

    extN/extN : ∀ {δ δ'} δ₁ {ρ : Fin δ → Fin δ'}
      → (x : Fin (δ₁ +ℕ δ))
      → extN δ₁ suc (extN δ₁ ρ x) ≡ extN δ₁ (ext ρ) (extN δ₁ suc x)
    extN/extN zero x = refl
    extN/extN (suc δ₁) zero = refl
    extN/extN (suc δ₁) (suc x) = cong suc (extN/extN δ₁ x)

    mutual
      rename/rename : ∀{δ δ' g} δ'' {ρ : ren δ δ'} (G : Global (δ'' +ℕ δ) g)
        → rename (extN δ'' suc) (rename (extN δ'' ρ) G)
          ≡ rename (extN δ'' (ext ρ)) (rename (extN δ'' suc) G)
      rename/rename δ end = refl
      rename/rename δ (μ G) = cong μ (rename/rename (suc δ) G)
      rename/rename δ (var x) = cong var (extN/extN δ x)
      rename/rename δ (P ⟶ Q ∶[ S ] Ch) =
        cong (P ⟶ Q ∶[ _ ]_) (rename/rename/Ch δ Ch)
      rename/rename δ (>> G) = cong >> (rename/rename δ G)
      rename/rename δ (par G G') = refl

      rename/rename/Ch : ∀ {δ δ' I} δ₁ {ρ : ren δ δ'}
        → (Ch : Choice (δ₁ +ℕ δ) I)
        → rename/choice (extN δ₁ suc) (rename/choice (extN δ₁ ρ) Ch)
          ≡ rename/choice (extN δ₁ (ext ρ)) (rename/choice (extN δ₁ suc) Ch)
      rename/rename/Ch δ₁ [] = refl
      rename/rename/Ch δ₁ (just x ∷ Ch)
        = cong₂ _∷_ (cong just (rename/rename δ₁ x)) (rename/rename/Ch δ₁ Ch)
      rename/rename/Ch δ₁ (nothing ∷ Ch)
        = cong (_ ∷_) (rename/rename/Ch δ₁ Ch)

    exts/suc : ∀ {δ} {δ'} δ₁ (x : Fin (δ₁ +ℕ δ))
      → (σ : sub δ δ')
      → (extsN δ₁(exts σ) (extN δ₁ suc x))
        ≡ rename (extN δ₁ suc) (extsN δ₁ σ x)
    exts/suc zero x σ = refl
    exts/suc (suc δ₁) zero σ = refl
    exts/suc (suc δ₁) (suc x) σ rewrite exts/suc δ₁ x σ
      = rename/rename 0 (extsN δ₁ σ x)

    mutual
      exts/rename : ∀ {δ δ' g} δ'' (G : Global (δ'' +ℕ δ) g) (σ : sub δ δ')
        → [ extsN δ'' (exts σ) ]G rename (extN δ'' suc) G
          ≡ rename (extN δ'' suc) ([ extsN δ'' σ ]G G)
      exts/rename _ end σ = refl
      exts/rename δ (μ G) σ = cong μ (exts/rename (suc δ) G σ)
      exts/rename δ (var x) σ = exts/suc δ x σ
      exts/rename δ (_ ⟶ _ ∶[ S ] Ch) σ =
        cong (_ ⟶ _ ∶[ _ ]_) (exts/rename/ch δ Ch σ)
      exts/rename δ (>> G) σ = cong >> (exts/rename δ G σ)
      exts/rename δ (par G G') σ = refl

      exts/rename/ch : ∀ {δ δ' I} δ₁(Ch : Choice (δ₁ +ℕ δ) I)
        → (σ : sub δ δ')
        → ([ extsN δ₁ (exts σ) ]Ch rename/choice (extN δ₁ suc) Ch)
          ≡ rename/choice (extN δ₁ suc) ([ extsN δ₁ σ ]Ch Ch)
      exts/rename/ch δ₁ [] _ = refl
      exts/rename/ch δ₁ (just x ∷ K) σ
        = cong₂ _∷_
                (cong just (exts/rename δ₁ x σ))
                (exts/rename/ch δ₁ K σ)
      exts/rename/ch δ₁ (nothing ∷ K) σ
        = cong (_ ∷_) (exts/rename/ch δ₁ K σ)

      add-subst/exts : ∀ {δ} {δ'} {σ : sub δ δ'}
        {G₀ : Global δ' ng} (x : Fin (suc δ))
        → ([ add-subst var G₀ ]G ([ exts σ ]G var x)) ≡ ([ add-subst σ G₀ ]G var x)
      add-subst/exts zero = refl
      add-subst/exts {σ = σ} (suc x) = subst/rename/suc 0 (σ x)

      add-subst/var/comm : ∀ {δ δ'} δ'' {σ : sub δ δ'}
        {G₀ : Global δ' ng} (x : Fin (δ'' +ℕ suc δ))
        → [ extsN δ'' (add-subst var G₀) ]G ([ extsN δ'' (exts σ) ]G var x)
          ≡ [ extsN δ'' (add-subst σ G₀) ]G var x
      add-subst/var/comm zero x = add-subst/exts x
      add-subst/var/comm (suc δ'') zero = refl
      add-subst/var/comm (suc δ'') {σ = σ} {G₀ = G₀} (suc x)
        rewrite exts/rename 0 (extsN δ'' (exts σ) x) (extsN δ'' (add-subst var G₀))
        = cong (rename suc) (add-subst/var/comm δ'' x)

      add-subst/comm : ∀ {δ δ'} δ'' {g} {σ : sub δ δ'}
        → {G₀ : Global δ' ng} (G : Global (δ'' +ℕ suc δ) g)
        → [ extsN δ'' (add-subst var G₀) ]G ([ extsN δ'' (exts σ) ]G G)
          ≡ [ extsN δ'' (add-subst σ G₀) ]G G
      add-subst/comm _ end = refl
      add-subst/comm δ (μ G) = cong μ (add-subst/comm (suc δ) G)
      add-subst/comm δ (var x) = add-subst/var/comm δ x
      add-subst/comm δ (P ⟶ Q ∶[ _ ] Ch)
        = cong (P ⟶ Q ∶[ _ ]_) (add-subst/Ch/comm δ Ch)
      add-subst/comm _ (>> G) = cong >> (add-subst/comm _ G)
      add-subst/comm _ (par G G') = refl

      add-subst/Ch/comm : ∀ {δ δ'} δ'' {I} {σ : sub δ δ'}
        {G₀ : Global δ' ng} (Ch : Choice (δ'' +ℕ suc δ) I)
        → ([ extsN δ'' (add-subst var G₀) ]Ch ([ extsN δ'' (exts σ) ]Ch Ch))
          ≡ ([ extsN δ'' (add-subst σ G₀) ]Ch Ch)
      add-subst/Ch/comm δ'' [] = refl
      add-subst/Ch/comm δ'' (just G ∷ Ch)
        = cong₂ _∷_ (cong just (add-subst/comm δ'' G))
                    (add-subst/Ch/comm δ'' Ch)
      add-subst/Ch/comm δ'' (nothing ∷ Ch)
        = cong (_ ∷_) (add-subst/Ch/comm δ'' Ch)

    -- lu/subst : ∀ {δ δ' I} (σ : sub δ δ') (Chs : Choice δ I) i
    --   → [ σ ]G (lookup Chs i) ≡ lookup ([ σ ]Ch Chs) i
    -- lu/subst σ (x ∷ Chs) zero = refl
    -- lu/subst σ (x ∷ Chs) (suc i) = lu/subst σ Chs i

    roles-impl : ∀ {n} (P Q : Fin n → Bool)
      → (Sub : (R : Fin n) → T (Q R) → T (P R))
      → ∀ b R
      → (if P R then b else false) ≡ false
      → (if Q R then b else false) ≡ false
    roles-impl P Q Sub b R with Q R | Sub R
    ... | false | s = λ z → refl
    ... | true | s with P R | s tt
    ... | true | _ = λ z → z

    to-equiv-l : ∀ {A : Set}{b : Bool} (P : T b) → Reflects A b → A
    to-equiv-l {b = b} P (ofʸ a) = a

    to-equiv-r : ∀ {A : Set}{b : Bool} (P : A) → Reflects A b → T b
    to-equiv-r {b = b} P (ofʸ a) = tt
    to-equiv-r {b = b} P (ofⁿ a) = a P

    disj-l : ∀{δ g δ' g' δ'' g''}
      → ∀ (G : Global δ g) (G' : Global δ' g') (G'' : Global δ'' g'')
      → (H : ∀{R} → R ∈G G'' → R ∈G G)
      → Disj G G' → Disj G'' G'
    disj-l G G' G'' H D  with intersect-in D
    ... | iD = in-intersect (λ P →
      roles-impl (roles G) (roles G'')
        (λ R x → to-equiv-r
          (H (to-equiv-l x (reflects-roles _ _)))
             (reflects-roles _ _))
        (roles G' P) P (iD P))

    disj-r : ∀{δ g δ' g' δ'' g''}
      → ∀ (G : Global δ g) (G' : Global δ' g') (G'' : Global δ'' g'')
      → (H : ∀{R} → R ∈G G'' → R ∈G G)
      → Disj G' G → Disj G' G''
    disj-r G G' G'' H D = Disj-sym _ _ (disj-l _ _ _ H (Disj-sym _ _ D))

  --   def-sub : ∀{δ I i G'}(K : Choice (suc δ) I) y
  --     → defined i K → defined i ([ G' / y ]K K)
  --   def-sub {i = zero} (just x₁ ∷ K) y x = just tt
  --   def-sub {i = suc i} (just x₁ ∷ K) y x = def-sub K y x
  --   def-sub {i = suc i} (nothing ∷ K) y x = def-sub K y x

    -- Pre-Transitions
    open HeadAct

    PreAction : Set
    PreAction = Σ[ α ∈ Action ]
      (Σ[ s ∈ Vec Bool (suc (nacts α)) ] valid (α .proj₂) s)

    to-action : PreAction → Action
    to-action (α , _)  = α

    hd-action : PreAction → HeadAct
    hd-action = proj₁ ∘ to-action

    asender : PreAction → Part
    asender = sender ∘ to-action

    areceiver : PreAction → Part
    areceiver = receiver ∘ to-action

    aacts : PreAction → ℕ
    aacts = nacts ∘ to-action

    -- Notes: semantics forbids to step into the continuation unless all
    -- continuations agree on which behaviours are defined
    mutual
      data _-<_>->_ : Global 0 ng → PreAction → Global 0 ng → Set where
        step/i : ∀ {P Q I S Ch} (i : Fin (suc I)) (K : valid i (dom Ch))
          → >> (P ⟶ Q ∶[ S ] Ch)
               -< (P ⟶ Q # S , i) , dom Ch , K >->
                 (get i Ch K)

        step/tl/I : ∀{α P Q I}{S : Sorts (suc I)}{Ch Ch'} →
          (P ⟶ Q # S) ⋔ (hd-action α) →
          ∃[ i ] valid i (dom Ch) →
          Ch =< α >=> Ch' →
          >> (P ⟶ Q ∶[ S ] Ch) -< α >-> >> ((P ⟶ Q ∶[ S ] Ch'))

        step/unfold : ∀{G α G'}
          → >> ([ μ G ]₀ G) -< α >-> G' → μ G -< α >-> G'

        step/parL : ∀{G α G′ G″} → G -< α >-> G′ → par G G″ -< α >-> par G′ G″
        step/parR : ∀{G α G′ G″} → G -< α >-> G′ → par G″ G -< α >-> par G″ G′

      data _=<_>=>_ : ∀{I} → Vec (Maybe (Global 0 ng)) I  → PreAction
        → Vec (Maybe (Global 0 ng)) I → Set where
        step/nil : ∀{α} → [] =< α >=> []
        step/cn : ∀{α I K K'} → _=<_>=>_ {I} K α K'
          → (nothing ∷ K) =< α >=> (nothing ∷ K')
        step/jn : ∀{α I G G' K K'} → G -< α >-> G' → _=<_>=>_ {I} K α K'
          → (just G ∷ K) =< α >=> (just G' ∷ K')

    dom-eq : ∀ {I α}{K K' : Choice 0 I} → K =< α >=> K'
      → dom K ≡ dom K'
    dom-eq step/nil = refl
    dom-eq (step/cn gr) rewrite dom-eq gr = refl
    dom-eq (step/jn x gr) rewrite dom-eq gr = refl

    mutual
      step-alt : ∀{α s i v G G′} → G -< (α , i) , s , v >-> G′
        → ∀ j (v′ : valid j s) → ∃[ G″ ] G -< (α , j) , s , v′ >-> G″
      step-alt (step/i _ _) j v = _ , step/i j v
      step-alt (step/tl/I x x₁ x₂) j v
        = _ , step/tl/I x x₁ (step-altK x₂ j v .proj₂)
      step-alt (step/unfold gr) j v = _ , step/unfold (step-alt gr j v .proj₂)
      step-alt (step/parL gr) j v = _ , step/parL (step-alt gr j v .proj₂)
      step-alt (step/parR gr) j v = _ , step/parR (step-alt gr j v .proj₂)
      step-altK : ∀{α s i v I}{G G′ : Choice 0 I} → G =< (α , i) , s , v >=> G′
        → ∀ j (v′ : valid j s) → ∃[ G″ ] G =< (α , j) , s , v′ >=> G″
      step-altK step/nil j v′ = [] , step/nil
      step-altK (step/cn x) j v′
        = _ , step/cn (step-altK x j v′ .proj₂)
      step-altK (step/jn x x₁) j v′
        = _ , step/jn (step-alt x j v′ .proj₂) (step-altK x₁ j v′ .proj₂)

    defined-rename : ∀{I δ δ'}(σ : ren δ δ')(i : Fin I) → (K : Choice δ I)
      → defined i K → defined i (rename/choice σ K)
    defined-rename σ zero (just x₁ ∷ K) x = tt
    defined-rename σ (suc i) (just x₁ ∷ K) x = defined-rename σ i K x
    defined-rename σ (suc i) (nothing ∷ K) x = defined-rename σ i K x

    defined-rename′ : ∀{I δ δ'}(σ : ren δ δ')(i : Fin I) → (K : Choice δ I)
      → defined i (rename/choice σ K) → defined i K
    defined-rename′ σ zero (just x ∷ K) d = tt
    defined-rename′ σ (suc i) (just x ∷ K) d = defined-rename′ σ i K d
    defined-rename′ σ (suc i) (nothing ∷ K) d = defined-rename′ σ i K d

    mutual
      wf-ren : ∀{δ δ' g}(σ : ren δ δ')(G : Global δ g)
        → well-formed G → well-formed (rename σ G)
      wf-ren σ end x = tt
      wf-ren σ (μ G) x = wf-ren (ext σ) G x
      wf-ren σ (var x₁) x = tt
      wf-ren σ (P ⟶ Q ∶[ x₁ ] x₂) (pnq , (i , D) , WFk)
        = pnq , (i , defined-rename σ i x₂ D) , wf-renK σ x₂ WFk
      wf-ren σ (>> G) x = wf-ren σ G x
      wf-ren σ (par G G₁) x = x

      wf-renK : ∀{I δ δ'}(σ : ren δ δ')(K : Choice δ I) →
        wf-conts K → wf-conts (rename/choice σ K)
      wf-renK σ [] x = tt
      wf-renK σ (just x₁ ∷ K) (fst , snd) = wf-ren σ x₁ fst , wf-renK  σ K snd
      wf-renK σ (nothing ∷ K) x = wf-renK σ K x

    wf-exts : ∀{δ δ'}(σ : sub δ δ')
        → (∀ i → well-formed (σ i)) → ∀ i → well-formed (exts σ i)
    wf-exts σ x zero = tt
    wf-exts σ x (suc i) = wf-ren suc (σ i) (x i)

    defined-subst : ∀{I δ δ'}(σ : sub δ δ')(i : Fin I) → (K : Choice δ I)
      → defined i K → defined i ([ σ ]Ch K)
    defined-subst σ zero (just x₁ ∷ K) x = tt
    defined-subst σ (suc i) (just x₁ ∷ K) x = defined-subst σ i K x
    defined-subst σ (suc i) (nothing ∷ K) x = defined-subst σ i K x

    defined-subst′ : ∀{I δ δ'}(σ : sub δ δ')(i : Fin I) → (K : Choice δ I)
      → defined i ([ σ ]Ch K) → defined i K
    defined-subst′ σ zero (just x₁ ∷ K) x = tt
    defined-subst′ σ (suc i) (just x₁ ∷ K) x = defined-subst′ σ i K x
    defined-subst′ σ (suc i) (nothing ∷ K) x = defined-subst′ σ i K x

    mutual
      wf-subst : ∀{δ δ' g}(σ : sub δ δ')(G : Global δ g)
        → (∀ i → well-formed (σ i)) → well-formed G → well-formed ([ σ ]G G)
      wf-subst σ end x x₁ = tt
      wf-subst σ (μ G) x x₁ = wf-subst (exts σ) G (wf-exts _ x) x₁
      wf-subst σ (var x₂) x x₁ = x x₂
      wf-subst σ (P ⟶ Q ∶[ x₂ ] K) x (pnq , (i , D) , WFK)
        = pnq , (i , defined-subst σ i K D), wf-substK σ K x WFK
      wf-subst σ (>> G) x x₁ = wf-subst σ G x x₁
      wf-subst σ (par G G₁) x x₁ = x₁

      wf-substK : ∀{δ δ' g}(σ : sub δ δ')(G : Choice δ g)
        → (∀ i → well-formed (σ i)) → wf-conts G → wf-conts ([ σ ]Ch G)
      wf-substK σ [] x x₁ = tt
      wf-substK σ (just x₂ ∷ G) x (fst , snd)
        = wf-subst σ x₂ x fst , wf-substK σ G x snd
      wf-substK σ (nothing ∷ G) x x₁ = wf-substK σ G x x₁

    wf-subst₀ : ∀{δ G′ g}(G : Global (suc δ) g)
        → well-formed G′ → well-formed G → well-formed ([ G′ ]₀ G)
    wf-subst₀ {G′ = G′} G W W'
      = wf-subst (add-subst var G′) G (λ{ zero → W ; (suc i) → tt }) W'

    mutual
      inG/rename : ∀ {P δ g} δ' {G : Global (δ' +ℕ δ) g}
        → P ∈G rename (extN δ' suc) G → P ∈G G
      inG/rename {δ = δ} δ' {G = μ G} (in/mu x) = in/mu (inG/rename (suc δ') x)
      inG/rename δ' {G = P ⟶ Q ∶[ S ] Ch} in/msg/send = in/msg/send
      inG/rename δ' {G = P ⟶ Q ∶[ S ] Ch} in/msg/recv = in/msg/recv
      inG/rename δ' {G = P ⟶ Q ∶[ S ] Ch} (in/msg/cont/i i Kg x) =
        in/msg/cont/i i (defined-rename′ (extN δ' suc) i Ch Kg)
                        (inG/rename/Ch δ' Ch i Kg x)
      inG/rename δ' {G = >> G} (in/>> x) = in/>> (inG/rename δ' x)
      inG/rename δ' {G = par G G₁} (in/par/l x) = in/par/l x
      inG/rename δ' {G = par G G₁} (in/par/r x) = in/par/r x

      inG/rename/Ch : ∀ {P δ I} δ'
        → ∀ (Ch : Choice (δ' +ℕ δ) I) (i : Fin I)
        → ∀ (Kg : defined i (rename/choice (extN δ' suc) Ch))
        → P ∈G get i _ Kg
        → P ∈G get i _ (defined-rename′ (extN δ' suc) i Ch Kg)
      inG/rename/Ch δ' (just x₁ ∷ Ch) zero _ x = inG/rename δ' x
      inG/rename/Ch δ' (just x₁ ∷ Ch) (suc i) Kg x = inG/rename/Ch δ' Ch i Kg x
      inG/rename/Ch δ' (nothing ∷ Ch) (suc i) Kg x = inG/rename/Ch δ' Ch i Kg x

    inG/ext/var : ∀ {P δ δ₁} {G' : Global δ ng} {x₁ : Fin (δ₁ +ℕ suc δ)}
      → (x : P ∈G extsN δ₁ (add-subst var G') x₁)
      → P ∈G G'
    inG/ext/var {δ₁ = zero} {x₁ = zero} x = x
    inG/ext/var {δ₁ = suc δ₁} {x₁ = suc x₁} x =
      inG/ext/var (inG/rename 0 x)
    mutual
      role-in-subst : ∀ {P δ g} {G'} δ' {G : Global (δ' +ℕ suc δ) g}
        → P ∈G ([ extsN δ' (add-subst var G') ]G G)
        → P ∈G G' ⊎ P ∈G G
      role-in-subst {G' = G'} δ {G = μ G} (in/mu x)
        with role-in-subst {G' = G'} (suc δ) {G = G} x
      ... | inj₁ i = inj₁ i
      ... | inj₂ i = inj₂ (in/mu i)
      role-in-subst δ {G = var x₁} x = inj₁ (inG/ext/var x)
      role-in-subst δ {G = P ⟶ Q ∶[ _ ] Ch} in/msg/send = inj₂ in/msg/send
      role-in-subst δ {G = P ⟶ Q ∶[ _ ] Ch} in/msg/recv = inj₂ in/msg/recv
      role-in-subst δ {G = P ⟶ Q ∶[ _ ] Ch} (in/msg/cont/i i Kg x)
        with role-in-subst/Ch δ Ch i Kg x
      ... | inj₁ i = inj₁ i
      ... | inj₂ j = inj₂ (in/msg/cont/i i (defined-subst′ _ i Ch Kg) j)
      role-in-subst δ {G = >> G} (in/>> x) with role-in-subst δ x
      ... | inj₁ i = inj₁ i
      ... | inj₂ i = inj₂ (in/>> i)
      role-in-subst δ {G = par G G₁} (in/par/l x) = inj₂ (in/par/l x) -- with role-in-subst 0 x
      role-in-subst δ {G = par G G₁} (in/par/r x) = inj₂ (in/par/r x)

      role-in-subst/Ch : ∀ {P δ I} {G'} δ'
        → (Ch : Choice (δ' +ℕ suc δ) I) (i : Fin I)
        → (Kg : defined i ([ extsN δ' (add-subst var G') ]Ch Ch))
        → P ∈G get i _ Kg
        → P ∈G G'
        ⊎ P ∈G get i _ (defined-subst′ (extsN δ' (add-subst var G')) i Ch Kg)
      role-in-subst/Ch δ' (just G ∷ Ch) zero _ x = role-in-subst δ' {G = G} x
      role-in-subst/Ch δ' (just x₁ ∷ Ch) (suc i) Kg x
        = role-in-subst/Ch δ' Ch i Kg x
      role-in-subst/Ch δ' (nothing ∷ Ch) (suc i) Kg x
        = role-in-subst/Ch δ' Ch i Kg x

    inG/fold : ∀ {P δ} {G : Global (suc δ) mg}
      → P ∈G ([ add-subst var (μ G) ]G G)
      → P ∈G μ G
    inG/fold {G = G} x with role-in-subst {G' = μ G} 0 {G = G} x
    ... | inj₁ i = i
    ... | inj₂ i = in/mu i

    just-kr : ∀{α I}{i : Fin I}{K K' : Choice 0 I} → K =< α >=> K'
      → (H : defined i K) → defined i K'
    just-kr {i = suc i} (step/cn x) H = just-kr {i = i} x H
    just-kr {i = zero} (step/jn x x₁) H = tt
    just-kr {i = suc i} (step/jn x x₁) H = just-kr {i = i} x₁ H
    just-kr′ : ∀{α I}{i : Fin I}{K K' : Choice 0 I} → K =< α >=> K'
      → defined i K' → defined i K
    just-kr′ {i = zero} (step/jn x kr) H = tt
    just-kr′ {i = suc i} (step/cn kr) H = just-kr′ {i = i} kr H
    just-kr′ {i = suc i} (step/jn x kr) H = just-kr′ {i = i} kr H

    get-kr : ∀{α I}{i : Fin I}{K K' : Choice 0 I} → K =< α >=> K'
      → (H : defined i K) → (H' : defined i K')
      → get i _ H -< α >-> get i _ H'
    get-kr {i = zero} (step/jn x kr) _ _ = x
    get-kr {i = suc i} (step/cn kr) H H' = get-kr {i = i} kr H H'
    get-kr {i = suc i} (step/jn x kr) H H' = get-kr {i = i} kr H H'

    part-in-step : ∀ {G α G'} → G -< α >-> G' → ∀{P} → P ∈G G' → P ∈G G
    part-in-step (step/i i₁ K) i = in/>> (in/msg/cont/i i₁ K i)
    part-in-step (step/unfold {G = G} gr) i
      with part-in-step gr i
    ... | in/>> ru  = inG/fold ru
    part-in-step (step/tl/I x _ x₁) (in/>> in/msg/send) = in/>> in/msg/send
    part-in-step (step/tl/I x _ x₁) (in/>> in/msg/recv) = in/>> in/msg/recv
    part-in-step (step/tl/I x _ x₁) (in/>> (in/msg/cont/i i Kg i₁))
      = in/>>
          (in/msg/cont/i i
            (just-kr′ {i = i} x₁ Kg)
            (part-in-step (get-kr {i = i} x₁ (just-kr′ {i = i} x₁ Kg) Kg) i₁))
    part-in-step (step/parL gr) (in/par/l i)
      = in/par/l (part-in-step gr i)
    part-in-step (step/parL gr) (in/par/r i) = in/par/r i
    part-in-step (step/parR gr) (in/par/l i) = in/par/l i
    part-in-step (step/parR gr) (in/par/r i)
      = in/par/r (part-in-step gr i)

    -- Transitions preserve well-formedness
    mutual
      step-wf : ∀{G α G'} → well-formed G → G -< α >-> G' → well-formed G'
      step-wf (_ , _ , wfK) (step/i {Ch = Ch} i K) = wf-lookup Ch i K wfK
      step-wf {G = μ G} wf (step/unfold gr)
        = step-wf (wf-subst₀ G wf wf) gr
      step-wf (pnq , (j , D) , wf) (step/tl/I x _ kr)
        = pnq , (j , just-kr {i = j} kr D) , stepK-wf wf kr
      step-wf (d , wfl , wfr) (step/parL st)
        = disj-l _ _ _ (part-in-step st) d , step-wf wfl st , wfr
      step-wf (d , wfl , wfr) (step/parR st)
        = disj-r _ _ _ (part-in-step st) d , wfl , step-wf wfr st
      stepK-wf : ∀{I}{G : Vec (Maybe (Global 0 ng)) I}{α G'}
        → wf-conts G → G =< α >=> G' → wf-conts G'
      stepK-wf wf step/nil = tt
      stepK-wf wf (step/cn kr) = stepK-wf wf kr
      stepK-wf (wf , kwf) (step/jn kr x) = step-wf wf kr , stepK-wf kwf x

    mutual
      in/action/global : ∀ {G G' α}
        → G -< α >-> G'
        → (asender α ∈G G) × (areceiver α ∈G G)
      in/action/global (step/i i D) = in/>> in/msg/send , in/>> in/msg/recv
      in/action/global (step/unfold x) with in/action/global x
      ... | in/>> inS , in/>> inR = inG/fold inS , inG/fold inR
      in/action/global (step/tl/I x (i , D) x₂) with in/action/choice i D x₂
      ... | l , r = in/>> (in/msg/cont/i i D l) , in/>> (in/msg/cont/i i D r)
      in/action/global (step/parL x)
        = in/par/l (in/action/global x .proj₁)
        , in/par/l (in/action/global x .proj₂)
      in/action/global (step/parR x)
        = in/par/r (in/action/global x .proj₁)
        , in/par/r (in/action/global x .proj₂)

      in/action/choice : ∀{I}{K K' : Choice 0 I}{α}
        → ∀ i (H : defined i K)
        → K =< α >=> K'
        → (asender α ∈G get i K H) × (areceiver α ∈G get i K H)
      in/action/choice zero x₂ (step/jn x x₁)
        = in/action/global x
      in/action/choice (suc i) H (step/cn x) = in/action/choice i H x
      in/action/choice (suc i) H (step/jn x x₁) = in/action/choice i H x₁

    ∈α-∈G : ∀ {G G' α P} → (G -< α >-> G' × P ∈α to-action α) → P ∈G G
    ∈α-∈G (tr , ∈S refl) = proj₁ (in/action/global tr)
    ∈α-∈G (tr , ∈R refl) = proj₂ (in/action/global tr)

    mutual
      recv-act-eq : ∀ {G α α' G' G''} → (H : well-formed G) → G -< α >-> G'
        → G -< α' >-> G'' → areceiver α ∈α to-action α'
        → proj₁ (to-action α) ≡ proj₁ (to-action α')
      recv-act-eq H (step/i i K) (step/i i₁ K₁) inα = refl
      recv-act-eq H (step/i i K) (step/tl/I x _ x₁) inα = ⊥-elim (x (inj₂ inα))
      recv-act-eq H (step/tl/I x _ x₁) (step/i i K) (∈S refl)
        = ⊥-elim (x (inj₁ (∈R refl)))
      recv-act-eq H (step/tl/I x _ x₁) (step/i i K) (∈R refl)
        = ⊥-elim (x (inj₂ (∈R refl)))
      recv-act-eq H (step/unfold {G = G} gr) (step/unfold gr') inα
        = recv-act-eq (wf-subst₀ G H H) gr gr' inα
      recv-act-eq (_ , wg , _) (step/parL gr) (step/parL gr') inα
        = recv-act-eq wg gr gr' inα
      recv-act-eq (_ , _ , wg) (step/parR gr) (step/parR gr') inα
        = recv-act-eq wg gr gr' inα
      recv-act-eq (D , _ , _) (step/parL gr) (step/parR gr') inα
        = ⊥-elim (D (∈α-∈G (gr , ∈R refl)) (∈α-∈G (gr' , inα)))
      recv-act-eq (D , _ , _) (step/parR gr) (step/parL gr') inα
        = ⊥-elim (D (∈α-∈G (gr' , inα)) (∈α-∈G (gr , ∈R refl)))
      recv-act-eq (_ , _ , H) (step/tl/I _ (j , d) kr) (step/tl/I ii' _ kr') inα
        = recv-act-eqK H j d kr kr' inα

      recv-act-eqK : ∀ {I α α'}{G G' G'' : Choice 0 I} → (H : wf-conts G)
        → ∀ j (d : defined j G)
        → G =< α >=> G' → G =< α' >=> G'' → areceiver α ∈α to-action α'
        → hd-action α ≡ hd-action α'
      recv-act-eqK (H , _) zero d (step/jn gr _) (step/jn gr' _) inα
        = recv-act-eq H gr gr' inα
      recv-act-eqK H (suc j) d (step/cn kr) (step/cn kr') inα
        = recv-act-eqK H j d kr kr' inα
      recv-act-eqK (_ , H) (suc j) d (step/jn x kr) (step/jn x₁ kr') inα
        = recv-act-eqK H j d kr kr' inα

    mutual
      snd≢rcv : ∀ {G α G'} → (H : well-formed G) → G -< α >-> G'
        → asender α ≢ areceiver α
      snd≢rcv H (step/i _ K) refl = H .proj₁ refl
      snd≢rcv H (step/unfold {G = G} gr) refl
        = snd≢rcv (wf-subst₀ G H H) gr refl
      snd≢rcv (_ , _ , H) (step/tl/I x (j , d) kr) refl = snd≢rcvK H kr j d refl
      snd≢rcv (_ , H , _) (step/parL gr) refl = snd≢rcv H gr refl
      snd≢rcv (_ , _ , H) (step/parR gr) refl = snd≢rcv H gr refl

      snd≢rcvK : ∀ {I α}{G G' : Choice 0 I} → (H : wf-conts G) → G =< α >=> G'
        → ∀ j (d : defined j G) → asender α ≢ areceiver α
      snd≢rcvK (H , _) (step/jn x x₂) zero d x₁ = snd≢rcv H x x₁
      snd≢rcvK H (step/cn x) (suc j) d x₁ = snd≢rcvK H x j d x₁
      snd≢rcvK (_ , H) (step/jn x x₂) (suc j) d x₁ = snd≢rcvK H x₂ j d x₁

    valid-eq : ∀ {I}(i : Fin I)(m : Vec Bool I)
      (K K' : valid i m)
      → K ≡ K'
    valid-eq zero (true ∷ m) K K' = refl
    valid-eq (suc i) (x ∷ m) K K' = valid-eq i m K K'

    to-witness-eq : ∀ {A : Set}{I}(i : Fin I)(m : Vec (Maybe A) I)
      (K K' : valid i (dom m))
      → get i m K ≡ get i m K'
    to-witness-eq i m K K' = cong (get i m) (valid-eq i (dom m) K K')

    mutual
      step-det  : ∀ {G α s s' G' G''} → (H : well-formed G)
        → G -< α , s >-> G' → G -< α , s' >-> G'' → G' ≡ G''
      step-det H (step/i i K) (step/i .i K₁) = to-witness-eq i _ K K₁
      step-det H (step/i i K) (step/tl/I x x₁ x₂) = ⊥-elim (x (inj₁ (∈S refl)))
      step-det H (step/unfold {G = G} gr) (step/unfold gr')
        = step-det (wf-subst₀ G H H) gr gr'
      step-det H (step/tl/I x x₁ x₂) (step/i i K) = ⊥-elim (x (inj₁ (∈S refl)))
      step-det (_ , _ , H) (step/tl/I x x₁ x₂) (step/tl/I x₃ x₄ x₅)
        = cong (λ K → >> (_ ⟶ _ ∶[ _ ] K)) (sd-cont H x₂ x₅)
      step-det H (step/parL gr) (step/parL gr')
        = cong (λ G → par G _) (step-det (H .proj₂ .proj₁) gr gr')
      step-det (D , _) (step/parL gr) (step/parR gr')
        = ⊥-elim (D (∈α-∈G (gr , ∈S refl)) (∈α-∈G (gr' , ∈S refl)))
      step-det (D , _) (step/parR gr) (step/parL gr')
        = ⊥-elim (D (∈α-∈G (gr' , ∈S refl)) (∈α-∈G (gr , ∈S refl)))
      step-det H (step/parR gr) (step/parR gr')
        = cong (λ G → par _ G) (step-det (H .proj₂ .proj₂) gr gr')

      sd-cont  : ∀ {α s s' I}{G G' G'' : Choice 0 I} → (H : wf-conts G)
        → G =< α , s >=> G' → G =< α , s' >=> G'' → G' ≡ G''
      sd-cont H step/nil step/nil = refl
      sd-cont H (step/cn kr) (step/cn kr') = cong (_ ∷_) (sd-cont H kr kr')
      sd-cont (H , H') (step/jn x kr) (step/jn x₁ kr')
        = cong₂ _∷_ (cong just (step-det H x x₁)) (sd-cont H' kr kr')

    mutual
      valid-det  : ∀ {G α i j s s' v v' G' G''} → (H : well-formed G)
        → G -< (α , i) , s , v >-> G' → G -< (α , j) , s' , v' >-> G'' → s ≡ s'
      valid-det H (step/i i K) (step/i J K₁) = refl -- cong (_ ,_) (valid-eq i _ K K₁)
      valid-det H (step/i i K) (step/tl/I x x₁ x₂) = ⊥-elim (x (inj₁ (∈S refl)))
      valid-det H (step/unfold {G = G} gr) (step/unfold gr')
        = valid-det (wf-subst₀ G H H) gr gr'
      valid-det H (step/tl/I x _ x₂) (step/i i K) = ⊥-elim (x (inj₁ (∈S refl)))
      valid-det (_ , _ , H) (step/tl/I x (i , v) x₂) (step/tl/I x₃ x₄ x₅)
        = vd-cont H i v x₂ x₅
      valid-det H (step/parL gr) (step/parL gr')
        = valid-det (H .proj₂ .proj₁) gr gr' -- cong (λ G → par G _) (valid-det (H .proj₂ .proj₁) gr gr')
      valid-det (D , _) (step/parL gr) (step/parR gr')
        = ⊥-elim (D (∈α-∈G (gr , ∈S refl)) (∈α-∈G (gr' , ∈S refl)))
      valid-det (D , _) (step/parR gr) (step/parL gr')
        = ⊥-elim (D (∈α-∈G (gr' , ∈S refl)) (∈α-∈G (gr , ∈S refl)))
      valid-det H (step/parR gr) (step/parR gr')
        = valid-det (H .proj₂ .proj₂) gr gr' -- cong (λ G → par _ G) (valid-det (H .proj₂ .proj₂) gr gr')

      vd-cont  : ∀ {α s s' a b vv vv' I}{G G' G'' : Choice 0 (suc I)} → (H : wf-conts G)
        → ∀ i (v : valid i (dom G))
        → G =< (α , a) , s , vv >=> G' → G =< (α , b) , s' , vv' >=> G'' → s ≡ s'
      vd-cont H zero v (step/jn x x₂) (step/jn x₁ x₃) = valid-det (H .proj₁) x x₁
      vd-cont {I = suc zero} H (suc zero) v (step/cn (step/jn x x₂)) (step/cn (step/jn x₁ x₃))
        = valid-det (H .proj₁) x x₁
      vd-cont {I = suc (suc I)} H (suc i) v (step/cn x) (step/cn x₁)
        = vd-cont H i v x x₁
      vd-cont {I = suc I} H (suc i) v (step/jn x x₂) (step/jn x₁ x₃)
        = valid-det (H .proj₁) x x₁

  module GT-Wrapper where

    open PreTypes
    record step G α G′ : Set where
      constructor s-do
      field
        {s-sub} : Vec Bool (suc (nacts α))
        {s-val} : valid (α .proj₂) s-sub
        s-step : G -< α , s-sub , s-val >-> G′

    PTypes : BTheory N
    PTypes .BTheory.Behav = PreTypes.Global 0 ng
    PTypes .BTheory._-<_>->_ = step

    open BTheory PTypes hiding (_-<_>->_)

    ~unfold : ∀ {G : Global 1 mg} → (μ G) ~ >> ([ add-subst var (μ G) ]G G)
    ~unfold .BTheory._~_.~L (s-do (step/unfold x)) = _ , s-do x , ~refl
    ~unfold .BTheory._~_.~R (s-do x) = _ , s-do (step/unfold x) , ~refl

    in-∈T/unfold : ∀ {P} {G : Global (suc zero) mg}
      → P ∈T >> ([ μ G ]₀ G) → P ∈T μ G
    in-∈T/unfold ii = ∈~ (~sym ~unfold) ii

    ∈T-parL : ∀ {P G G'} → (P ∈T G) → P ∈T (par G G')
    ∈T-parL (BTheory.in/α (s-do x) x₁) = in/α (s-do (step/parL x)) x₁
    ∈T-parL (BTheory.in/later (s-do x) i)
      = in/later (s-do (step/parL x)) (∈T-parL i)

    ∈T-parR : ∀ {P G G'} → (P ∈T G') → P ∈T (par G G')
    ∈T-parR (BTheory.in/α (s-do x) x₁) = in/α (s-do (step/parR x)) x₁
    ∈T-parR (BTheory.in/later (s-do x) i)
      = in/later (s-do (step/parR x)) (∈T-parR i)

    transport/∈T : ∀ {P G G'} → G ≡ G' → P ∈T G → P ∈T G'
    transport/∈T refl x = x

    mutual
      ∈G-∈T/aux : ∀ {P δ g} → {G : Global δ g}
        → well-formed G
        → P ∈G G → ∀ σ → P ∈T ([ σ ]G (ing G))
      ∈G-∈T/aux {δ = δ} {G = μ G} H (in/mu x) σ
        = in-∈T/unfold (transport/∈T (cong >> rw) inT)
        where
          rw = sym (add-subst/comm 0 G)
          inT = ∈G-∈T/aux H x (add-subst σ ([ σ ]G (μ G)))
      ∈G-∈T/aux (_ , (i , D), _) (in/msg/send {Chs = K}) σ
        = in/send (s-do (step/i i (defined-subst σ i K D)))
      ∈G-∈T/aux (_ , (i , D), _) (in/msg/recv {Chs = K}) σ
        = in/recv (s-do (step/i i (defined-subst σ i K D)))
      ∈G-∈T/aux H (in/>> x) σ = ∈G-∈T/aux H x σ
      ∈G-∈T/aux (_ , _ , W) (in/msg/cont/i {Chs = K} i Kg x) σ
        = in/later (s-do (step/i i (defined-subst σ i K Kg))) (∈G-∈T/K W i Kg x σ)
      ∈G-∈T/aux (_ , H , _) (in/par/l {G = G} x) σ
        = let rr = transport/∈T (subst/id G) (∈G-∈T/aux H x (λ ()))
          in ∈T-parL rr
      ∈G-∈T/aux (_ , _ , H) (in/par/r {G = G} x) σ
        = let rr = transport/∈T (subst/id G) (∈G-∈T/aux H x (λ ()))
          in ∈T-parR rr

      ∈G-∈T/K : ∀ {P δ I} {K : Choice δ I} (W : wf-conts K) i (Kg : defined i K)
        (x : P ∈G get i K Kg) (σ : Fin δ → Global 0 ng)
        → P ∈T get i _ (defined-subst σ i K Kg)
      ∈G-∈T/K {K = just x₁ ∷ K} W zero x₂ x σ = ∈G-∈T/aux (W .proj₁) x σ
      ∈G-∈T/K {K = just x₁ ∷ K} W (suc i) Kg x σ = ∈G-∈T/K (W .proj₂) i Kg x σ
      ∈G-∈T/K {K = nothing ∷ K} W (suc i) Kg x σ = ∈G-∈T/K W i Kg x σ

    ∈G-∈T : ∀ {P} → {G : Global 0 ng} → well-formed G → P ∈G G → P ∈T G
    ∈G-∈T H x = transport/∈T (subst/id _) (∈G-∈T/aux H x (λ ()))

    private
      mutual
        in/action/skip : ∀ {P G G'' α}
          → (inN : P ∈G G'') → (st : G -< α >-> G'')
          → P ∈G G
        in/action/skip inN (step/i i D) = in/>> (in/msg/cont/i i D inN)
        in/action/skip inN (step/unfold st) with in/action/skip inN st
        ... | in/>> rr = inG/fold rr
        in/action/skip (in/>> in/msg/send) (step/tl/I _ _ _) = in/>> in/msg/send
        in/action/skip (in/>> in/msg/recv) (step/tl/I _ _ _) = in/>> in/msg/recv
        in/action/skip (in/>> (in/msg/cont/i i Kg y)) (step/tl/I _ _ x)
          = in/>> (in/msg/cont/i i (just-kr′ {i = i} x Kg)
                     (in/action/skip/Ch i Kg (just-kr′ {i = i} x Kg) y x))
        in/action/skip (in/par/l x) (step/parL gr)
          = in/par/l (in/action/skip x gr)
        in/action/skip (in/par/r x) (step/parL gr)
          = in/par/r x
        in/action/skip (in/par/l x) (step/parR gr)
          = in/par/l x
        in/action/skip (in/par/r x) (step/parR gr)
          = in/par/r (in/action/skip x gr)

        in/action/skip/Ch : ∀ {P α I} {Ch Chs : Choice 0 I} (i : Fin I)
          → (H : defined i Chs) → (H' : defined i Ch)
          → P ∈G get i Chs H → Ch =< α >=> Chs → P ∈G get i _ H'
        in/action/skip/Ch zero x₃ x₄ x (step/jn x₁ x₂)
          = in/action/skip x x₁
        in/action/skip/Ch (suc i) H H' x (step/cn x₁)
          = in/action/skip/Ch i H H' x x₁
        in/action/skip/Ch (suc i) H H' x (step/jn x₁ x₂)
          = in/action/skip/Ch i H H' x x₂

      ∈-trace/skip : ∀ {P G G''} → (inN : P ∈G G'') → (st : G ===> G'') → P ∈G G
      ∈-trace/skip i (■ , snd) = i
      ∈-trace/skip i ((s-do x ► fst) , _ , snd)
        = in/action/skip (∈-trace/skip i (fst , snd)) x

      ∈T-∈G/aux : ∀ {P} {G : Global 0 ng} → P ∈T G → P ∈G G
      ∈T-∈G/aux (in/α (s-do x) x₁) = ∈α-∈G (x , x₁)
      ∈T-∈G/aux (in/later x tr)
        = ∈-trace/skip (∈T-∈G/aux tr) ([ x , tt ]► (■ , tt)) -- (tr/trans x tt tr/refl)

    ∈T-∈G : ∀ {P} {G : Global 0 ng} → P ∈T G → P ∈G G
    ∈T-∈G inA = ∈T-∈G/aux inA

    in/bisim : ∀ {P G G'} → well-formed G → G ~ G' → P ∈G G → P ∈G G'
    in/bisim W G~G' p∈G = ∈T-∈G (∈~ G~G' (∈G-∈T W p∈G))

    replace-s : ∀ {G α s s' v G'} v'
      → s ≡ s' → G -< α , s , v' >-> G' → G -< α , s' , v >-> G'
    replace-s {α = α} {s = s} {s' = s'} {v = v} v' refl gr
      rewrite val-eq (α .proj₂) s v v'
      = gr

    mutual
      diamond : ∀ {G α G₁ α' G₂}
        → G -< α >-> G₁ → G -< α' >-> G₂
        → (nS  : (hd-action α) ⋔ (hd-action α'))
        → ∃[ G' ] (G₁ -< α' >-> G' × G₂ -< α >-> G')
      diamond (step/i i D) (step/i i₁ D') f = ⊥-elim (f (inj₂ (∈R refl)))
      diamond (step/i i D) (step/tl/I _ _ x₂) nS
        with just-kr {i = i} x₂ D | dom-eq x₂
      ... | D' | Eq
        = _ , get-kr {i = i} x₂ D D'
            , replace-s D' (sym Eq) (step/i i D')
      diamond (step/unfold x) (step/unfold y) nS = diamond x y nS
      diamond (step/tl/I x y x₂) (step/i i D) nS
        = _ , replace-s (just-kr {i = i} x₂ D)
                        (sym (dom-eq x₂)) (step/i i (just-kr {i = i} x₂ D))
            , get-kr {i = i} x₂ D (just-kr {i = i} x₂ D)
      diamond (step/tl/I x (i , D) x₂) (step/tl/I x₃ (i' , D') x₅) nS =
        let _ , (sCh , sCh') = diamondK x₂ x₅ nS
        in _ , (step/tl/I x₃ (i , just-kr {i = i} x₂ D) sCh
             , step/tl/I x (i' , just-kr {i = i'} x₅ D') sCh')
      diamond (step/parL gr) (step/parL gr') ii with diamond gr gr' ii
      ... | _ , grl , grr = _ , step/parL grl , step/parL grr
      diamond (step/parL gr) (step/parR gr') _
        = _ , step/parR gr' , step/parL gr
      diamond (step/parR gr) (step/parL gr') _
        = _ , step/parL gr' , step/parR gr
      diamond (step/parR gr) (step/parR gr') ii with diamond gr gr' ii
      ... | _ , grl , grr = _ , step/parR grl , step/parR grr

      diamondK : ∀ {I}{G : Choice 0 I}{α G₁ α' G₂}
        → G =< α >=> G₁ → G =< α' >=> G₂
        → (nS  : (hd-action α) ⋔ (hd-action α'))
        → ∃[ G' ] (G₁ =< α' >=> G' × G₂ =< α >=> G')
      diamondK step/nil step/nil ii = [] , step/nil , step/nil
      diamondK (step/cn gr) (step/cn gr') ii
        = nothing ∷ diamondK gr gr' ii .proj₁
        , step/cn (diamondK gr gr' ii .proj₂ .proj₁)
        , step/cn (diamondK gr gr' ii .proj₂ .proj₂)
      diamondK (step/jn x gr) (step/jn x₁ gr') ii
        =  _
        , step/jn (diamond x x₁ ii .proj₂ .proj₁) (diamondK gr gr' ii .proj₂ .proj₁)
        , step/jn (diamond x x₁ ii .proj₂ .proj₂) (diamondK gr gr' ii .proj₂ .proj₂)

    mutual
      ¬Indep/≡act : ∀ {G α α' G' G''}
                  → well-formed G
                  → G -< α >-> G' → G -< α' >-> G''
                  → ¬ (hd-action α) ⋔ (hd-action α')
                  → hd-action α ≡ hd-action α'
      ¬Indep/≡act H (step/i i _) (step/i i₁ _) ii = refl -- refl
      ¬Indep/≡act H (step/i i _) (step/tl/I x _ x₁) ii = ⊥-elim (ii x)
      ¬Indep/≡act H (step/tl/I x _ x₁) (step/i i _) ii = ⊥-elim (ii (⋔sym x))
      ¬Indep/≡act H (step/unfold {G = G} gr0) (step/unfold gr1) ii
        = ¬Indep/≡act (wf-subst₀ G H H) gr0 gr1 ii
      ¬Indep/≡act H (step/tl/I x (i , D) K1) (step/tl/I _ _ K2) ii
        = ¬Indep/≡actK (H .proj₂ .proj₂) i D K1 K2 ii
      ¬Indep/≡act H (step/parL a) (step/parL b) ii = ¬Indep/≡act (H .proj₂ .proj₁) a b ii
      ¬Indep/≡act (D , _ , _) (step/parL a) (step/parR b) ii
        = ⊥-elim (ii (λ{ (inj₁ (∈S refl)) → D (∈α-∈G (a , ∈S refl)) (∈α-∈G (b , ∈S refl))
                       ; (inj₁ (∈R refl)) → D (∈α-∈G (a , ∈S refl)) (∈α-∈G (b , ∈R refl))
                       ; (inj₂ (∈S refl)) → D (∈α-∈G (a , ∈R refl)) (∈α-∈G (b , ∈S refl))
                       ; (inj₂ (∈R refl)) → D (∈α-∈G (a , ∈R refl)) (∈α-∈G (b , ∈R refl))
                       }))
      ¬Indep/≡act (D , _ , _) (step/parR a) (step/parL b) ii
        = ⊥-elim (ii (λ{ (inj₁ (∈S refl)) → D (∈α-∈G (b , ∈S refl)) (∈α-∈G (a , ∈S refl))
                       ; (inj₁ (∈R refl)) → D (∈α-∈G (b , ∈R refl)) (∈α-∈G (a , ∈S refl))
                       ; (inj₂ (∈S refl)) → D (∈α-∈G (b , ∈S refl)) (∈α-∈G (a , ∈R refl))
                       ; (inj₂ (∈R refl)) → D (∈α-∈G (b , ∈R refl)) (∈α-∈G (a , ∈R refl))
                       }))
      ¬Indep/≡act H (step/parR a) (step/parR b) ii = ¬Indep/≡act (H .proj₂ .proj₂) a b ii
        -- (step/tl/I {Ch = (_ ·· G ) ∷ _} _ (step/choice/cons sG _))
        -- (step/tl/I {Ch = (_ ·· G') ∷ _} _ (step/choice/cons sG' _)) ii
        -- = ¬Indep/≡act sG sG' ii
      ¬Indep/≡actK : ∀ {I G α α' G' G''}
                  → wf-conts G
                  → ∀ (i : Fin I) (v : valid i (dom G))
                  → G =< α >=> G' → G =< α' >=> G''
                  → ¬ (hd-action α) ⋔ (hd-action α')
                  → hd-action α ≡ hd-action α'
      ¬Indep/≡actK x zero v (step/jn x₁ x₅) (step/jn x₂ x₄) x₃
        = ¬Indep/≡act (x .proj₁) x₁ x₂ x₃
      ¬Indep/≡actK x (suc i) v (step/cn x₁) (step/cn x₂) x₃
        = ¬Indep/≡actK x i v x₁ x₂ x₃
      ¬Indep/≡actK x (suc i) v (step/jn x₁ x₄) (step/jn x₂ x₅) x₃
        = ¬Indep/≡act (x .proj₁) x₁ x₂ x₃


    step/acts/same : ∀ {G α α' G' G''}
                   → well-formed G
                   → G -< α >-> G' → G -< α' >-> G''
                   → asender α ∈α to-action α'
                   → hd-action α ≡ hd-action α'
    step/acts/same H gr gr' (∈S refl)
      = ¬Indep/≡act H gr gr' λ{ f → f (inj₁ (∈S refl)) }
    step/acts/same H gr gr' (∈R refl)
      = ¬Indep/≡act H gr gr' λ{ f → f (inj₁ (∈R refl)) }

    step/parts/det : ∀ {G α α' G' G''}
                 → well-formed G
                 → G -< α >-> G' → G -< α' >-> G''
                 → asender α ≡ asender α'
                 → hd-action α ≡ hd-action α'
    step/parts/det H gr gr' refl = step/acts/same H gr gr' (∈S refl)

    the-diamond : ∀ {G α G₁ α' G₂}
        → well-formed G
        → G -< α >-> G₁ → G -< α' >-> G₂
        → (nS  : to-action α ∥ to-action α')
        → ∃[ G' ] (G₁ -< α' >-> G' × G₂ -< α >-> G')
    the-diamond H gr gr' (ii-≡snd refl x₁)
      with step/parts/det H gr gr' refl
    ... | refl = ⊥-elim (x₁ refl)
    the-diamond H gr gr' (ii-disj x) = diamond gr gr' x

    step-cont : ∀{I α}{Ch : Choice 0 I}
      → (Kr : ∀ i v → ∃[ G ] get i Ch v -< α >-> G)
      → ∃[ Ch' ] Ch =< α >=> Ch'
    step-cont {Ch = []} Kr = [] , step/nil
    step-cont {Ch = just x ∷ Ch} Kr
      = _ , (step/jn (Kr zero tt .proj₂) (step-cont (Kr ∘ suc) .proj₂))
    step-cont {Ch = nothing ∷ Ch} Kr = _ , step/cn (step-cont (Kr ∘ suc) .proj₂)

    do-step : ∀ {G α s s' v G' G''} v'
      → s ≡ s' → G' ≡ G'' → G -< α , s , v' >-> G' → G -< α , s' , v >-> G''
    do-step {α = α} {s = s} {s' = s'} {v = v} v' refl refl gr
      rewrite val-eq (α .proj₂) s v v'
      = gr

    valid-eq-dom : ∀{I} {v v' : Vec Bool I} (e : v ≡ v') i → valid i v → valid i v'
    valid-eq-dom refl _ v = v

    alt-k : ∀{P Q I}{S : Vec Sort (suc I)}{α α'}{Ch Ch'}
      → (ii :  (P ⟶ Q # S) ⋔ hd-action α)
      → (r : Ch =< α' >=> Ch')
      → ∀ j (v : valid j (dom Ch))
      → (∀ i v → ∃[ G' ] (>> (P ⟶ Q ∶[ S ] step-altK r i v .proj₁)) -< α >-> G')
      → ∀ i v → ∃[ K' ] step-altK r i v .proj₁ =< α >=> K'
    alt-k ii r j vj x i vi with x i vi
    ... | _ , step/i i₁ K = ⊥-elim (ii (inj₂ (∈R refl)))
    ... | _ , step/tl/I x₁ x₂ x₃ = _ , x₃

    alt-parL : ∀{α α'}{G G' G''}
      → (D : Disj G G'')
      → (r : G -< α' >-> G')
      → ∀ j v {Gj}
      → step-alt r j v .proj₁ -< α >-> Gj
      → (∀ i v → ∃[ Gf ] (par (step-alt r i v .proj₁) G'') -< α >-> Gf)
      → ∀ i v → ∃[ Gf ] step-alt r i v .proj₁ -< α >-> Gf
    alt-parL D r j vv gr x i v with x i v
    ... | _ , step/parL gr' = _ , gr'
    ... | _ , step/parR gr'
      = ⊥-elim (disj-l _ _ _
                       (part-in-step (step-alt r j vv .proj₂))
                       D
                       (in/action/global gr .proj₁)
                       (in/action/global gr' .proj₁))

    alt-parR : ∀{α α'}{G G' G''}
      → (D : Disj G'' G)
      → (r : G -< α' >-> G')
      → ∀ j v {Gj}
      → step-alt r j v .proj₁ -< α >-> Gj
      → (∀ i v → ∃[ Gf ] (par  G'' (step-alt r i v .proj₁)) -< α >-> Gf)
      → ∀ i v → ∃[ Gf ] step-alt r i v .proj₁ -< α >-> Gf
    alt-parR D r j vv gr x i v with x i v
    ... | _ , step/parR gr' = _ , gr'
    ... | _ , step/parL gr'
      = ⊥-elim (disj-r _ _ _
                       (part-in-step (step-alt r j vv .proj₂))
                       D
                       (in/action/global gr' .proj₁)
                       (in/action/global gr .proj₁))

    mutual
      swap-act : ∀ { α α' G₀ G₁ }
        (H : well-formed G₀)
        (ii : (hd-action α) ⋔ (hd-action α'))
        (r : G₀ -< α >-> G₁)
        → (∀ i v → ∃[ Gi ] proj₁ (step-alt r i v) -< α' >-> Gi)
        → ∃[ G₂ ] G₀ -< α' >-> G₂
      swap-act {α} {α'} {G₀} {G₁} H ii (step/i i Kg) x
        = _ , step/tl/I ii (i , Kg) (step-cont x .proj₂)
      swap-act {α} {α'} {G₀ = μ G₀} {G₁} H ii (step/unfold r) x
        = let _ , rr = swap-act (wf-subst₀ G₀ H H) ii r x
          in _ , (step/unfold rr)
      swap-act {α} {α'} {G₀} {G₁} (_ , _ , H) ii (step/tl/I ii' (j , D) r) x
        with x (α .proj₁ .proj₂) (α .proj₂ .proj₂)
      ... | _ , step/i i K
        = let eqd = dom-eq (step-altK r _ _ .proj₂)
              K' = valid-eq-dom (sym eqd) i K
          in _ , do-step K' eqd refl (step/i i K')
      ... | _ , step/tl/I ii'' (k , D') kr'
        = _ , step/tl/I ii'' (j , D)
                        (swap-actK H ii r (alt-k ii'' r j D  x) .proj₂)
      swap-act {α} {α'} {G₀} {G₁} (D , H , _) ii (step/parL gr) x
        with x (α .proj₁ .proj₂) (α .proj₂ .proj₂)
      ... | _ , step/parL gr₁
        = _ , step/parL (swap-act H ii gr (alt-parL D gr _ _ gr₁ x) .proj₂)
      ... | _ , step/parR gr₁ = _ , step/parR gr₁
      swap-act {α} {α'} {G₀} {G₁} (D , _ , H) ii (step/parR gr) x
        with x (α .proj₁ .proj₂) (α .proj₂ .proj₂)
      ... | _ , step/parR gr₁
        = _ , step/parR (swap-act H ii gr (alt-parR D gr _ _ gr₁ x) .proj₂)
      ... | _ , step/parL gr₁ = _ , step/parL gr₁

      swap-actK : ∀ {I α α'}{G₀ G₁ : Choice 0 I}
        (H : wf-conts G₀)
        (ii : (hd-action α) ⋔ (hd-action α'))
        (r : G₀ =< α >=> G₁)
        → (∀ i v → ∃[ Gi ] proj₁ (step-altK r i v) =< α' >=> Gi)
        → ∃[ G₂ ] G₀ =< α' >=> G₂
      swap-actK H ii step/nil x = [] , step/nil
      swap-actK {α' = α'} H ii (step/cn r) x
        = _ , step/cn (swap-actK H ii r tlX .proj₂) -- step/cn ()
        where
          tlX : ∀ i v → ∃[ K' ] step-altK r i v .proj₁ =< α' >=> K'
          tlX i v with x i v
          ... | _ , step/cn gr = _ , gr
      swap-actK {α' = α'} (W , H) ii (step/jn x₁ r) x
        = _ , step/jn (swap-act W ii x₁ hdX .proj₂)
                      (swap-actK H ii r tlX .proj₂)
        where
          hdX : ∀ i v → ∃[ K' ] step-alt x₁ i v .proj₁ -< α' >-> K'
          hdX i v with x i v
          ... | _ , step/jn x _ = _ , x
          tlX : ∀ i v → ∃[ K' ] step-altK r i v .proj₁ =< α' >=> K'
          tlX i v with x i v
          ... | _ , step/jn x gr = _ , gr

    valid-comm : ∀ {hα i j α' s v s' v' G G' Gᵢ Gⱼ'}
        → well-formed G
        → hα ∥ₕ (hd-action α')
        → G -< α' >-> G' → G -< (hα , i) , s , v >-> Gᵢ
        → G' -< (hα , j) , s' , v' >-> Gⱼ'
        → s ≡ s'
    valid-comm W ii r1 r2 r3 with the-diamond W r2 r1 ii
    ... | _ , a , b = valid-det (step-wf W r1) b r3

    build-cont : ∀{G G' P Q I}{S : Sorts (suc I)} i {s v} G0
      → G -< (P ⟶ Q # S , i) , s , v >-> G'
      → Fin (suc (HeadAct.nchoices (P ⟶ Q # S))) → Maybe (Global 0 ng)
    build-cont i {s = s} G gr j with j ≟f i
    ... | yes refl  = just G
    ... | no _ with valid? j s
    ... | yes a = just (step-alt gr j a .proj₁)
    ... | no b = nothing

    build-cont/i : ∀{G G' P Q I}{S : Sorts (suc I)} i {s v} G0
      → (gr : G -< (P ⟶ Q # S , i) , s , v >-> G')
      → build-cont i G0 gr i ≡ just G0
    build-cont/i i G0 gr with i ≟f i
    ... | yes refl = refl
    ... | no ¬eq = ⊥-elim (¬eq refl)

    build-cont/j : ∀{G G' P Q I}{S : Sorts (suc I)} i {s v} G0
      → (gr : G -< (P ⟶ Q # S , i) , s , v >-> G')
      → ∀ j (vv : valid j s)
      → j ≢ i
      → build-cont i G0 gr j ≡ just (step-alt gr j vv .proj₁)
    build-cont/j i {s = s} G0 gr j vv jni with j ≟f i
    ... | yes refl = ⊥-elim (jni refl)
    ... | no ¬eq with valid? j s
    ... | yes p rewrite valid-eq j s vv p = refl
    ... | no ¬p = ⊥-elim (¬p vv)

    mk-branches : ∀{α G G'}
      → G -< α >-> G' → Global 0 ng → Choice 0 (suc (aacts α))
    mk-branches gr G = tabulate (build-cont _ G gr)

    build : ∀ {α G0 G1} (G : Global 0 ng) → G0 -< α >-> G1 → Global 0 ng
    build {α = (P ⟶ Q # S , i) , s , v} G gr
      = >> (P ⟶ Q ∶[ S ] tabulate (build-cont i G gr))

    vec-pos-eq : ∀ {A : Set}{I} (v v' : Vec A I)
      → (∀ i → lookup v i ≡ lookup v' i) → v ≡ v'
    vec-pos-eq [] [] f = refl
    vec-pos-eq (x ∷ v) (x₁ ∷ v') f rewrite f zero
      = cong (_ ∷_) (vec-pos-eq v v' (f ∘ suc))

    valid-lookup : ∀{I} (v : Vec Bool I) i → valid i v → lookup v i ≡ true
    valid-lookup (true ∷ v) zero tt = refl
    valid-lookup (x ∷ v) (suc i) H = valid-lookup v i H

    ¬valid-lookup : ∀{I} (v : Vec Bool I) i → ¬ valid i v → lookup v i ≡ false
    ¬valid-lookup (true ∷ v) zero F = ⊥-elim (F tt)
    ¬valid-lookup (false ∷ v) zero F = refl
    ¬valid-lookup (x ∷ v) (suc i) H = ¬valid-lookup v i H

    build-dom-i : ∀ {P Q I} {S : Sorts (suc I)} i s {v : valid i s} {G0 G1} G
                (gr : G0 -< ((P ⟶ Q # S) , i) , s , v >-> G1) j
      → lookup s j ≡ lookup (dom (tabulate (build-cont i G gr))) j
    build-dom-i i s {v = v} G gr j
      rewrite lookup-map j is-just (tabulate (build-cont i G gr))
        | lookup∘tabulate (build-cont i G gr) j
      with j ≟f i
    ... | yes refl = valid-lookup s i v
    ... | no neq  with valid? j s
    ... | yes vv = valid-lookup s j vv
    ... | no ¬vv = ¬valid-lookup s j ¬vv

    build-dom : ∀ {P Q I}{S : Sorts (suc I)} i {s v} {G0 G1} G
      (gr : G0 -< (P ⟶ Q # S , i) , s , v >-> G1) →
      s ≡ dom (tabulate (build-cont i G gr))
    build-dom i {s = s} G gr
      = vec-pos-eq s (dom (tabulate (build-cont i G gr))) (build-dom-i i s G gr)

    dom-mkbr : ∀{G₀ G₁ G G' α} G₂ nG
      → (rG₀G₁ : G₀ -< α >-> G₁)
      → (rGG'  : G -< α >-> G')
      → dom (mk-branches rG₀G₁ G₂) ≡ dom (mk-branches rGG' nG)
    dom-mkbr {α = α , s , i} G₂ nG rG₀G₁ rGG'
      rewrite sym (build-dom _ G₂ rG₀G₁)
      rewrite sym (build-dom _ nG rGG')
      = refl

    valid-get : ∀{A : Set}{I} i (v : Vec (Maybe A) I)
      (V : valid i (dom v))
      → ∃[ x ] lookup v i ≡ just x
    valid-get zero (just x ∷ v) V = x , refl
    valid-get (suc i) (x ∷ v) V = valid-get i v V

    valid-tabulate : ∀{A : Set}{I} i (v : Fin I → Maybe A)
      (V : valid i (dom (tabulate v)))
      → ∃[ x ] v i ≡ just x
    valid-tabulate zero f V with f zero
    ... | just x = x , refl
    valid-tabulate (suc i) f V = valid-tabulate i (f ∘ suc) V

    get∘tabulate : ∀ {A : Set}{X}{I}(f : Fin I → Maybe A) i
      → (V : valid i (dom (tabulate f))) → f i ≡ just X
      → get i (tabulate f) V ≡ X
    get∘tabulate {I = suc zero} f zero V x with f zero | x
    ... | just X | refl = refl
    get∘tabulate {I = suc (suc I)} f zero V x with f zero | x
    ... | just X | refl = refl
    get∘tabulate {I = suc (suc I)} f (suc i) V x = get∘tabulate (f ∘ suc) i V x

    build-steps : ∀ {α G0 G1} G (gr : G0 -< α >-> G1) → build G gr -< α >-> G
    build-steps {α = (P ⟶ Q # S , i) , s , v} G gr
      with build-dom i G gr | valid-eq-dom (build-dom i G gr) i v
    ... | ee | vv
      = do-step vv (sym ee)
                (get∘tabulate (build-cont i G gr) i vv (build-cont/i i G gr))
                (step/i i vv)

    build-steps-neq : ∀ {α i s vi G0 G1} G (gr : G0 -< (α , i) , s , vi >-> G1)
      → ∀ j (e : j ≢ i) vj
      → build G gr -< (α , j) , s , vj  >-> step-alt gr j vj .proj₁
    build-steps-neq {α = (P ⟶ Q # S)} {i = i} {s = s} {vi = vi} G gr j ne vj
      with j ≟f i
    ... | yes refl = ⊥-elim (ne refl)
    ... | no ff with build-dom i G gr | valid-eq-dom (build-dom i G gr) j vj
    ... | ee | vv
      = do-step vv (sym ee)
                (get∘tabulate (build-cont i G gr) j vv
                              (build-cont/j i G gr j vj ff))
                (step/i j vv)

    defined-tabulate : ∀{A : Set}{I}{x : A} f (i : Fin I) → f i ≡ just x
      → defined i (tabulate f)
    defined-tabulate f zero  x
      with f zero | x
    ... | just x₁ | b = tt
    defined-tabulate f (suc i) x = defined-tabulate (λ x₂ → f (suc x₂)) i x

    conts-wf : ∀ {i} (K : Choice 0 i)
      → (∀ j (v : valid j (dom K)) → well-formed (get j K v))
      → wf-conts K
    conts-wf [] x = tt
    conts-wf (just x₁ ∷ K) x = (x zero tt) , conts-wf K (x ∘ suc)
    conts-wf (nothing ∷ K) x = conts-wf K (x ∘ suc)

    wf-get-cont : ∀ {α i s G0 G1} G (gr : G0 -< (α , i) , s >-> G1)
      → well-formed G0
      → well-formed G
      → ∀ j v
      → well-formed (get j (tabulate (build-cont i G gr)) v)
    wf-get-cont {i = i} G gr x x₁ j v
      with j ≟f i
    ... | yes refl
      rewrite get∘tabulate (build-cont i G gr) i v (build-cont/i i G gr)
      = x₁
    ... | no ¬eq
      rewrite get∘tabulate (build-cont i G gr) j v
                           (build-cont/j i G gr j
                             (valid-eq-dom (sym (build-dom i G gr)) j v) ¬eq)
      = step-wf x (step-alt gr j
                (valid-eq-dom (sym (build-dom i G gr)) j v) .proj₂)

    build-conts-wf : ∀ {α i s G0 G1} G (gr : G0 -< (α , i) , s >-> G1)
      → well-formed G0 → well-formed G → wf-conts (tabulate (build-cont i G gr))
    build-conts-wf G gr H H'
      = conts-wf (tabulate (build-cont _ G gr))
                 (wf-get-cont G gr H H')

    build-wf : ∀ {α G0 G1} G (gr : G0 -< α >-> G1)
      → well-formed G0 → well-formed G → well-formed (build G gr)
    build-wf {α = (P ⟶ Q # S , i) , s , v} G gr x x₁
      = snd≢rcv x gr
      , (i , defined-tabulate (build-cont i G gr) i (build-cont/i i G gr))
      , build-conts-wf G gr x x₁

    indep? : ∀ {G α₁ G₁ α₂ G₂}
      → well-formed G
      → G -< α₁ >-> G₁
      → G -< α₂ >-> G₂
      → (hd-action α₁) ⋔ (hd-action α₂) ⊎ hd-action α₁ ≡ hd-action α₂
    indep? {α₁ = α₁} {α₂ = α₂} H gr gr' with hd-action α₁ ⋏? hd-action α₂
    ... | no ¬d = inj₁ ¬d
    ... | yes (inj₂ y₁) rewrite recv-act-eq H gr gr' y₁ = inj₂ refl
    ... | yes (inj₁ (∈R refl)) rewrite recv-act-eq H gr' gr (∈S refl) = inj₂ refl
    ... | yes (inj₁ (∈S p)) with areceiver α₁ ≟f areceiver α₂
    ... | yes refl rewrite recv-act-eq H gr gr' (∈R refl) = inj₂ refl
    ... | no  R∉ rewrite step/acts/same H gr gr' (∈S p) = ⊥-elim (R∉ refl) -- inj₂ refl

    eq-tl : ∀{A : Set}{I} {x y : A} {v v' : Vec A I} →
      x ∷ v ≡ y ∷ v' → v ≡ v'
    eq-tl refl = refl

    step/conts : ∀ {α I}{Ch Ch' : Choice 0 I}
      → dom Ch ≡ dom Ch'
      → (∀ i v v' → (get i Ch v) -< α >-> (get i Ch' v'))
      → Ch =< α >=> Ch'
    step/conts {Ch = []} {Ch' = []} e x = step/nil
    step/conts {Ch = just G₁ ∷ Ch} {Ch' = just G₂ ∷ Ch'} e x
      = step/jn (x zero tt tt) (step/conts (eq-tl e) (x ∘ suc))
    step/conts {Ch = nothing ∷ Ch} {Ch' = nothing ∷ Ch'} e x
      = step/cn (step/conts (eq-tl e) (x ∘ suc))

    stepback/cont : ∀ {α α' G₀ G₁ G G' G₂ nG}
      (H : well-formed G₀)
      (ii : (hd-action α) ⋔ (hd-action α'))
      (rG₀G₁  : G₀ -< α >-> G₁)
      (rG₀G   : G₀ -< α' >-> G) -- because we need to know where 'G' comes from
      (rGG'   : G -< α >-> G')
      (rG₂Gn  : G₂ -< α' >-> nG) -- Because we need to know what G₂ reduces to
      → ∀ i v v' → (get i (mk-branches rG₀G₁ G₂) v)
                            -< α' >-> (get i (mk-branches rGG' nG) v')
    stepback/cont {α = (α , i) , _ , vi}{α' = α'}{G₂ = G₂}{nG = nG}
                  H ii rG₀G₁ rG₀G rGG' rG₂Gn j v v' with j ≟f i
    ... | yes refl
      rewrite get∘tabulate (build-cont i _ rG₀G₁) i v (build-cont/i _ _ rG₀G₁)
      | get∘tabulate (build-cont i _ rGG') i v' (build-cont/i _ _ rGG')
      = rG₂Gn
    ... | no neq
      with valid-eq-dom (sym (build-dom _ _ rG₀G₁)) j v
      | (valid-eq-dom (sym (build-dom _ _ rGG')) j v')
    ... | vj | vj'
      rewrite
        get∘tabulate (build-cont i _ rG₀G₁) j v (build-cont/j _ _ rG₀G₁ _ vj neq)
      | get∘tabulate (build-cont i _ rGG') j v' (build-cont/j _ _ rGG' _ vj' neq)
      = let G₁' , rG₀G₁' = step-alt rG₀G₁ j vj
            G'' , rGG'' = step-alt rGG' j vj'
            _ , r₀ , r₁ = diamond rG₀G rG₀G₁' (⋔sym ii)
            eq = step-det (step-wf H rG₀G) r₀ rGG''
      in subst (λ G → G₁' -< α' >-> G) eq r₁

    stepback/ch : ∀ {α α' G₀ G₁ G G' G₂ nG}
      (H : well-formed G₀)
      (ii : (hd-action α) ⋔ (hd-action α'))
      (rG₀G₁  : G₀ -< α >-> G₁)
      (rG₀G   : G₀ -< α' >-> G) -- because we need to know where 'G' comes from
      (rGG'   : G -< α >-> G')
      (rG₂Gn  : G₂ -< α' >-> nG) -- Because we need to know what G₂ reduces to
      → mk-branches rG₀G₁ G₂ =< α' >=> mk-branches rGG' nG
    stepback/ch {α = α}{G₂ = G₂}{nG = nG} H ii rG₀G₁ rG₀G rGG' rG₂Gn
      = step/conts (dom-mkbr G₂ nG rG₀G₁ rGG')
                   (stepback/cont H ii rG₀G₁ rG₀G rGG' rG₂Gn)

    dom-dne : ∀{I}(s s'  : Vec Bool I) → ¬ ¬ (s ≡ s') → s ≡ s'
    dom-dne [] [] ne = refl
    dom-dne (false ∷ s) (false ∷ s') ne = cong (_ ∷_) (dom-dne s s' λ x → ne (λ{ refl → x refl }))
    dom-dne (false ∷ s) (true ∷ s') ne = ⊥-elim (ne (λ ()))
    dom-dne (true ∷ s) (false ∷ s') ne = ⊥-elim (ne (λ ()))
    dom-dne (true ∷ s) (true ∷ s') ne = cong (_ ∷_) (dom-dne s s' λ x → ne (λ{ refl → x refl }))

    get-neq : ∀{I}(s s'  : Vec Bool I) → ¬ (s ≡ s')
      → ∃[ j ] ((valid j s) × (¬ valid j s') ⊎ (¬ valid j s) × (valid j s'))
    get-neq [] [] ne = ⊥-elim (ne refl)
    get-neq (false ∷ s) (false ∷ s') ne with get-neq s s' (λ{ refl → ne refl })
    ... | j , nv  = suc j , nv
    get-neq (false ∷ s) (true ∷ s') _ = zero , inj₂ ((λ ()) , tt)
    get-neq (true ∷ s) (false ∷ s') ne = zero , inj₁ (tt , λ ())
    get-neq (true ∷ s) (true ∷ s') ne with get-neq s s' (λ{ refl → ne refl })
    ... | j , nv  = suc j , nv

    open _~_

    dom/~ : ∀ {α s s' v v' G₀ G₀' G₁ G₁'}
      → well-formed G₀
      → well-formed G₀'
      → G₀ ~ G₀'
      → G₀ -< α , s , v >-> G₁
      → G₀' -< α , s' , v' >-> G₁'
      → ¬ ¬ s ≡ s'
    dom/~ H H' b gr gr' ne with get-neq _ _ ne
    ... | j , inj₁ (v , nv)
      = let G₂ , gr'' = step-alt gr j v
            G₂' , s-do {s-val = s''} gr''' , _ = ~L b (s-do gr'')
            ee = valid-det  H' gr' gr'''
        in nv (subst (valid j) (sym ee) s'')
    ... | j , inj₂ (nv , v)
      = let G₂ , gr''' = step-alt gr' j v
            G₂' , s-do {s-val = s''} gr'' , _ = ~R b (s-do gr''')
            ee = valid-det  H gr gr''
        in nv (subst (valid j) (sym ee) s'')

    dom~ : ∀ {α s s' v v' G₀ G₀' G₁ G₁'}
      → well-formed G₀
      → well-formed G₀'
      → G₀ ~ G₀'
      → G₀ -< α , s , v >-> G₁
      → G₀' -< α , s' , v' >-> G₁'
      → s ≡ s'
    dom~ x x₁ x₂ x₃ x₄ = dom-dne _ _ (dom/~ x x₁ x₂ x₃ x₄)

    ~Le : ∀ {α G G' G''} → well-formed G → well-formed G' → G ~ G'
      → G -< α >-> G'' → ∃[ G''' ] G' -< α >-> G''' × G'' ~ G'''
    ~Le {α = α , s , v} H H' b gr with ~L b (s-do gr)
    ... | G''' , s-do {s-val = v} gr' , br
      = G''' , do-step v (sym (dom~ H H' b gr gr')) refl gr' , br

    ~Re : ∀ {α G G' G''} → well-formed G → well-formed G' → G' ~ G
      → G -< α >-> G'' → ∃[ G''' ] G' -< α >-> G''' × G'' ~ G'''
    ~Re H H' b gr = ~Le H H' (~sym b) gr

    mk-branches/step : ∀ { α α' G₀ G₁ G₂ Ch }
      (H : well-formed G₀)
      (H : well-formed G₂)
      (ii : (hd-action α) ⋔ (hd-action α'))
      (r : G₀ -< α >-> G₁)
      (b   : G₁ ~ G₂)
      (k : mk-branches r G₂ =< α' >=> Ch)
      → ∀ i v → ∃[ Gi ] proj₁ (step-alt r i v) -< α' >-> Gi
    mk-branches/step {α = (α , i) , s , vi}{G₂ = G₂} H H' ii r b k j vj
      with valid-eq-dom (build-dom _ G₂ r) j vj
    ... | vj' with just-kr {i = j} k vj'
    ... | vj'' with get-kr {i = j} k vj' vj''
    ... | rr with j ≟f i
    ... | yes refl
      rewrite get∘tabulate (build-cont i G₂ r) i vj' (build-cont/i i G₂ r)
        | step-det H (step-alt r i vj .proj₂) r
      = let _ , grl , grr = ~Re H' (step-wf H r) b rr
        in _ , grl
    ... | no neq
      rewrite
        get∘tabulate (build-cont i G₂ r) j vj' (build-cont/j i G₂ r _ vj neq)
      = _ , rr

    record diamond-~ α α' G0 G1 G2 : Set where
      constructor mk-dia-~
      field
        d~-G3 : Global 0 ng
        d~-Gf : Global 0 ng
        d~-Gn : Global 0 ng
        d~-r03 : G0 -< α' >-> d~-G3
        d~-r3f : d~-G3 -< α >-> d~-Gf
        d~-r1f : G1 -< α' >-> d~-Gf
        d~-r2n : G2 -< α' >-> d~-Gn
        d~-f~n : d~-Gf ~ d~-Gn

    opaque
      mk-branches/swap : ∀ { α α' G₀ G₁ G₂ Ch }
        (H : well-formed G₀)
        (H' : well-formed G₂)
        (ii : (hd-action α) ⋔ (hd-action α'))
        (r : G₀ -< α >-> G₁)
        (b   : G₁ ~ G₂)
        (k : mk-branches r G₂ =< α' >=> Ch)
        → diamond-~ α α' G₀ G₁ G₂
      mk-branches/swap H H' ii r b k
        = let ki = mk-branches/step H H' ii r b k
              G3 , rr = swap-act H ii r ki
              nG , r0 , r1 = diamond r rr ii
              nG' , r2 , bb = ~Le (step-wf H r) H' b r0
          in mk-dia-~ G3 nG nG' rr r1 r0 r2 bb

    vec-ext : ∀ {A : Set}{I} → (v v' : Vec (Maybe A) I)
      → dom v ≡ dom v'
      → (∀ i V V' → get i v V ≡ get i v' V') → v ≡ v'
    vec-ext [] [] D f = refl
    vec-ext (just x ∷ v) (just x₁ ∷ v') D f with f zero tt tt
    ... | refl = cong (_ ∷_) (vec-ext v v' (eq-tl D) (f ∘ suc))
    vec-ext (nothing ∷ v) (nothing ∷ v') D f
      = cong (_ ∷_) (vec-ext v v' (eq-tl D) (f ∘ suc))

    step-alt/◇ : ∀ {α α' G₀ G₁ G₂}
      → (H : well-formed G₀)
      → ∀ (ii : (hd-action α) ⋔ (hd-action α'))
      → ∀ (r : G₀ -< α >-> G₁) (r' : G₀ -< α' >-> G₂) i vi vj
      → proj₁ (step-alt (diamond r r' ii .proj₂ .proj₂) i vi)
        ≡ proj₁ (diamond (step-alt r i vj .proj₂) r' ii)
    step-alt/◇ H ii r r' i vi vj
      with diamond (step-alt r i vj .proj₂) r' ii | diamond r r' ii
    ... | G' , r₀ , r₁ | G'' , r₂ , r₃ with step-alt r₃ i vi
    ... | Gf , r₄
      = step-det (step-wf H r') r₄ r₁

    open diamond-~
    mk-branches/swap/st : ∀ { α α' G₀ G₁ G₂ Ch }
      (H : well-formed G₀)
      (H' : well-formed G₂)
      (ii : (hd-action α) ⋔ (hd-action α'))
      (r : G₀ -< α >-> G₁)
      (b   : G₁ ~ G₂)
      (k : mk-branches r G₂ =< α' >=> Ch)
      → ∀ i v v'
      → get i Ch v
      ≡ get i (mk-branches (mk-branches/swap H H' ii r b k .d~-r3f)
                           (mk-branches/swap H H' ii r b k .d~-Gn)) v'
    mk-branches/swap/st {α = (α , i) , s , vi} H H' ii r b k j v v'
      with mk-branches/swap H H' ii r b k | j ≟f i
    mk-branches/swap/st {α = (α , i) , s , vi} {G₂ = G₂} H H' ii r b k j v v'
        | mk-dia-~ d~-G4 d~-Gf d~-Gn d~-r4 d~-r3f d~-r1f d~-r2n d~-f~n
        | yes refl with get-kr {i = i} k
                          (valid-eq-dom (dom-mkbr d~-Gn G₂ d~-r3f r) i v') v
    ... | str
        rewrite
          get∘tabulate (build-cont i d~-Gn d~-r3f) i v'
                       (build-cont/i i d~-Gn d~-r3f)
        | get∘tabulate (build-cont i G₂ r) i
                       (valid-eq-dom (dom-mkbr d~-Gn G₂ d~-r3f r) i v')
                       (build-cont/i i G₂ r)
        = step-det H' str d~-r2n
    mk-branches/swap/st {α = (α , i) , s , vi} {G₂ = G₂} H H' ii r b k j v v'
        | mk-dia-~ d~-G4 d~-Gf d~-Gn d~-r4 d~-r3f d~-r1f d~-r2n d~-f~n
        | no ne with get-kr {i = j} k
                          (valid-eq-dom (dom-mkbr d~-Gn G₂ d~-r3f r) j v') v
    ... | str
      with valid-eq-dom (trans (sym (dom-eq k)) (sym (build-dom i G₂ r))) j v
      | valid-eq-dom (sym (build-dom i d~-Gn d~-r3f)) j v'
      | swap-act H ii r (mk-branches/step H H' ii r b k)
    ... | vj' | vj'' | G4 , ir
        rewrite
          get∘tabulate (build-cont i d~-Gn d~-r3f) j v'
                       (build-cont/j i d~-Gn d~-r3f _ vj'' ne)
        | get∘tabulate (build-cont i G₂ r) j
                       (valid-eq-dom (dom-mkbr d~-Gn G₂ d~-r3f r) j v')
                       (build-cont/j i G₂ r _ vj' ne)
        | sym (step-det H ir d~-r4)
        =  let _ , r₀ , r₁ = diamond (step-alt r j vj' .proj₂) ir ii
               ee = step-det (step-wf H (step-alt r j vj' .proj₂)) str r₀
               ee' = step-det (step-wf H ir) r₁ (step-alt d~-r3f j vj'' .proj₂)
           in trans ee ee'

    mk-branches/swap/steps : ∀ { α α' G₀ G₁ G₂ Ch }
      (H : well-formed G₀)
      (H' : well-formed G₂)
      (ii : (hd-action α) ⋔ (hd-action α'))
      (r : G₀ -< α >-> G₁)
      (b   : G₁ ~ G₂)
      (k : mk-branches r G₂ =< α' >=> Ch)
      → Ch ≡ mk-branches (mk-branches/swap H H' ii r b k .d~-r3f)
                         (mk-branches/swap H H' ii r b k .d~-Gn)
    mk-branches/swap/steps {G₂ = G₂} H H' ii r b k
      = vec-ext _ _
         (trans (sym (dom-eq k))
           (dom-mkbr G₂ _ r (mk-branches/swap H H' ii r b k .d~-r3f)))
         (mk-branches/swap/st H H' ii r b k)

    stb/~ : ∀ {α G0 G1 G1'}
        → (H : well-formed G0)
        → (H' : well-formed G1')
        → (b : G1 ~ G1')
        → (gr : G0 -< α >-> G1)
        → G0 ~ build G1' gr
    stb/~  {α = (P ⟶ Q # S , i) , s , v} H H' b gr .~L  {α = α'} (s-do gr')
      with indep? H gr gr'
    stb/~  {α = (P ⟶ Q # S , i) , s , v} H H' b gr .~L  {α = P ⟶ Q # S , j}
      (s-do gr') | inj₂ refl with j ≟f i
    stb/~  {α = (P ⟶ Q # S , i) , s , v} H H' b gr .~L  {α = P ⟶ Q # S , j}
      (s-do gr') | inj₂ refl | yes refl
      with step-det H gr' gr
    ... | refl = _ , s-do (build-steps _ gr) , b
    stb/~  {α = (P ⟶ Q # S , i) , s , v} H H' b gr .~L  {α = P ⟶ Q # S , j}
      (s-do {s-sub = s'}{s-val = vj} gr') | inj₂ refl | no eq
      with valid-det H gr gr'
    ... | refl rewrite  step-det H gr' (step-alt gr j vj .proj₂)
      = _ , s-do (build-steps-neq _ gr j eq vj) , ~refl
    stb/~  {α = (P ⟶ Q # S , i) , s , v} H H' b rG₀G₁ .~L  {α = α'}
      (s-do rG₀G) | inj₁ ii
      = let G' , rG₁G' , rGG' = diamond rG₀G₁ rG₀G ii
            _ ,  rG₂Gn , Gn~G' = ~Le (step-wf H rG₀G₁) H' b rG₁G'
        in _ , s-do (step/tl/I ii (i , subst (valid i) (build-dom _ _ rG₀G₁) v)
                                  (stepback/ch H ii rG₀G₁ rG₀G rGG' rG₂Gn ))
           , stb/~ (step-wf H rG₀G) (step-wf H' rG₂Gn) Gn~G' rGG'
    stb/~ {α = (P ⟶ Q # S , i) , s , vi} {G1' = G1'}  H H' b gr
      .~R (s-do (step/i j vj))
      with j ≟f i
    ... | yes refl rewrite  get∘tabulate {X = G1'} (build-cont i _ gr) i vj
                                         (build-cont/i i G1' gr)
      = _ , s-do gr , b
    ... | no neq
      rewrite get∘tabulate
                (build-cont i _ gr) j vj
                (build-cont/j i G1' gr j
                  (valid-eq-dom (sym (build-dom i G1' gr)) j vj) neq)
      = _
      , s-do (step-alt gr j
                       (valid-eq-dom (sym (build-dom i G1' gr)) j vj) .proj₂)
      , ~refl
    stb/~ H H' b gr .~R (s-do (step/tl/I ii (j , D) k))
      rewrite mk-branches/swap/steps H H' ii gr b k
      = _ , s-do (mk-branches/swap H H' ii gr b k .d~-r03)
        , stb/~ (step-wf H (mk-branches/swap H H' ii gr b k .d~-r03))
                (step-wf H' (mk-branches/swap H H' ii gr b k .d~-r2n))
                (mk-branches/swap H H' ii gr b k .d~-f~n)
                (mk-branches/swap H H' ii gr b k .d~-r3f)

    stb : ∀ {α G0 G1 G1'}
        → (H : well-formed G0)
        → (H' : well-formed G1')
        → G1 ~ G1' → G0 -< α >-> G1
        → ∃[ G0' ] (well-formed G0') × (G0 ~ G0') × (G0' -< α >-> G1')
    stb {G1' = G1'} H H' b gr
      = build G1' gr , build-wf _ gr H H' , stb/~ H H' b gr , build-steps _ gr

  GlobalTypes : BTheory N
  GlobalTypes .BTheory.Behav
    = Σ[ b ∈ PreTypes.Global 0 ng ] True (PreTypes.wf? b)
  GlobalTypes .BTheory._-<_>->_ (G , _) α (G' , _) = GT-Wrapper.step G α G'

  WF-equal : ∀ (G : PreTypes.Global 0 ng)
    → ∀(W : True (PreTypes.wf? G)) (W' : True (PreTypes.wf? G)) → W ≡ W'
  WF-equal G W W' with PreTypes.wf? G
  ... | yes a = refl
  ... | no a = refl

  B-equal : ∀{G G' : GlobalTypes .BTheory.Behav} → G .proj₁ ≡ G' .proj₁ → G ≡ G'
  B-equal {G , WF}{G , WF'} refl = cong (_ ,_) (WF-equal G WF WF')

  lower-bisim : ∀{G G' : GlobalTypes .BTheory.Behav}
    → BTheory._~_ GlobalTypes G G'
    → BTheory._~_ GT-Wrapper.PTypes (G .proj₁) (G' .proj₁)
  lower-bisim {G , W} {G' , W'} b .BTheory._~_.~L {G″ = G″} (GT-Wrapper.s-do gr)
    with BTheory._~_.~L {G = G , W} b
      {G″ = G″ , fromWitness (PreTypes.step-wf (toWitness W) gr)}  (GT-Wrapper.s-do gr)
  ... | G0' , gr' , b'  = (G0' .proj₁ ) , gr' , lower-bisim b'
  lower-bisim {G , W} {G' , W'} b .BTheory._~_.~R {G‴ = G‴} (GT-Wrapper.s-do gr)
    with BTheory._~_.~R {G = G , W} b
      {G‴ = G‴ , fromWitness (PreTypes.step-wf (toWitness W') gr)}  (GT-Wrapper.s-do gr)
  ... | G0' , gr' , b'  = (G0' .proj₁ ) , gr' , lower-bisim b'

  higher-bisim : ∀{G G' : GlobalTypes .BTheory.Behav}
    → BTheory._~_ GT-Wrapper.PTypes (G .proj₁) (G' .proj₁)
    → BTheory._~_ GlobalTypes G G'
  higher-bisim {G , W} {G' , W'} b .BTheory._~_.~L gr
    with BTheory._~_.~L b gr
  ... | _ , GT-Wrapper.s-do gr' , b'
    = (_ , fromWitness (PreTypes.step-wf (toWitness W') gr'))
    , GT-Wrapper.s-do gr' , higher-bisim b'
  higher-bisim {G , W} {G' , W'} b .BTheory._~_.~R gr
    with BTheory._~_.~R b gr
  ... | _ , GT-Wrapper.s-do gr' , b'
    = (_ , fromWitness (PreTypes.step-wf (toWitness W) gr'))
    , GT-Wrapper.s-do gr' , higher-bisim b'

  GT-Properties : BT-Prop GlobalTypes
  GT-Properties .BT-Prop.recv-act-eq {G = _ , WF} (GT-Wrapper.s-do a) (GT-Wrapper.s-do b) c
    = PreTypes.recv-act-eq (toWitness WF) a b c
  GT-Properties .BT-Prop.snd≢rcv {G = _ , WF} (GT-Wrapper.s-do a) b
    = PreTypes.snd≢rcv (toWitness WF) a b
  GT-Properties .BT-Prop.step-det {G = _ , WF} (GT-Wrapper.s-do x) (GT-Wrapper.s-do x₁)
    = B-equal (PreTypes.step-det (toWitness WF) x x₁)
  GT-Properties .BT-Prop.~stepback {G0 = G0 , WF} {G1' = G1' , WF'} G~G' (GT-Wrapper.s-do gr)
    with GT-Wrapper.stb (toWitness WF) (toWitness WF') (lower-bisim G~G') gr
  ... | G0' , WF' , b , gr' = (G0' , fromWitness WF') , higher-bisim b , GT-Wrapper.s-do gr'
  GT-Properties .BT-Prop.diamond {G = G , WF} (GT-Wrapper.s-do a) (GT-Wrapper.s-do b) x₂
    with GT-Wrapper.the-diamond (toWitness WF) a b x₂
  ... | _ , grl , grr = (_ , fromWitness (PreTypes.step-wf (PreTypes.step-wf (toWitness WF) a) grl))
      , GT-Wrapper.s-do grl , GT-Wrapper.s-do grr
  GT-Properties .BT-Prop.cond-comm {j = j} {G = G , WF} ii
    (GT-Wrapper.s-do gr) (GT-Wrapper.s-do gr') (GT-Wrapper.s-do {s-val = v} gr'')
    with PreTypes.step-alt gr' j
           (subst (PreTypes.valid j)
                  (sym (GT-Wrapper.valid-comm (toWitness WF) ii gr gr' gr'')) v)
  ... | a , b = (a , fromWitness (PreTypes.step-wf (toWitness WF) b))
              , GT-Wrapper.s-do b
