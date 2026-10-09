{-# OPTIONS --guardedness #-}
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; suc)
open import Data.Fin
  using (Fin; zero; suc; punchIn; punchOut)
  renaming (_≟_ to _≟f_)
import Data.Fin.Properties as FinP
open import Data.Fin.Subset using (_∈_; Side; inside)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Product using (∃-syntax; _×_; _,_; proj₂)
open import Data.List using (List)
import Data.List as L
open import Data.Vec
  using (Vec; []; _∷_; _[_]=_; _[_]≔_; tabulate)
  renaming (lookup to lu)
open import Data.Vec.Properties using (lookup∘tabulate; lookup⇒[]=; []=⇒lookup)
open import Relation.Nullary using (Dec; does; yes; no; ¬_; ¬?)
open import Relation.Nullary.Decidable
  using (_×?_; dec-true; dec-yes; dec-no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; cong)

open import Definitions.Expr

module Definitions.Proc (N : ℕ) where

  open import Definitions.Actions(N)
  open import Definitions.Common(N)

  -- γ and δ count expression and recursion binders, respectively.
  data Proc (γ δ : ℕ) : Set where
    -- Role `P` sends to every role in `Qs`.
    _⇒_!_<_>∙_ :
      Part → PartSet → {I : ℕ} → Fin (suc I) → Exp γ → Proc γ δ → Proc γ δ
    -- Role `R` receives from `P`.  Branch sorts come from the matched step,
    -- not from the process.
    _⇐_？·_ :
      Part → Part → {I : ℕ}
      → Vec (Proc (suc γ) δ) (suc I) → Proc γ δ
    ifp_then_else_ : Exp γ → Proc γ δ → Proc γ δ → Proc γ δ
    rec : Proc γ (suc δ) → Proc γ δ
    v : Fin δ → Proc γ δ
    ∅ : Proc γ δ

  infixr 8 _⇒_!_<_>∙_
  infixr 8 _⇐_？·_
  infix  6 ifp_then_else_

  -- A process typed at the set of roles it owns.
  data NProc (γ δ : ℕ) : Set where
    _◂_ : PartSet → Proc γ δ → NProc γ δ

  infix 5 _◂_

  -- A `rec` body starts with a message on every branch of its `if`s.
  data MessageGuarded {γ δ} : Proc γ δ → Set where
    mg/send :
      ∀ {Q} {Qs : PartSet} {I}
        {i  : Fin (suc I)}
        {E  : Exp γ}
        {Pr : Proc γ δ}
      → MessageGuarded (Q ⇒ Qs ! i < E >∙ Pr)

    mg/recv :
      ∀ {R P I}
        {Br : Vec (Proc (suc γ) δ) (suc I)}
      → MessageGuarded (R ⇐ P ？· Br)

    mg/if :
      ∀ {E : Exp γ}
        {Pr Pr' : Proc γ δ}
      → MessageGuarded Pr
      → MessageGuarded Pr'
      → MessageGuarded (ifp E then Pr else Pr')

  data done/proc {γ δ} : Proc γ δ → Set where
    done-∅ : done/proc ∅
    done-if :
      ∀ {E Pr Pr′}
      → done/proc Pr
      → done/proc Pr′
      → done/proc (ifp E then Pr else Pr′)

  module Subst where
    mutual
      weaken/proc :
        ∀ {γ δ} → Proc γ δ → Fin (suc δ) → Proc γ (suc δ)
      weaken/proc (Q ⇒ Qs ! L < E >∙ Pr) X =
        Q ⇒ Qs ! L < E >∙ (weaken/proc Pr X)
      weaken/proc (R ⇐ P ？· Br) X = R ⇐ P ？· (weaken/proc/branch Br X)
      weaken/proc (ifp E then Pr else Pr′) X =
        ifp E then weaken/proc Pr X else weaken/proc Pr′ X
      weaken/proc (rec Pr) X = rec (weaken/proc Pr (suc X))
      weaken/proc (v x) X = v (punchIn X x)
      weaken/proc ∅ X = ∅

      weaken/proc/branch :
        ∀ {γ δ I}
        → Vec (Proc γ δ) I
        → Fin (suc δ)
        → Vec (Proc γ (suc δ)) I
      weaken/proc/branch [] X = []
      weaken/proc/branch (Pr ∷ Br) X =
        weaken/proc Pr X ∷ weaken/proc/branch Br X

    mutual
      weaken/proc/exp :
        ∀ {γ δ} → Proc γ δ → Fin (suc γ) → Proc (suc γ) δ
      weaken/proc/exp (Q ⇒ Qs ! L < E >∙ Pr) x =
        Q ⇒ Qs ! L < weaken/exp E x >∙ (weaken/proc/exp Pr x)
      weaken/proc/exp (R ⇐ P ？· Br) x =
        R ⇐ P ？· weaken/exp/branch Br (suc x)
      weaken/proc/exp (ifp E then Pr else Pr′) x =
        ifp weaken/exp E x
          then weaken/proc/exp Pr x
          else weaken/proc/exp Pr′ x
      weaken/proc/exp (rec Pr) x = rec (weaken/proc/exp Pr x)
      weaken/proc/exp (v X) x = v X
      weaken/proc/exp ∅ x = ∅

      weaken/exp/branch :
        ∀ {γ δ I}
        → Vec (Proc (suc γ) δ) I
        → Fin (suc (suc γ))
        → Vec (Proc (suc (suc γ)) δ) I
      weaken/exp/branch [] x = []
      weaken/exp/branch (Pr ∷ Br) x =
        weaken/proc/exp Pr x ∷ weaken/exp/branch Br x

    mutual
      [_/_]pr_ :
        ∀ {γ δ} → Proc γ δ → Fin (suc δ) → Proc γ (suc δ) → Proc γ δ
      [ Pr / y ]pr (Q ⇒ Qs ! L < E >∙ Pr') =
        Q ⇒ Qs ! L < E >∙ ([ Pr / y ]pr Pr')
      [ Pr / y ]pr (R ⇐ P ？· Br) = R ⇐ P ？· ([ Pr / y ]prch Br)
      [ Pr / y ]pr (ifp E then Prₜ else Prₑ) =
        ifp E then [ Pr / y ]pr Prₜ else [ Pr / y ]pr Prₑ
      [ Pr / y ]pr rec Pr' = rec ([ weaken/proc Pr zero / suc y ]pr Pr')
      [ Pr / y ]pr v x with y ≟f x
      [ Pr / x ]pr v (.x) | yes refl = Pr
      [ Pr / y ]pr v x | no y≢x = v (punchOut y≢x)
      [ Pr / y ]pr ∅ = ∅

      [_/_]prch_ :
        ∀ {γ δ I}
        → Proc γ δ
        → Fin (suc δ)
        → Vec (Proc (suc γ) (suc δ)) I
        → Vec (Proc (suc γ) δ) I
      [ Pr / y ]prch [] = []
      [ Pr / y ]prch (Pr′ ∷ Br) =
        [ weaken/proc/exp Pr zero / y ]pr Pr′ ∷ [ Pr / y ]prch Br

    mutual
      [_/_]e_ : ∀{γ δ} -> Exp γ -> Fin (suc γ) -> Proc (suc γ) δ -> Proc γ δ
      [ E / y ]e (Q ⇒ Qs ! L < E′ >∙ Pr′) =
        Q ⇒ Qs ! L < [ E / y ]exp E′ >∙ [ E / y ]e Pr′
      [ E / y ]e (R ⇐ P ？· Br) =
        R ⇐ P ？· [ weaken/exp E zero / y ]ech Br
      [ E / y ]e (ifp E′ then Prₜ else Prₑ) =
        ifp [ E / y ]exp E′
          then [ E / y ]e Prₜ
          else [ E / y ]e Prₑ
      [ E / y ]e rec Pr′ = rec ([ E / y ]e Pr′)
      [ E / y ]e v x = v x
      [ E / y ]e ∅ = ∅

      [_/_]ech_ :
        ∀ {γ δ I}
        → Exp γ → Fin γ → Vec (Proc (suc γ) δ) I → Vec (Proc γ δ) I
      [ E / y ]ech [] = []
      [ E / y ]ech (Pr′ ∷ Br) =
        [ E / suc y ]e Pr′ ∷ [ E / y ]ech Br

  unfold/proc : ∀{γ} -> Proc γ 1 -> Proc γ 0
  unfold/proc Pr = Subst.[ (rec Pr) / zero ]pr Pr

  -- ════════════════════════════════════════════════════════════════════
  --  Sessions: one process per block of an assignment
  -- ════════════════════════════════════════════════════════════════════

  -- A partition of the roles into `K` blocks; process `j` owns `roles j`.
  record Assignment (K : ℕ) : Set where
    field
      roles   : Vec PartSet K
      owner   : Part → Fin K
      owner/∈ : ∀ R → R ∈ lu roles (owner R)
      ∈/owner : ∀ {j R} → R ∈ lu roles j → owner R ≡ j

  -- The assignment of an owner map: block `j` is the roles `owner` sends
  -- to `j`.
  byOwner : ∀ {K} → (Part → Fin K) → Assignment K
  byOwner {K} own = record
    { roles   = roles
    ; owner   = own
    ; owner/∈ = λ R → lookup⇒[]= R (lu roles (own R)) (side/self R)
    ; ∈/owner = λ {j} {R} R∈ → side/inside (trans (sym (lookup∘tabulate _ R))
                  (trans (cong (λ v → lu v R) (sym (lookup∘tabulate _ j)))
                    ([]=⇒lookup R∈)))
    }
    where
      side : Fin K → Part → Side
      side j R = does (own R ≟f j)

      roles : Vec PartSet K
      roles = tabulate λ j → tabulate (side j)

      side/self : ∀ R → lu (lu roles (own R)) R ≡ inside
      side/self R
        rewrite lookup∘tabulate (λ j → tabulate (side j)) (own R)
              | lookup∘tabulate (side (own R)) R =
        dec-true (own R ≟f own R) refl

      side/inside : ∀ {j R} → side j R ≡ inside → own R ≡ j
      side/inside {j} {R} eq with own R ≟f j
      ... | yes e = e
      side/inside () | no _

  -- One process per role: the single-role sessions.
  singletons : Assignment N
  singletons = byOwner λ R → R

  module Over {K : ℕ} (Ρ : Assignment K) where

    open Assignment Ρ

    -- One closed process per block.
    Session : Set
    Session = Vec (Proc 0 0) K

    -- Process `k` receives a send by `j` to `Qs`: another process owning a
    -- role of `Qs`.
    Receives : Fin K → PartSet → Fin K → Set
    Receives j Qs k = k ≢ j × ∃[ R ] R ∈ Qs × owner R ≡ k

    receives? : ∀ j Qs k → Dec (Receives j Qs k)
    receives? j Qs k =
      ¬? (k ≟f j) ×? FinP.any? (λ R → (R ∈? Qs) ×? (owner R ≟f k))

    -- Multicast update: `j` becomes `Pr`, each receiver `k` becomes `F k`.
    upd-at :
      Session → Fin K → Proc 0 0 → PartSet → (Fin K → Proc 0 0)
      → Fin K → Proc 0 0
    upd-at M j Pr Qs F k with k ≟f j
    ... | yes _ = Pr
    ... | no _ with receives? j Qs k
    ...   | yes _ = F k
    ...   | no _  = lu M k

    _[_↦_∣_↦_] :
      Session → Fin K → Proc 0 0 → PartSet → (Fin K → Proc 0 0) → Session
    M [ j ↦ Pr ∣ Qs ↦ F ] = tabulate (upd-at M j Pr Qs F)

    upd/sender :
      ∀ {M j Pr Qs F} → lu (M [ j ↦ Pr ∣ Qs ↦ F ]) j ≡ Pr
    upd/sender {M} {j} {Pr} {Qs} {F} =
      trans (lookup∘tabulate (upd-at M j Pr Qs F) j) at
      where
        at : upd-at M j Pr Qs F j ≡ Pr
        at rewrite FinP.≟-≡-refl j = refl

    upd/recv :
      ∀ {M j Pr Qs F k}
      → Receives j Qs k → lu (M [ j ↦ Pr ∣ Qs ↦ F ]) k ≡ F k
    upd/recv {M} {j} {Pr} {Qs} {F} {k} r@(k≢j , _) =
      trans (lookup∘tabulate (upd-at M j Pr Qs F) k) at
      where
        at : upd-at M j Pr Qs F k ≡ F k
        at rewrite FinP.≟-≢ k≢j | proj₂ (dec-yes (receives? j Qs k) r) = refl

    upd/other :
      ∀ {M j Pr Qs F l}
      → l ≢ j → ¬ Receives j Qs l → lu (M [ j ↦ Pr ∣ Qs ↦ F ]) l ≡ lu M l
    upd/other {M} {j} {Pr} {Qs} {F} {l} l≢j ¬r =
      trans (lookup∘tabulate (upd-at M j Pr Qs F) l) at
      where
        at : upd-at M j Pr Qs F l ≡ lu M l
        at rewrite FinP.≟-≢ l≢j | dec-no (receives? j Qs l) ¬r = refl

    -- Operational semantics.

    data _[_]⇒_ (M : Session) : Maybe Action → Session → Set where
      -- Role `P` of `j` sends; every other process owning a role of `Qs`
      -- receives.
      s/comm :
        ∀ {P Qs I} {i : Fin (suc I)} {E V Pr}
          {Rk : Fin K → Part}
          {Br : Fin K → Vec (Proc 1 0) (suc I)}
        → (j : Fin K)
        → P ∈ lu roles j
        → M [ j ]= P ⇒ Qs ! i < E >∙ Pr
        → E ⇓ V
        → (recvs : ∀ k → Receives j Qs k
                   → Rk k ∈ Qs × Rk k ∈ lu roles k
                   × M [ k ]= Rk k ⇐ P ？· Br k)
        → M [ just (P ⟶ Qs # i < sort/value V >) ]⇒
            (M [ j ↦ Pr ∣ Qs ↦ (λ k → Subst.[ val V / zero ]e lu (Br k) i) ])

      s/if/true :
        ∀ {E Pr Pr′}
        → (j : Fin K)
        → M [ j ]= ifp E then Pr else Pr′
        → E ⇓ v/bool true
        → M [ nothing ]⇒ (M [ j ]≔ Pr)

      s/if/false :
        ∀ {E Pr Pr′}
        → (j : Fin K)
        → M [ j ]= ifp E then Pr else Pr′
        → E ⇓ v/bool false
        → M [ nothing ]⇒ (M [ j ]≔ Pr′)

      s/rec :
        ∀ {Pr}
        → (j : Fin K)
        → M [ j ]= rec Pr
        → M [ nothing ]⇒ (M [ j ]≔ unfold/proc Pr)

    -- A run, recording its communications; silent steps anywhere.
    infix 4 _=[_]⇒*_

    data _=[_]⇒*_ (M : Session) : List Action → Session → Set where
      run/end  : M =[ L.[] ]⇒* M
      run/τ    : ∀ {M′ M″ αs} → M [ nothing ]⇒ M′ → M′ =[ αs ]⇒* M″ → M =[ αs ]⇒* M″
      run/comm : ∀ {M′ M″ α αs}
               → M [ just α ]⇒ M′ → M′ =[ αs ]⇒* M″ → M =[ α L.∷ αs ]⇒* M″

    infixr 5 _++ʳ_

    _++ʳ_ :
      ∀ {M M′ M″ αs βs}
      → M =[ αs ]⇒* M′ → M′ =[ βs ]⇒* M″ → M =[ αs L.++ βs ]⇒* M″
    run/end       ++ʳ r′ = r′
    run/τ st r    ++ʳ r′ = run/τ st (r ++ʳ r′)
    run/comm st r ++ʳ r′ = run/comm st (r ++ʳ r′)

    -- A run of silent steps (`run/comm` cannot produce `[]`).
    _τ⇒_ : Session → Session → Set
    M τ⇒ M′ = M =[ L.[] ]⇒* M′

    record _⇒∞ (M : Session) : Set where
      coinductive
      field
        ∞-M    : Session
        ∞-step : M [ nothing ]⇒ ∞-M
        ∞-next : ∞-M ⇒∞

    -- Every process is done.
    done : Session → Set
    done M = ∀ j → done/proc (lu M j)

    finished : Session → Set
    finished M = ∀ j → lu M j ≡ ∅
