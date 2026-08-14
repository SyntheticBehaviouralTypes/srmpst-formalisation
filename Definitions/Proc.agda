{-# OPTIONS --guardedness #-}
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc)
open import Data.Fin
  using (Fin; zero; suc; punchIn; punchOut)
  renaming (_≟_ to _≟f_)
open import Data.Vec
  using (Vec; []; _∷_; _[_]=_; _[_]≔_)
  renaming (lookup to lu)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Definitions.Expr

module Definitions.Proc (N : ℕ) where

  open import Definitions.Actions(N)
  open import Definitions.Common(N)
  open Comm
  open Choice
  open Action

  -- γ and δ count expression and recursion binders, respectively.
  data Proc (γ δ : ℕ) : Set where
    _!_<_>∙_ :
      Part → {I : ℕ} → Fin (suc I) → Exp γ → Proc γ δ → Proc γ δ
    -- The branch sorts are NOT recorded here: `blocked/recv` reads each
    -- branch's sort off the graph edge it matches (`(U ∷ Γ) & Δ ⊢a …`), so a
    -- declared vector was never consulted by any premise.  See
    -- `Tests/LabelSorts.agda`: one label can carry different sorts at
    -- different states, and a single receive must cover all of them.  The
    -- arity `I` stays pinned by the branch vector.
    Σ_？·_ :
      Part → {I : ℕ}
      → Vec (Proc (suc γ) δ) (suc I) → Proc γ δ
    ifp_then_else_ : Exp γ → Proc γ δ → Proc γ δ → Proc γ δ
    rec : Proc γ (suc δ) → Proc γ δ
    v : Fin δ → Proc γ δ
    ∅ : Proc γ δ

  infixr 8 _!_<_>∙_
  infixr 8 Σ_？·_
  infix  6 ifp_then_else_

  data NProc (γ δ : ℕ) : Set where
    _◂_ : Part → Proc γ δ → NProc γ δ

  infix 5 _◂_

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
      weaken/proc (P ! L < E >∙ Pr) X = P ! L < E >∙ (weaken/proc Pr X)
      weaken/proc (Σ P ？· Br) X = Σ P ？· (weaken/proc/branch Br X)
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
      weaken/proc/exp (P ! L < E >∙ Pr) x =
        P ! L < weaken/exp E x >∙ (weaken/proc/exp Pr x)
      weaken/proc/exp (Σ P ？· Br) x =
        Σ P ？· weaken/exp/branch Br (suc x)
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
      [ Pr / y ]pr (P ! L < E >∙ Pr') = P ! L < E >∙ ([ Pr / y ]pr Pr')
      [ Pr / y ]pr (Σ P ？· Br) = Σ P ？· ([ Pr / y ]prch Br)
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
      [ E / y ]e (P ! L < E′ >∙ Pr′) =
        P ! L < [ E / y ]exp E′ >∙ [ E / y ]e Pr′
      -- y will be weakned per branch
      [ E / y ]e (Σ P ？· Br) =
        Σ P ？· [ weaken/exp E zero / y ]ech Br
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

  -- Sessions

  -- a complete session has N participants and all the processes are closed
  Session : Set
  Session = Vec (Proc 0 0) N

  _[_]s : Session → Part → Proc 0 0
  M [ P ]s = lu M P

  -- Operational semantics of sessions

  data _[_]⇒_ (M : Session) : Maybe Action → Session → Set where
    s/comm :
      ∀ {I} {i : Fin (suc I)} {E V Pr Br}
      → (P Q : Part)
      → M [ P ]= Q ! i < E >∙ Pr
      → E ⇓ V
      → M [ Q ]= Σ P ？· Br
      → M [ just (P ⟶ Q # i < sort/value V >) ]⇒
          (M [ P ]≔ Pr [ Q ]≔ Subst.[ val V / zero ]e (lu Br i))

    s/if/true :
      ∀ {E Pr Pr'}
      → (P : Part)
      → M [ P ]= ifp E then Pr else Pr'
      → E ⇓ v/bool true
      → M [ nothing ]⇒ (M [ P ]≔ Pr)
    s/if/false :
      ∀ {E Pr Pr'}
      → (P : Part)
      → M [ P ]= ifp E then Pr else Pr'
      → E ⇓ v/bool false
      → M [ nothing ]⇒ (M [ P ]≔ Pr')

    s/rec :
      ∀ {Pr}
      → (P : Part)
      → M [ P ]= rec Pr
      → M [ nothing ]⇒ (M [ P ]≔ unfold/proc Pr)

  data _[_]⇒+_ (M : Session) : Action → Session → Set where
    s/one : ∀ {α M′} → M [ just α ]⇒ M′ → M [ α ]⇒+ M′
    s/more :
      ∀ {α M′ M″}
      → M [ nothing ]⇒ M′ → M′ [ α ]⇒+ M″ → M [ α ]⇒+ M″

  data _τ⇒_ (M : Session) : Session → Set where
    s/zero : M τ⇒ M
    s/more :
      ∀ {M′ M″} → M [ nothing ]⇒ M′ → M′ τ⇒ M″ → M τ⇒ M″

  record _⇒∞ (M : Session) : Set where
      coinductive
      field
        ∞-M : Session
        ∞-step : M [ nothing ]⇒ ∞-M
        ∞-next : ∞-M ⇒∞

  _⇏∞ : Session → Set
  M ⇏∞ = ¬ (M ⇒∞)

  -- A session is done if all it's participants are done
  done : Session → Set
  done M = ∀ P → done/proc (M [ P ]s)

  finished : Session → Set
  finished M = ∀ P → M [ P ]s ≡ ∅
