{-# OPTIONS --guardedness #-}

-- No infinite run of τ steps, and a `done` session runs to `finished`.

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Fin using (Fin; zero) renaming (_≟_ to _≟f_; suc to fsuc)
open import Data.Vec
  using (Vec; []; _∷_; _[_]=_; map; sum; allFin)
  renaming (lookup to lu)
open import Data.Vec.Properties
  using ( []=⇒lookup; lookup⇒[]=; lookup-allFin
        ; lookup∘update; lookup∘update′ )
open import Data.Product using (∃-syntax; _,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Maybe using (nothing)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; sym)

open import Utils.Vec using (sum/map-update<)
open import Definitions.Expr
open import Definitions.Behav using (BTheory; WellBehaved; Synchronous)
import Definitions.Proc as A
import Safety.Preservation as Views

module Safety.Termination
  {N : ℕ} {B : BTheory N} (wb : WellBehaved B) (sync : Synchronous B)
  {K : ℕ} (Ρ : A.Assignment N K)
  (wbL   : ∀ j → WellBehaved (Views.Local wb sync Ρ j))
  where

  open import Definitions.Proc N
  open import Safety.Depth N
  open A.Assignment Ρ
  open A.Over N Ρ
  open Views wb sync Ρ using (module Typed)
  open Typed wbL

  τ-depth/processes : Session → ℕ
  τ-depth/processes M = sum (map (τ-depth/proc {γ = 0} {δ = 0}) M)

  τ-depth/lookup< :
    ∀ {M : Session} {j} {Pr Pr′ : Proc 0 0}
    → M [ j ]= Pr
    → τ-depth/proc Pr′ < τ-depth/proc Pr
    → τ-depth/proc Pr′ < τ-depth/proc (lu M j)
  τ-depth/lookup< lu≡ decrease rewrite []=⇒lookup lu≡ = decrease

  τ-depth/decrease :
    ∀ {M M′ G} → ⊢ᴸ M ∶ G → M [ nothing ]⇒ M′
    → τ-depth/processes M′ < τ-depth/processes M
  τ-depth/decrease {M} _
    (s/if/true {E = E} {Pr = Pr} {Pr′ = Pr′} j lu≡ _) =
    sum/map-update< (τ-depth/proc {γ = 0} {δ = 0}) M j
      (τ-depth/lookup< lu≡ (τ-depth/if-then {E = E} {Pr = Pr} {Pr′ = Pr′}))
  τ-depth/decrease {M} _
    (s/if/false {E = E} {Pr = Pr} {Pr′ = Pr′} j lu≡ _) =
    sum/map-update< (τ-depth/proc {γ = 0} {δ = 0}) M j
      (τ-depth/lookup< lu≡ (τ-depth/if-else {E = E} {Pr = Pr} {Pr′ = Pr′}))
  τ-depth/decrease {M} ts (s/rec j lu≡) =
    sum/map-update< (τ-depth/proc {γ = 0} {δ = 0}) M j
      (τ-depth/lookup< lu≡
        (τ-depth/unfold<rec (Per.guarded j (td/lookup ts lu≡))))

  no-infinite-τ-reductions : ∀ M {G} → ⊢ᴸ M ∶ G → M ⇒∞ → ⊥
  no-infinite-τ-reductions M ts r =
    go ts r (<-wellFounded (τ-depth/processes M))
    where
      go : ∀ {M G} → ⊢ᴸ M ∶ G → M ⇒∞ → Acc _<_ (τ-depth/processes M) → ⊥
      go ts r (acc rs) =
        let open _⇒∞ r in
        go (preservation/τ ts ∞-step) ∞-next (rs (τ-depth/decrease ts ∞-step))

  -- ══════════════════════════════════════════════════════════════════
  --  A `done` session runs to `finished`
  -- ══════════════════════════════════════════════════════════════════

  lookup-done : ∀ {M j Pr} → done M → M [ j ]= Pr → done/proc Pr
  lookup-done {j = j} d lu≡ rewrite sym ([]=⇒lookup lu≡) = d j

  still-done : ∀ {M M′} → M [ nothing ]⇒ M′ → done M → done M′
  still-done {M} (s/if/true {Pr = Pr} j lu≡ _) d l
    with l ≟f j | lookup-done d lu≡
  ... | yes refl | done-if dPr _ rewrite lookup∘update l M Pr = dPr
  ... | no l≢j   | _            rewrite lookup∘update′ l≢j M Pr = d l
  still-done {M} (s/if/false {Pr′ = Pr′} j lu≡ _) d l
    with l ≟f j | lookup-done d lu≡
  ... | yes refl | done-if _ dPr′ rewrite lookup∘update l M Pr′ = dPr′
  ... | no l≢j   | _             rewrite lookup∘update′ l≢j M Pr′ = d l
  still-done (s/rec j lu≡) d l with lookup-done d lu≡
  ... | ()

  still-done* : ∀ {M M′} → M τ⇒ M′ → done M → done M′
  still-done* run/end d      = d
  still-done* (run/τ st r) d = still-done* r (still-done st d)

  still-ended :
    ∀ {M M′} (l : Fin K) → M [ nothing ]⇒ M′ → lu M l ≡ ∅ → lu M′ l ≡ ∅
  still-ended {M} l (s/if/true {Pr = Pr} j lu≡ _) ended with l ≟f j
  ... | no l≢j rewrite lookup∘update′ l≢j M Pr = ended
  ... | yes refl rewrite []=⇒lookup lu≡ with ended
  ...   | ()
  still-ended {M} l (s/if/false {Pr′ = Pr′} j lu≡ _) ended with l ≟f j
  ... | no l≢j rewrite lookup∘update′ l≢j M Pr′ = ended
  ... | yes refl rewrite []=⇒lookup lu≡ with ended
  ...   | ()
  still-ended {M} l (s/rec {Pr = Pr} j lu≡) ended with l ≟f j
  ... | no l≢j rewrite lookup∘update′ l≢j M (unfold/proc Pr) = ended
  ... | yes refl rewrite []=⇒lookup lu≡ with ended
  ...   | ()

  still-ended* :
    ∀ {M M′ l} → M τ⇒ M′ → lu M l ≡ ∅ → lu M′ l ≡ ∅
  still-ended* run/end ended = ended
  still-ended* {l = l} (run/τ st r) ended =
    still-ended* r (still-ended l st ended)

  final-run/proc :
    ∀ {M G j}
    → (Pr : Proc 0 0)
    → ⊢ᴸ M ∶ G
    → lu M j ≡ Pr
    → done/proc Pr
    → ∃[ M′ ] M τ⇒ M′ × lu M′ j ≡ ∅
  final-run/proc Pr ts lu≡ done-∅ = _ , run/end , lu≡
  final-run/proc {M} {j = j}
    (ifp E then Pr else Pr′) ts lu≡ (done-if dPr dPr′)
    with eval-bool (Per.guard j (td/lookup ts (lookup⇒[]= j M lu≡)))
  ...   | inj₁ e⇓true =
    let st = s/if/true j (lookup⇒[]= j M lu≡) e⇓true
        M′ , r , ended =
          final-run/proc Pr (preservation/τ ts st) (lookup∘update j M Pr) dPr
    in M′ , run/τ st r , ended
  ...   | inj₂ e⇓false =
    let st = s/if/false j (lookup⇒[]= j M lu≡) e⇓false
        M′ , r , ended =
          final-run/proc Pr′ (preservation/τ ts st) (lookup∘update j M Pr′)
            dPr′
    in M′ , run/τ st r , ended

  final-run/aux :
    ∀ {I M G}
    → (js : Vec (Fin K) I)
    → ⊢ᴸ M ∶ G
    → done M
    → ∃[ M′ ] M τ⇒ M′ × (∀ i → lu M′ (lu js i) ≡ ∅)
  final-run/aux [] ts d = _ , run/end , λ ()
  final-run/aux {M = M} (j ∷ js) ts d
    with final-run/aux js ts d
  ... | M′ , r , endedjs
    with final-run/proc {j = j} (lu M′ j) (preservation/τ* ts r) refl
           (still-done* r d j)
  ...   | M″ , r′ , endedj =
    M″ , r ++ʳ r′ ,
    λ { zero     → endedj
      ; (fsuc i) → still-ended* r′ (endedjs i) }

  final-run :
    ∀ {M G} → ⊢ᴸ M ∶ G → done M → ∃[ M′ ] M τ⇒ M′ × finished M′
  final-run ts d with final-run/aux (allFin K) ts d
  ... | M′ , r , ended =
    M′ , r , λ j → subst (λ l → lu M′ l ≡ ∅) (lookup-allFin j) (ended j)
