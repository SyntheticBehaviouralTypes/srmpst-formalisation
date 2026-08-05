{-# OPTIONS --guardedness #-}

open import Data.Empty using (⊥; ⊥-elim)

open import Data.Nat using (ℕ; _<_; _⊔_; s≤s; suc)
open import Data.Nat.Induction using (<-wellFounded)

open import Data.Nat.Properties
  using
    ( ≤-refl
    ; m≤n⇒m≤n⊔o
    ; m≤n⇒m≤o⊔n
    )

open import Induction.WellFounded using (Acc; acc)

open import Data.Fin
  using (Fin; zero)
  renaming (_≟_ to _≟f_; suc to fsuc)

open import Data.Vec
  using (Vec; []; _∷_; _[_]=_; _[_]≔_; lookup; map; sum; tabulate)

open import Data.Vec.Properties
  using
    ( []=⇒lookup
    ; lookup⇒[]=
    ; lookup∘tabulate
    ; lookup∘update
    ; lookup∘update′
    )

open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (just; nothing)

open import Relation.Nullary using (yes; no)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; sym)

open import Utils.Vec using (sum/map-update<)
open import Definitions.Typing
import Definitions.Typing.Algorithmic as Alg

module Safety.Termination {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  private
    module M = MPST wb
  open M
  open Alg wb using (_&_⊢a_∶_; a/skip; a/if; a/end)
  open M.Subst
  open import Definitions.Typing.Norm wb using (norm; a/if/inv; a/rec/guarded)
  open import Safety.Preservation wb
  open import Safety.Progress wb
  open import Definitions.Typing.Properties wb

  τ-depth/proc :
    ∀ {γ δ}
    → Proc γ δ
    → ℕ
  τ-depth/proc (_ ! _ < _ >∙ _) =
    0
  τ-depth/proc (Σ _ ？[ _ ]· _) =
    0
  τ-depth/proc (ifp _ then Pr else Pr′) =
    suc (τ-depth/proc Pr ⊔ τ-depth/proc Pr′)
  τ-depth/proc (rec Pr) =
    suc (τ-depth/proc Pr)
  τ-depth/proc (v _) =
    0
  τ-depth/proc ∅ =
    0

  τ-depth/message-subst :
    ∀ {γ δ X}
      {Pr  : Proc γ (suc δ)}
      {Pr′ : Proc γ δ}
    → MessageGuarded Pr
    → τ-depth/proc ([ Pr′ / X ]pr Pr) ≡ τ-depth/proc Pr
  τ-depth/message-subst mg/send =
    refl
  τ-depth/message-subst mg/recv =
    refl
  τ-depth/message-subst {X = X} {Pr′ = Pr′} (mg/if mg₁ mg₂)
    rewrite τ-depth/message-subst {X = X} {Pr′ = Pr′} mg₁
          | τ-depth/message-subst {X = X} {Pr′ = Pr′} mg₂ =
    refl

  τ-depth/unfold :
    ∀ {γ}
      {Pr : Proc γ 1}
    → MessageGuarded Pr
    → τ-depth/proc (unfold/proc Pr) ≡ τ-depth/proc Pr
  τ-depth/unfold {Pr = Pr} guarded =
    τ-depth/message-subst {X = zero} {Pr′ = rec Pr} guarded

  τ-depth/if-then :
    ∀ {γ δ E}
      {Pr Pr′ : Proc γ δ}
    → τ-depth/proc Pr < τ-depth/proc (ifp E then Pr else Pr′)
  τ-depth/if-then =
    s≤s (m≤n⇒m≤n⊔o _ ≤-refl)

  τ-depth/if-else :
    ∀ {γ δ E}
      {Pr Pr′ : Proc γ δ}
    → τ-depth/proc Pr′ < τ-depth/proc (ifp E then Pr else Pr′)
  τ-depth/if-else =
    s≤s (m≤n⇒m≤o⊔n _ ≤-refl)

  τ-depth/unfold<rec :
    ∀ {Pr : Proc 0 1}
    → MessageGuarded Pr
    → τ-depth/proc (unfold/proc Pr) < τ-depth/proc (rec Pr)
  τ-depth/unfold<rec guarded
    rewrite τ-depth/unfold guarded =
    ≤-refl

  -- WAS ~65 lines of `head/rec/guarded*` over `⊢head`.  `⊢a` needs none
  -- of it: `blocked/rec` carries `MessageGuarded Pr` as a field, so
  -- `a/rec/guarded` (`Definitions/Typing/Norm.agda`) reads it straight off
  -- a main leaf, with the `P ∈T` chase only for all-cycle trees.
  rec/guarded :
    ∀ {G P Pr}
    → [] & [] ⊢a P ◂ rec Pr ∶ G
    → MessageGuarded Pr
  rec/guarded = a/rec/guarded

  τ-depth/session :
    Session
    → ℕ
  τ-depth/session M =
    sum (map (τ-depth/proc {γ = 0} {δ = 0}) M)

  τ-depth/lookup< :
    ∀ {M : Session} {P} {Pr Pr′ : Proc 0 0}
    → M [ P ]= Pr
    → τ-depth/proc Pr′ < τ-depth/proc Pr
    → τ-depth/proc Pr′ < τ-depth/proc (M [ P ]s)
  τ-depth/lookup< proc≡ decrease
    rewrite []=⇒lookup proc≡ =
    decrease

  τ-depth/decrease :
    ∀ {G M M′}
    → (M⊢G : ⊢s M ∶ G)
    → (st : M [ nothing ]⇒ M′)
    → τ-depth/session M′ < τ-depth/session M
  τ-depth/decrease {M = M} M⊢G
    (s/if/true {E = E} {Pr = Pr} {Pr' = Pr′} P proc≡ _) =
    sum/map-update< (τ-depth/proc {γ = 0} {δ = 0}) M P
      (τ-depth/lookup< proc≡
        (τ-depth/if-then {E = E} {Pr = Pr} {Pr′ = Pr′}))
  τ-depth/decrease {M = M} M⊢G
    (s/if/false {E = E} {Pr = Pr} {Pr' = Pr′} P proc≡ _) =
    sum/map-update< (τ-depth/proc {γ = 0} {δ = 0}) M P
      (τ-depth/lookup< proc≡
        (τ-depth/if-else {E = E} {Pr = Pr} {Pr′ = Pr′}))
  τ-depth/decrease {M = M} M⊢G (s/rec {Pr = Pr} P proc≡) =
    sum/map-update< (τ-depth/proc {γ = 0} {δ = 0}) M P
      (τ-depth/lookup< proc≡
        (τ-depth/unfold<rec
          (rec/guarded (alg/lookup M⊢G proc≡))))

  catτ :
    ∀ {M M′ M″}
    → M  τ⇒ M′
    → M′ τ⇒ M″
    → M  τ⇒ M″
  catτ s/zero tr′ =
    tr′
  catτ (s/more st tr) tr′ =
    s/more st (catτ tr tr′)

  lookup-done :
    ∀ {M P Pr}
    → done M
    → M [ P ]= Pr
    → done/proc Pr
  lookup-done {P = P} doneM proc≡
    rewrite sym ([]=⇒lookup proc≡) =
    doneM P

  still-done :
    ∀ {M M′}
    → M [ nothing ]⇒ M′
    → done M
    → done M′
  still-done {M = M} (s/if/true {Pr = Pr} P proc≡ _) doneM Q
    with Q ≟f P | lookup-done doneM proc≡
  ... | yes refl | done-if donePr _
    rewrite lookup∘update P M Pr =
    donePr
  ... | no Q≢P | _
    rewrite lookup∘update′ Q≢P M Pr =
    doneM Q
  still-done {M = M} (s/if/false {Pr' = Pr′} P proc≡ _) doneM Q
    with Q ≟f P | lookup-done doneM proc≡
  ... | yes refl | done-if _ donePr′
    rewrite lookup∘update P M Pr′ =
    donePr′
  ... | no Q≢P | _
    rewrite lookup∘update′ Q≢P M Pr′ =
    doneM Q
  still-done (s/rec P proc≡) doneM Q
    with lookup-done doneM proc≡
  ... | ()

  still-done* :
    ∀ {M M′}
    → M τ⇒ M′
    → done M
    → done M′
  still-done* s/zero doneM =
    doneM
  still-done* (s/more st tr) doneM =
    still-done* tr (still-done st doneM)

  still-ended :
    ∀ {M M′}
    → (P : Part)
    → M [ nothing ]⇒ M′
    → M  [ P ]s ≡ ∅
    → M′ [ P ]s ≡ ∅
  still-ended {M = M} P
    (s/if/true {Pr = Pr} Q proc≡ _)
    ended
    with P ≟f Q
  ... | no P≢Q
    rewrite lookup∘update′ P≢Q M Pr =
    ended
  ... | yes refl
    rewrite lookup∘update Q M Pr
          | []=⇒lookup proc≡
    with ended
  ...   | ()
  still-ended {M = M} P
    (s/if/false {Pr' = Pr′} Q proc≡ _)
    ended
    with P ≟f Q
  ... | no P≢Q
    rewrite lookup∘update′ P≢Q M Pr′ =
    ended
  ... | yes refl
    rewrite lookup∘update Q M Pr′
          | []=⇒lookup proc≡
    with ended
  ...   | ()
  still-ended {M = M} P (s/rec {Pr = Pr} Q proc≡) ended
    with P ≟f Q
  ... | no P≢Q
    rewrite lookup∘update′ P≢Q M (unfold/proc Pr) =
    ended
  ... | yes refl
    rewrite lookup∘update Q M (unfold/proc Pr)
          | []=⇒lookup proc≡
    with ended
  ...   | ()

  still-ended* :
    ∀ {M M′ P}
    → M τ⇒ M′
    → M  [ P ]s ≡ ∅
    → M′ [ P ]s ≡ ∅
  still-ended* s/zero ended =
    ended
  still-ended* {P = P} (s/more st tr) ended =
    still-ended* tr (still-ended P st ended)

  final-run/proc :
    ∀ {M G P}
    → (Pr : Proc 0 0)
    → ⊢s M ∶ G
    → M [ P ]s ≡ Pr
    → done/proc Pr
    → ∃[ M′ ] M τ⇒ M′ × M′ [ P ]s ≡ ∅
  final-run/proc Pr M⊢G proc≡ done-∅ =
    _ , s/zero , proc≡
  final-run/proc
    {M = M}
    {P = P}
    (ifp E then Pr else Pr′)
    M⊢G
    proc≡
    (done-if donePr donePr′)
    with a/if/inv
           refl
           (alg/lookup
             {M = M}
             {P = P}
             M⊢G
             (lookup⇒[]= P M proc≡))
  ... | etd , _ , _
    with eval-bool etd
  ...   | inj₁ e⇓true =
    let st = s/if/true P (lookup⇒[]= P M proc≡) e⇓true
        M′ , tr , ended =
          final-run/proc
            {M = M [ P ]≔ Pr}
            {P = P}
            Pr
            (preservation/τ M M⊢G st)
            (lookup∘update P M Pr)
            donePr
    in M′ , s/more st tr , ended
  ...   | inj₂ e⇓false =
    let st = s/if/false P (lookup⇒[]= P M proc≡) e⇓false
        M′ , tr , ended =
          final-run/proc
            {M = M [ P ]≔ Pr′}
            {P = P}
            Pr′
            (preservation/τ M M⊢G st)
            (lookup∘update P M Pr′)
            donePr′
    in M′ , s/more st tr , ended

  final-run/aux :
    ∀ {I M G}
    → (Ps : Vec Part I)
    → ⊢s M ∶ G
    → done M
    → ∃[ M′ ]
        M τ⇒ M′
      × (∀ i → M′ [ lookup Ps i ]s ≡ ∅)
  final-run/aux [] M⊢G doneM =
    _ , s/zero , λ ()
  final-run/aux {M = M} (P ∷ Ps) M⊢G doneM
    with final-run/aux Ps M⊢G doneM
  ... | M′ , tr , endedPs
    with final-run/proc
           {M = M′}
           {P = P}
           (M′ [ P ]s)
           (preservation/τ* M⊢G tr)
           refl
           (still-done* tr doneM P)
  ...   | M″ , tr′ , endedP =
    M″ ,
    catτ tr tr′ ,
    λ
      { zero     → endedP
      ; (fsuc i) → still-ended* tr′ (endedPs i)
      }

  final-run :
    ∀ {M G}
    → ⊢s M ∶ G
    → done M
    → ∃[ M′ ] M τ⇒ M′ × finished M′
  final-run {M = M} M⊢G doneM
    with final-run/aux (tabulate (λ P → P)) M⊢G doneM
  ... | M′ , tr , ended =
    M′ ,
    tr ,
    λ P →
      let eq = lookup∘tabulate (λ Q → Q) P
      in subst (λ Q → M′ [ Q ]s ≡ ∅) eq (ended P)

  progress/eventual :
    ∀ {M G}
    → ⊢s M ∶ G
    → ∃[ M′ ]
        ((M τ⇒ M′ × finished M′)
        ⊎ ∃[ α ] M [ α ]⇒+ M′)
  progress/eventual {M = M} M⊢G =
    go M⊢G (<-wellFounded (τ-depth/session M))
    where
    go :
      ∀ {M G}
      → ⊢s M ∶ G
      → Acc _<_ (τ-depth/session M)
      → ∃[ M′ ]
          ((M τ⇒ M′ × finished M′)
          ⊎ ∃[ α ] M [ α ]⇒+ M′)
    go {M = M} M⊢G (acc rs)
      with progress {M = M} M⊢G
    ... | inj₁ doneM =
      let M′ , tr , finishedM′ = final-run M⊢G doneM
      in M′ , inj₁ (tr , finishedM′)
    ... | inj₂ (just α , M′ , st) =
      M′ , inj₂ (α , s/one st)
    ... | inj₂ (nothing , M′ , st)
      with go
             (preservation/τ M M⊢G st)
             (rs (τ-depth/decrease M⊢G st))
    ...   | M″ , inj₁ (tr , finishedM″) =
      M″ , inj₁ (s/more st tr , finishedM″)
    ...   | M″ , inj₂ (α , tr) =
      M″ , inj₂ (α , s/more st tr)

  no-infinite-τ-reductions :
    ∀ M {G}
    → ⊢s M ∶ G
    → M ⇏∞

  no-infinite-τ-reductions M td sr =
    go td sr (<-wellFounded (τ-depth/session M))
    where
    go :
      ∀ {M G}
      → ⊢s M ∶ G
      → M ⇒∞
      → Acc _<_ (τ-depth/session M)
      → ⊥
    go {M = M} M⊢G td (acc rs) =
      let open _⇒∞ td in
      go
        (preservation/τ M M⊢G ∞-step)
        ∞-next
        (rs (τ-depth/decrease M⊢G ∞-step))
