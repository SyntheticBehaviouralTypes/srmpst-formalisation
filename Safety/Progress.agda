{-# OPTIONS --guardedness #-}

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc)
open import Data.Fin
  using (Fin; zero)
  renaming (_≟_ to _≟f_; suc to fsuc)
open import Data.Vec
  using (Vec; []; _∷_; _[_]=_; lookup; tabulate)
open import Data.Vec.Properties using (lookup⇒[]=; lookup∘tabulate)
open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Data.Maybe.Base using (just; nothing)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; sym)
open import Definitions.Typing

module Safety.Progress {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  private
    module M = MPST wb
  open M
  open import Definitions.Typing.Alg wb
    using ( a/send; a/recv; a/if; a/end; a/var; a/rec
          ; waitActive; waitStep; waitLeaf
          ; _⊢at_∶_; at/send-inv; at/recv-inv )
  open M.Subst
  open import Definitions.Typing.Substitution wb
  open import Safety.Preservation wb

  -- The judgment is syntax directed, so `MessageGuarded` narrows it to
  -- send/recv/if, and the tree walk is `waitActive`.
  guarded/active :
    ∀ {γ δ G P Pr}
      {Γ : Vec Sort γ}
      {ws : Vec Behav δ}
    → MessageGuarded Pr
    → Γ ⊢at P ◂ Pr ∶ (ws , G)
    → P ∈T G

  guarded/active mg/send td
    with at/send-inv td
  ... | _ , _ , w , _ =
    waitActive (λ { (_ , gr) → in/send gr }) w

  guarded/active mg/recv td =
    waitActive (λ { (_ , _ , _ , gr) → in/recv gr }) (proj₁ (at/recv-inv td))

  guarded/active (mg/if mg₁ _) (𝒮 , a/if _ ttd _ , mem) =
    guarded/active mg₁ (𝒮 , ttd , mem)

  -- `a/var` is impossible because Safety is all `δ = 0`, so `X : Fin 0`;
  -- `a/rec` unfolds the recursion, where the guarded body forces `P ∈T`.
  inactive/done :
    ∀ {G P Pr}
    → P ∉T G
    → [] ⊢at P ◂ Pr ∶ ([] , G)
    → done/proc Pr

  inactive/done P∉G td@(_ , a/send _ _ _ , _) =
    ⊥-elim (P∉G (guarded/active mg/send td))

  inactive/done P∉G td@(_ , a/recv _ _ , _) =
    ⊥-elim (P∉G (guarded/active mg/recv td))

  inactive/done P∉G (𝒮 , a/if _ ttd ftd , mem) =
    done-if
      (inactive/done P∉G (𝒮 , ttd , mem))
      (inactive/done P∉G (𝒮 , ftd , mem))

  inactive/done _ (_ , a/end _ , _) =
    done-∅

  inactive/done _ (_ , a/var {X = ()} _ , _)

  inactive/done P∉G td@(_ , a/rec guarded _ _ , _) =
    ⊥-elim
      (P∉G
        (guarded/active
          (guarded/subst-proc guarded)
          (at/rec/unfold td)))

  data SessionStatus
    (M : Session)
    (G : Behav)
    {I : ℕ}
    (Ps : Vec Part I)
    : Set
    where

    ss/step :
      ∀ {α G′}
      → G -< α >-> G′
      → SessionStatus M G Ps

    ss/if :
      ∀ {P E Pr Pr′}
      → [] ⊢e E ∶ s/bool
      → M [ P ]= ifp E then Pr else Pr′
      → SessionStatus M G Ps

    ss/rec :
      ∀ {P Pr}
      → M [ P ]= rec Pr
      → SessionStatus M G Ps

    ss/end :
      (∀ i → lookup Ps i ∉T G)
      → SessionStatus M G Ps

  status/cons :
    ∀ {I M G P}
      {Ps : Vec Part I}
    → P ∉T G
    → SessionStatus M G Ps
    → SessionStatus M G (P ∷ Ps)
  status/cons _ (ss/step gr) =
    ss/step gr
  status/cons _ (ss/if etd proc≡) =
    ss/if etd proc≡
  status/cons _ (ss/rec proc≡) =
    ss/rec proc≡
  status/cons P∉G (ss/end done) =
    ss/end λ
      { zero     → P∉G
      ; (fsuc i) → done i
      }

  -- The two communication rules both reduce to "the root steps": `waitStep`.
  head/status :
    ∀ {I M G P Pr}
      {Ps : Vec Part I}
    → SessionStatus M G Ps
    → M [ P ]= Pr
    → [] ⊢at P ◂ Pr ∶ ([] , G)
    → SessionStatus M G (P ∷ Ps)

  head/status _ _ td@(_ , a/send _ _ _ , _)
    with at/send-inv td
  ... | _ , _ , w , _
    with waitStep (λ { (_ , gr) → _ , _ , gr }) w
  ...   | _ , _ , gr = ss/step gr

  head/status _ _ td@(_ , a/recv _ _ , _)
    with waitStep (λ { (_ , _ , _ , gr) → _ , _ , gr }) (proj₁ (at/recv-inv td))
  ... | _ , _ , gr = ss/step gr

  head/status _ proc≡ (_ , a/if etd _ _ , _) =
    ss/if etd proc≡

  head/status {G = G} tail _ (_ , a/end done , mem) =
    status/cons (done {[] , G} mem) tail

  head/status _ _ (_ , a/var {X = ()} _ , _)

  head/status _ proc≡ (_ , a/rec _ _ _ , _) =
    ss/rec proc≡

  session/status :
    ∀ {I M G}
    → (Ps : Vec Part I)
    → ⊢s M ∶ G
    → SessionStatus M G Ps

  session/status [] M⊢G =
    ss/end λ ()

  session/status {M = M} (P ∷ Ps) M⊢G =
    head/status
      (session/status Ps M⊢G)
      (lookup⇒[]= P M refl)
      (at/lookup M⊢G (lookup⇒[]= P M refl))

  all-parts/end :
    ∀ {G}
    → (∀ i → lookup (tabulate (λ P → P)) i ∉T G)
    → ∀ P → P ∉T G
  all-parts/end ended P P∈G =
    ended P
      (subst
        (λ Q → Q ∈T _)
        (sym (lookup∘tabulate (λ Q → Q) P))
        P∈G)

  if/progress :
    ∀ {M P E Pr Pr′}
    → [] ⊢e E ∶ s/bool
    → M [ P ]= ifp E then Pr else Pr′
    → ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′
  if/progress {P = P} etd proc≡
    with eval-bool etd
  ... | inj₁ e⇓true =
    nothing , _ , s/if/true P proc≡ e⇓true
  ... | inj₂ e⇓false =
    nothing , _ , s/if/false P proc≡ e⇓false

  -- `Q` is ACTIVE at `G` (it is `gr`'s receiver), so `waitLeaf` says the
  -- `Wait` is a leaf.
  receiver/head-progress :
    ∀ {M G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {E : Exp 0}
      {Pr : Proc 0 0}
      {QPr : Proc 0 0}
    → ⊢s M ∶ G
    → [] ⊢e E ∶ S
    → G -< P ⟶ Q # i < S > >-> G′
    → M [ P ]= Q ! i < E >∙ Pr
    → M [ Q ]= QPr
    → [] ⊢at Q ◂ QPr ∶ ([] , G)
    → ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′

  -- `Q` cannot be sending here: the two actions would share a comm, making
  -- `Q` its own sender and receiver.
  receiver/head-progress M⊢G etd gr send≡ recv≡ td@(_ , a/send _ _ _ , _)
    with at/send-inv td
  ... | _ , _ , w , _
    with waitLeaf gr (∈R refl) w
  ...   | _ , gr′
    with recv-overlap⇒same-comm gr gr′ (∈S refl)
  ...     | refl =
    ⊥-elim (sender≢receiver gr refl)

  receiver/head-progress {P = P} {Q = Q} {i = i}
    M⊢G etd gr send≡ recv≡ td@(_ , a/recv _ _ , _)
    with waitLeaf gr (∈R refl) (proj₁ (at/recv-inv td))
  ... | _ , _ , _ , gr′
    with recv-overlap⇒same-comm gr gr′ (∈R refl)
  ...   | refl
    with step-arity-deterministic gr gr′
  ...     | refl
    with eval-exp etd
  ...       | V , e⇓v =
    just (P ⟶ Q # i < sort/value V >) , _ ,
    s/comm P Q send≡ e⇓v recv≡

  receiver/head-progress M⊢G etd gr send≡ recv≡ (_ , a/if etd′ _ _ , _) =
    if/progress etd′ recv≡

  receiver/head-progress {G = G} M⊢G etd gr send≡ recv≡ (_ , a/end done , mem) =
    ⊥-elim (done {[] , G} mem (in/recv gr))

  receiver/head-progress M⊢G etd gr send≡ recv≡ (_ , a/var {X = ()} _ , _)

  receiver/head-progress {Q = Q}
    M⊢G etd gr send≡ recv≡ (_ , a/rec _ _ _ , _) =
    nothing , _ , s/rec Q recv≡

  -- `P` is active at `G` (it is `gr`'s sender), so `waitLeaf` collapses the
  -- tree walk.
  sender/head-progress :
    ∀ {M G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {Pr : Proc 0 0}
    → ⊢s M ∶ G
    → G -< P ⟶ Q # i < S > >-> G′
    → M [ P ]= Pr
    → [] ⊢at P ◂ Pr ∶ ([] , G)
    → ∃[ β ] ∃[ M′ ] M [ β ]⇒ M′

  sender/head-progress {M = M} M⊢G gr send≡
    td@(_ , a/send {Q = Q′} _ _ _ , _)
    with at/send-inv td
  ... | _ , etd , w , _
    with waitLeaf gr (∈S refl) w
  ...   | _ , gr′ =
    receiver/head-progress
      M⊢G
      etd
      gr′
      send≡
      (lookup⇒[]= Q′ M refl)
      (at/lookup M⊢G (lookup⇒[]= Q′ M refl))

  sender/head-progress M⊢G gr send≡ td@(_ , a/recv _ _ , _)
    with waitLeaf gr (∈S refl) (proj₁ (at/recv-inv td))
  ... | _ , _ , _ , gr′
    with recv-overlap⇒same-comm gr′ gr (∈S refl)
  ...   | refl =
    ⊥-elim (sender≢receiver gr refl)

  sender/head-progress M⊢G gr send≡ (_ , a/if etd _ _ , _) =
    if/progress etd send≡

  sender/head-progress {G = G} M⊢G gr send≡ (_ , a/end done , mem) =
    ⊥-elim (done {[] , G} mem (in/send gr))

  sender/head-progress M⊢G gr send≡ (_ , a/var {X = ()} _ , _)

  sender/head-progress {P = P} M⊢G gr send≡ (_ , a/rec _ _ _ , _) =
    nothing , _ , s/rec P send≡

  step/progress :
    ∀ {M G G′ α}
    → ⊢s M ∶ G
    → G -< α >-> G′
    → ∃[ β ] ∃[ M′ ] M [ β ]⇒ M′
  step/progress {M = M} {α = P ⟶ Q # i < S >} M⊢G gr =
    sender/head-progress
      M⊢G
      gr
      (lookup⇒[]= P M refl)
      (at/lookup M⊢G (lookup⇒[]= P M refl))

  progress :
    ∀ {M G}
    → ⊢s M ∶ G
    → done M ⊎ ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′

  progress {M = M} M⊢G
    with session/status (tabulate (λ P → P)) M⊢G
  ... | ss/step gr =
    inj₂ (step/progress M⊢G gr)
  ... | ss/if etd proc≡ =
    inj₂ (if/progress etd proc≡)
  ... | ss/rec proc≡ =
    inj₂ (nothing , _ , s/rec _ proc≡)
  ... | ss/end ended =
    inj₁ λ P →
      inactive/done
        (all-parts/end ended P)
        (at/lookup M⊢G (lookup⇒[]= P M refl))
