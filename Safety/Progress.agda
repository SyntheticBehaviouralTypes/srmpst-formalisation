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
import Definitions.Typing.Algorithmic as Alg

module Safety.Progress {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  private
    module M = MPST wb
  open M
  open Alg wb using (_&_⊢a_∶_; _&_⊢blocked_∶_; a/skip; a/if; a/end;
                     blocked/send; blocked/recv; blocked/var; blocked/rec)
  open M.Subst
  open import Definitions.Typing.Substitution wb
  open import Definitions.Typing.Norm wb using (norm)
  open import Safety.Preservation wb

  -- `⊢a` splits these differently from `⊢head`: the six-way case becomes a
  -- three-way one on `⊢a` (`a/skip`/`a/if`/`a/end`) with the send/recv/rec
  -- analysis pushed down into the `⊢blocked` leaf.  Two clauses that had to
  -- be written out under `⊢head` vanish, because `MessageGuarded` has no
  -- constructor for `∅`/`v`/`rec` and `⊢blocked` has none for `ifp` —
  -- Agda discharges all four by coverage.
  mutual

    guarded/active :
      ∀ {γ δ G P Pr}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
      → MessageGuarded Pr
      → Γ & Δ ⊢a P ◂ Pr ∶ G
      → P ∈T G
    guarded/active guarded (a/skip std) =
      guarded/active-skip guarded std
    guarded/active (mg/if mg₁ _) (a/if _ ttd _) =
      guarded/active mg₁ ttd

    guarded/active-skip :
      ∀ {γ δ ξ G P Pr}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {Ξ : Vec Behav ξ}
      → MessageGuarded Pr
      → (Γ & Δ ⊢blocked_∶_) & Ξ ⊢skip P ◂ Pr ∶ G
      → P ∈T G
    guarded/active-skip guarded (skip/main bl) =
      guarded/blocked guarded bl
    guarded/active-skip guarded (skip/step gr _ ktd) =
      in/later gr (guarded/active-skip guarded (ktd gr))
    guarded/active-skip guarded (skip/cycle _ inT) =
      inT

    guarded/blocked :
      ∀ {γ δ G P Pr}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
      → MessageGuarded Pr
      → Γ & Δ ⊢blocked P ◂ Pr ∶ G
      → P ∈T G
    guarded/blocked mg/send (blocked/send gr _ _) =
      in/send gr
    guarded/blocked mg/recv (blocked/recv gr _) =
      in/recv gr

  mutual

    inactive/done :
      ∀ {G P Pr}
      → P ∉T G
      → [] & [] ⊢a P ◂ Pr ∶ G
      → done/proc Pr
    inactive/done P∉G (a/skip std) =
      inactive/done-skip P∉G std
    inactive/done P∉G (a/if _ ttd ftd) =
      done-if
        (inactive/done P∉G ttd)
        (inactive/done P∉G ftd)
    inactive/done _ (a/end _) =
      done-∅

    inactive/done-skip :
      ∀ {ξ G P Pr}
        {Ξ : Vec Behav ξ}
      → P ∉T G
      → ([] & [] ⊢blocked_∶_) & Ξ ⊢skip P ◂ Pr ∶ G
      → done/proc Pr
    inactive/done-skip P∉G (skip/main bl) =
      inactive/done-blocked P∉G bl
    inactive/done-skip P∉G (skip/step gr _ ktd) =
      inactive/done-skip (P∉G ∘ in/later gr) (ktd gr)
    inactive/done-skip P∉G (skip/cycle _ inT) =
      ⊥-elim (P∉G inT)

    -- `blocked/var` is impossible: Safety is all `δ = 0`, so `X : Fin 0`.
    -- `blocked/rec` reproduces the old `h/rec` argument — unfold the
    -- recursion AT THE LEAF, where the guarded body forces `P ∈T`.
    -- Entirely within `⊢a` as far as this file is concerned:
    -- `a/rec/unfold` (`Typing/Substitution.agda`) is `⊢a`-stated, and the
    -- `⊢p` round trip that proves it is confined to that module.
    inactive/done-blocked :
      ∀ {G P Pr}
      → P ∉T G
      → [] & [] ⊢blocked P ◂ Pr ∶ G
      → done/proc Pr
    inactive/done-blocked P∉G (blocked/send gr _ _) =
      ⊥-elim (P∉G (in/send gr))
    inactive/done-blocked P∉G (blocked/recv gr _) =
      ⊥-elim (P∉G (in/recv gr))
    inactive/done-blocked P∉G (blocked/var {X = ()} _ _)
    inactive/done-blocked P∉G btd@(blocked/rec _ guarded _) =
      ⊥-elim
        (P∉G
          (guarded/active
            (guarded/subst-proc guarded)
            (a/rec/unfold (a/skip (skip/main btd)))))

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

  mutual

    head/status :
      ∀ {I M G P Pr}
        {Ps : Vec Part I}
      → SessionStatus M G Ps
      → M [ P ]= Pr
      → [] & [] ⊢a P ◂ Pr ∶ G
      → SessionStatus M G (P ∷ Ps)
    head/status tail proc≡ (a/skip std) =
      skip/status tail proc≡ std
    head/status _ proc≡ (a/if etd _ _) =
      ss/if etd proc≡
    head/status tail _ (a/end done) =
      status/cons done tail

    -- `Ξ = []` kills `skip/cycle` (`X : Fin 0`), exactly as it did for
    -- `⊢hskip`, so this still needs only the two clauses.
    skip/status :
      ∀ {I M G P Pr}
        {Ps : Vec Part I}
      → SessionStatus M G Ps
      → M [ P ]= Pr
      → ([] & [] ⊢blocked_∶_) & [] ⊢skip P ◂ Pr ∶ G
      → SessionStatus M G (P ∷ Ps)
    skip/status tail proc≡ (skip/main bl) =
      blocked/status tail proc≡ bl
    skip/status _ _ (skip/step gr _ _) =
      ss/step gr

    blocked/status :
      ∀ {I M G P Pr}
        {Ps : Vec Part I}
      → SessionStatus M G Ps
      → M [ P ]= Pr
      → [] & [] ⊢blocked P ◂ Pr ∶ G
      → SessionStatus M G (P ∷ Ps)
    blocked/status _ _ (blocked/send gr _ _) =
      ss/step gr
    blocked/status _ _ (blocked/recv gr _) =
      ss/step gr
    blocked/status _ _ (blocked/var {X = ()} _ _)
    blocked/status _ proc≡ (blocked/rec _ _ _) =
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
      (lookup⇒[]= _ _ refl)
      (norm (M⊢G P) skip/refl)

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

  mutual

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
      → [] & [] ⊢a Q ◂ QPr ∶ G
      → ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′
    receiver/head-progress M⊢G etd gr send≡ recv≡ (a/skip std) =
      receiver/hskip-progress M⊢G etd gr send≡ recv≡ std
    receiver/head-progress M⊢G etd gr send≡ recv≡ (a/if etd′ _ _) =
      if/progress etd′ recv≡
    receiver/head-progress M⊢G etd gr send≡ recv≡ (a/end done) =
      ⊥-elim (done (in/recv gr))

    receiver/hskip-progress :
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
      → ([] & [] ⊢blocked_∶_) & [] ⊢skip Q ◂ QPr ∶ G
      → ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′
    receiver/hskip-progress M⊢G etd gr send≡ recv≡ (skip/main bl) =
      receiver/blocked-progress M⊢G etd gr send≡ recv≡ bl
    receiver/hskip-progress M⊢G etd gr send≡ recv≡
      (skip/step _ Q∉G _) =
      ⊥-elim (∉c→¬∈c (Q∉G gr) (∈R refl))

    receiver/blocked-progress :
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
      → [] & [] ⊢blocked Q ◂ QPr ∶ G
      → ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′
    receiver/blocked-progress M⊢G etd gr send≡ recv≡ (blocked/send gr′ _ _)
      with recv-overlap⇒same-comm gr gr′ (∈S refl)
    ... | refl =
      ⊥-elim (sender≢receiver gr refl)
    receiver/blocked-progress {P = P} {Q = Q} {i = i}
      M⊢G etd gr send≡ recv≡ (blocked/recv gr′ _)
      with recv-overlap⇒same-comm gr gr′ (∈R refl)
    ... | refl
      with step-arity-deterministic gr gr′
    ...   | refl
      with eval-exp etd
    ...     | V , e⇓v =
      just (P ⟶ Q # i < sort/value V >) , _ ,
      s/comm P Q send≡ e⇓v recv≡
    receiver/blocked-progress M⊢G etd gr send≡ recv≡
      (blocked/var {X = ()} _ _)
    receiver/blocked-progress {Q = Q} M⊢G etd gr send≡ recv≡
      (blocked/rec _ _ _) =
      nothing , _ , s/rec Q recv≡

    sender/head-progress :
      ∀ {M G G′ P Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {Pr : Proc 0 0}
      → ⊢s M ∶ G
      → G -< P ⟶ Q # i < S > >-> G′
      → M [ P ]= Pr
      → [] & [] ⊢a P ◂ Pr ∶ G
      → ∃[ β ] ∃[ M′ ] M [ β ]⇒ M′
    sender/head-progress M⊢G gr send≡ (a/skip std) =
      sender/hskip-progress M⊢G gr send≡ std
    sender/head-progress M⊢G gr send≡ (a/if etd _ _) =
      if/progress etd send≡
    sender/head-progress M⊢G gr send≡ (a/end done) =
      ⊥-elim (done (in/send gr))

    sender/hskip-progress :
      ∀ {M G G′ P Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {Pr : Proc 0 0}
      → ⊢s M ∶ G
      → G -< P ⟶ Q # i < S > >-> G′
      → M [ P ]= Pr
      → ([] & [] ⊢blocked_∶_) & [] ⊢skip P ◂ Pr ∶ G
      → ∃[ β ] ∃[ M′ ] M [ β ]⇒ M′
    sender/hskip-progress M⊢G gr send≡ (skip/main bl) =
      sender/blocked-progress M⊢G gr send≡ bl
    sender/hskip-progress M⊢G gr send≡ (skip/step _ P∉G _) =
      ⊥-elim (∉c→¬∈c (P∉G gr) (∈S refl))

    sender/blocked-progress :
      ∀ {M G G′ P Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {Pr : Proc 0 0}
      → ⊢s M ∶ G
      → G -< P ⟶ Q # i < S > >-> G′
      → M [ P ]= Pr
      → [] & [] ⊢blocked P ◂ Pr ∶ G
      → ∃[ β ] ∃[ M′ ] M [ β ]⇒ M′
    sender/blocked-progress M⊢G gr send≡ (blocked/send {Q = Q′} gr′ etd _) =
      receiver/head-progress
        M⊢G
        etd
        gr′
        send≡
        (lookup⇒[]= _ _ refl)
        (norm (M⊢G Q′) skip/refl)
    sender/blocked-progress M⊢G gr send≡ (blocked/recv gr′ _)
      with recv-overlap⇒same-comm gr′ gr (∈S refl)
    ... | refl =
      ⊥-elim (sender≢receiver gr refl)
    sender/blocked-progress M⊢G gr send≡ (blocked/var {X = ()} _ _)
    sender/blocked-progress {P = P} M⊢G gr send≡ (blocked/rec _ _ _) =
      nothing , _ , s/rec P send≡

  step/progress :
    ∀ {M G G′ α}
    → ⊢s M ∶ G
    → G -< α >-> G′
    → ∃[ β ] ∃[ M′ ] M [ β ]⇒ M′
  step/progress {α = P ⟶ Q # i < S >} M⊢G gr =
    sender/head-progress
      M⊢G
      gr
      (lookup⇒[]= _ _ refl)
      (norm (M⊢G P) skip/refl)

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
        -- `⊢s` gives `⊢p`; go straight to `⊢a` and stay there.
        (norm (M⊢G P) skip/refl)
