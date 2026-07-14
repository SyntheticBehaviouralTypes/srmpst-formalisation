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
open import Definitions

module Safety.Progress {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  private
    module M = Definitions.MPST wb
  open M
  open M.Subst
  open import Typing.Substitution wb
  open import Safety.Head wb
  open import Safety.Preservation wb

  mutual

    guarded/active :
      ∀ {γ G P Pr}
        {Γ : Vec Sort γ}
      → MessageGuarded Pr
      → Γ ⊢head P ◂ Pr ∶ G
      → P ∈T G
    guarded/active mg/send (h/send gr _ _) =
      in/send gr
    guarded/active mg/send (h/skip std) =
      guarded/active-skip mg/send std refl
    guarded/active mg/recv (h/recv gr _) =
      in/recv gr
    guarded/active mg/recv (h/skip std) =
      guarded/active-skip mg/recv std refl
    guarded/active (mg/if mg₁ _) (h/if _ head₁ _) =
      guarded/active mg₁ head₁
    guarded/active guarded@(mg/if _ _) (h/skip std) =
      guarded/active-skip guarded std refl

    guarded/active-skip :
      ∀ {γ ξ m G P Pr}
        {Γ : Vec Sort γ}
        {Ξ : Vec Behav ξ}
      → MessageGuarded Pr
      → Γ & Ξ ⊢hskip[ m ] P ◂ Pr ∶ G
      → m ≡ prod
      → P ∈T G
    guarded/active-skip guarded (skip/main head) _ =
      guarded/active guarded head
    guarded/active-skip guarded (skip/step gr _ ktd mode-gr) _ =
      in/later gr (guarded/active-skip guarded (ktd gr .proj₂) mode-gr)
    guarded/active-skip guarded (skip/cycle _) ()

  mutual

    inactive/done :
      ∀ {G P Pr}
      → P ∉T G
      → [] ⊢head P ◂ Pr ∶ G
      → done/proc Pr
    inactive/done P∉G (h/send gr _ _) =
      ⊥-elim (P∉G (in/send gr))
    inactive/done P∉G (h/recv gr _) =
      ⊥-elim (P∉G (in/recv gr))
    inactive/done P∉G (h/skip std) =
      inactive/done-skip P∉G std refl
    inactive/done P∉G (h/if _ head₁ head₂) =
      done-if
        (inactive/done P∉G head₁)
        (inactive/done P∉G head₂)
    inactive/done P∉G htd@(h/rec _ guarded _) =
      ⊥-elim
        (P∉G
          (guarded/active
            (guarded/subst-proc guarded)
            (td/head
              (t/rec/unfold (head/typing htd))
              skip/refl)))
    inactive/done _ (h/end _) =
      done-∅

    inactive/done-skip :
      ∀ {ξ m G P Pr}
        {Ξ : Vec Behav ξ}
      → P ∉T G
      → [] & Ξ ⊢hskip[ m ] P ◂ Pr ∶ G
      → m ≡ prod
      → done/proc Pr
    inactive/done-skip P∉G (skip/main head) _ =
      inactive/done P∉G head
    inactive/done-skip P∉G (skip/step gr _ ktd mode-gr) _ =
      inactive/done-skip
        (P∉G ∘ in/later gr)
        (ktd gr .proj₂)
        mode-gr
    inactive/done-skip P∉G (skip/cycle _) ()

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
      → [] ⊢head P ◂ Pr ∶ G
      → SessionStatus M G (P ∷ Ps)
    head/status _ _ (h/send gr _ _) =
      ss/step gr
    head/status _ _ (h/recv gr _) =
      ss/step gr
    head/status tail proc≡ (h/skip std) =
      skip/status tail proc≡ std
    head/status _ proc≡ (h/if etd _ _) =
      ss/if etd proc≡
    head/status _ proc≡ (h/rec _ _ _) =
      ss/rec proc≡
    head/status tail _ (h/end done) =
      status/cons done tail

    skip/status :
      ∀ {I ξ M G P Pr}
        {Ps : Vec Part I}
        {Ξ : Vec Behav ξ}
      → SessionStatus M G Ps
      → M [ P ]= Pr
      → [] & Ξ ⊢hskip[ prod ] P ◂ Pr ∶ G
      → SessionStatus M G (P ∷ Ps)
    skip/status tail proc≡ (skip/main head) =
      head/status tail proc≡ head
    skip/status _ _ (skip/step gr _ _ _) =
      ss/step gr

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
      (td/head (M⊢G P) skip/refl)

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
      → [] ⊢head Q ◂ QPr ∶ G
      → ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′
    receiver/head-progress M⊢G etd gr send≡ recv≡ (h/send gr′ _ _)
      with recv-overlap⇒same-comm gr gr′ (∈S refl)
    ... | refl =
      ⊥-elim (sender≢receiver gr refl)
    receiver/head-progress {P = P} {Q = Q} {i = i}
      M⊢G etd gr send≡ recv≡ (h/recv gr′ _)
      with recv-overlap⇒same-comm gr gr′ (∈R refl)
    ... | refl
      with step-arity-deterministic gr gr′
    ...   | refl
      with eval-exp etd
    ...     | V , e⇓v =
      just (P ⟶ Q # i < sort/value V >) , _ ,
      s/comm P Q send≡ e⇓v recv≡
    receiver/head-progress M⊢G etd gr send≡ recv≡ (h/skip std) =
      receiver/hskip-progress M⊢G etd gr send≡ recv≡ std
    receiver/head-progress M⊢G etd gr send≡ recv≡ (h/if etd′ _ _) =
      if/progress etd′ recv≡
    receiver/head-progress {Q = Q} M⊢G etd gr send≡ recv≡
      (h/rec _ _ _) =
      nothing , _ , s/rec Q recv≡
    receiver/head-progress M⊢G etd gr send≡ recv≡ (h/end done) =
      ⊥-elim (done (in/recv gr))

    receiver/hskip-progress :
      ∀ {ξ M G G′ P Q I}
        {Ξ : Vec Behav ξ}
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
      → [] & Ξ ⊢hskip[ prod ] Q ◂ QPr ∶ G
      → ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′
    receiver/hskip-progress M⊢G etd gr send≡ recv≡ (skip/main head) =
      receiver/head-progress M⊢G etd gr send≡ recv≡ head
    receiver/hskip-progress M⊢G etd gr send≡ recv≡
      (skip/step _ Q∉G _ _) =
      ⊥-elim (∉c→¬∈c (Q∉G gr) (∈R refl))

    sender/head-progress :
      ∀ {M G G′ P Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {Pr : Proc 0 0}
      → ⊢s M ∶ G
      → G -< P ⟶ Q # i < S > >-> G′
      → M [ P ]= Pr
      → [] ⊢head P ◂ Pr ∶ G
      → ∃[ β ] ∃[ M′ ] M [ β ]⇒ M′
    sender/head-progress M⊢G gr send≡ (h/send {Q = Q′} gr′ etd _) =
      receiver/head-progress
        M⊢G
        etd
        gr′
        send≡
        (lookup⇒[]= _ _ refl)
        (td/head (M⊢G Q′) skip/refl)
    sender/head-progress M⊢G gr send≡ (h/recv gr′ _)
      with recv-overlap⇒same-comm gr′ gr (∈S refl)
    ... | refl =
      ⊥-elim (sender≢receiver gr refl)
    sender/head-progress M⊢G gr send≡ (h/skip std) =
      sender/hskip-progress M⊢G gr send≡ std
    sender/head-progress M⊢G gr send≡ (h/if etd _ _) =
      if/progress etd send≡
    sender/head-progress {P = P} M⊢G gr send≡ (h/rec _ _ _) =
      nothing , _ , s/rec P send≡
    sender/head-progress M⊢G gr send≡ (h/end done) =
      ⊥-elim (done (in/send gr))

    sender/hskip-progress :
      ∀ {ξ M G G′ P Q I}
        {Ξ : Vec Behav ξ}
        {i : Fin (suc I)}
        {S : Sort}
        {Pr : Proc 0 0}
      → ⊢s M ∶ G
      → G -< P ⟶ Q # i < S > >-> G′
      → M [ P ]= Pr
      → [] & Ξ ⊢hskip[ prod ] P ◂ Pr ∶ G
      → ∃[ β ] ∃[ M′ ] M [ β ]⇒ M′
    sender/hskip-progress M⊢G gr send≡ (skip/main head) =
      sender/head-progress M⊢G gr send≡ head
    sender/hskip-progress M⊢G gr send≡ (skip/step _ P∉G _ _) =
      ⊥-elim (∉c→¬∈c (P∉G gr) (∈S refl))

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
      (td/head (M⊢G P) skip/refl)

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
        (td/head (M⊢G P) skip/refl)
