{-# OPTIONS --guardedness #-}

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc)
open import Data.Fin
  using (Fin; zero)
  renaming (_≟_ to _≟f_; suc to fsuc)
open import Data.Vec
  using (Vec; []; _∷_; _[_]=_; lookup; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Data.Maybe.Base using (just; nothing)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; sym)
open import Utils.Fin using (lookup-get)
open import Definitions

import SubstitutionProperties
import Safety.Head
import Safety.Preservation

module Safety.Progress {N : ℕ}{B : BTheory N}(BP : BT-Prop B) where
  private
    module SP = SubstitutionProperties BP
    module H = Safety.Head BP
    module P = Safety.Preservation BP
  open SP
  open SP.M
  open SP.M.Subst
  open H
  open P

  mutual

    message-guarded/∈T/head :
      ∀ {γ G P Pr}
        {Γ : Vec Sort γ}
      → MessageGuarded Pr
      → Γ ⊢head P ◂ Pr ∶ G
      → P ∈T G
    message-guarded/∈T/head mg/send (h/send gr _ _) =
      in/send gr
    message-guarded/∈T/head mg/send (h/skip std) =
      message-guarded/∈T/hskip mg/send std refl
    message-guarded/∈T/head mg/recv (h/recv gr _) =
      in/recv gr
    message-guarded/∈T/head mg/recv (h/skip std) =
      message-guarded/∈T/hskip mg/recv std refl
    message-guarded/∈T/head (mg/if mg₁ _) (h/if _ head₁ _) =
      message-guarded/∈T/head mg₁ head₁
    message-guarded/∈T/head guarded@(mg/if _ _) (h/skip std) =
      message-guarded/∈T/hskip guarded std refl

    message-guarded/∈T/hskip :
      ∀ {γ ξ m G P Pr}
        {Γ : Vec Sort γ}
        {Ξ : Vec Behav ξ}
      → MessageGuarded Pr
      → Γ & Ξ ⊢hskip[ m ] P ◂ Pr ∶ G
      → m ≡ prod
      → P ∈T G
    message-guarded/∈T/hskip guarded (skip/main head) _ =
      message-guarded/∈T/head guarded head
    message-guarded/∈T/hskip guarded (skip/step gr _ ktd mode-gr) _ =
      in/later gr (message-guarded/∈T/hskip guarded (ktd gr .proj₂) mode-gr)
    message-guarded/∈T/hskip guarded (skip/cycle _) ()

  mutual

    not-in-type/done/head :
      ∀ {G P Pr}
      → P ∉T G
      → [] ⊢head P ◂ Pr ∶ G
      → done/proc Pr
    not-in-type/done/head P∉G (h/send gr _ _) =
      ⊥-elim (P∉G (in/send gr))
    not-in-type/done/head P∉G (h/recv gr _) =
      ⊥-elim (P∉G (in/recv gr))
    not-in-type/done/head P∉G (h/skip std) =
      not-in-type/done/hskip P∉G std refl
    not-in-type/done/head P∉G (h/if _ head₁ head₂) =
      done-if
        (not-in-type/done/head P∉G head₁)
        (not-in-type/done/head P∉G head₂)
    not-in-type/done/head P∉G htd@(h/rec _ guarded _) =
      ⊥-elim
        (P∉G
          (message-guarded/∈T/head
            (message-guarded/proc-subst guarded)
            (td/head
              (t/rec/unfold (head/typing htd))
              skip/refl)))
    not-in-type/done/head _ (h/end _) =
      done-∅

    not-in-type/done/hskip :
      ∀ {ξ m G P Pr}
        {Ξ : Vec Behav ξ}
      → P ∉T G
      → [] & Ξ ⊢hskip[ m ] P ◂ Pr ∶ G
      → m ≡ prod
      → done/proc Pr
    not-in-type/done/hskip P∉G (skip/main head) _ =
      not-in-type/done/head P∉G head
    not-in-type/done/hskip P∉G (skip/step gr _ ktd mode-gr) _ =
      not-in-type/done/hskip
        (P∉G ∘ in/later gr)
        (ktd gr .proj₂)
        mode-gr
    not-in-type/done/hskip P∉G (skip/cycle _) ()

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

  session/status/cons-end :
    ∀ {I M G P}
      {Ps : Vec Part I}
    → P ∉T G
    → SessionStatus M G Ps
    → SessionStatus M G (P ∷ Ps)
  session/status/cons-end _ (ss/step gr) =
    ss/step gr
  session/status/cons-end _ (ss/if etd proc≡) =
    ss/if etd proc≡
  session/status/cons-end _ (ss/rec proc≡) =
    ss/rec proc≡
  session/status/cons-end P∉G (ss/end done) =
    ss/end λ
      { zero     → P∉G
      ; (fsuc i) → done i
      }

  mutual

    head/session-status :
      ∀ {I M G P Pr}
        {Ps : Vec Part I}
      → SessionStatus M G Ps
      → M [ P ]= Pr
      → [] ⊢head P ◂ Pr ∶ G
      → SessionStatus M G (P ∷ Ps)
    head/session-status _ _ (h/send gr _ _) =
      ss/step gr
    head/session-status _ _ (h/recv gr _) =
      ss/step gr
    head/session-status tail proc≡ (h/skip std) =
      hskip/session-status tail proc≡ std
    head/session-status _ proc≡ (h/if etd _ _) =
      ss/if etd proc≡
    head/session-status _ proc≡ (h/rec _ _ _) =
      ss/rec proc≡
    head/session-status tail _ (h/end done) =
      session/status/cons-end done tail

    hskip/session-status :
      ∀ {I ξ M G P Pr}
        {Ps : Vec Part I}
        {Ξ : Vec Behav ξ}
      → SessionStatus M G Ps
      → M [ P ]= Pr
      → [] & Ξ ⊢hskip[ prod ] P ◂ Pr ∶ G
      → SessionStatus M G (P ∷ Ps)
    hskip/session-status tail proc≡ (skip/main head) =
      head/session-status tail proc≡ head
    hskip/session-status _ _ (skip/step gr _ _ _) =
      ss/step gr

  session/status :
    ∀ {I M G}
    → (Ps : Vec Part I)
    → ⊢s M ∶ G
    → SessionStatus M G Ps

  session/status [] M⊢G =
    ss/end λ ()

  session/status {M = M} (P ∷ Ps) M⊢G =
    head/session-status
      (session/status Ps M⊢G)
      (lookup-get refl)
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
        (lookup-get refl)
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
      (lookup-get refl)
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
      not-in-type/done/head
        (all-parts/end ended P)
        (td/head (M⊢G P) skip/refl)
