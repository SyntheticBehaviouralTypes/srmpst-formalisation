{-# OPTIONS --guardedness #-}

open import Data.Empty using (⊥; ⊥-elim)

open import Data.Nat using (ℕ; _+_; _<_; _≤_; _⊔_; s≤s; suc)
open import Data.Nat.Induction using (<-wellFounded)

open import Data.Nat.Properties
  using
    ( +-mono-<-≤
    ; +-mono-≤
    ; +-mono-≤-<
    ; <⇒≤
    ; ≤-refl
    ; m≤n⇒m≤n⊔o
    ; m≤n⇒m≤o⊔n
    )

open import Induction.WellFounded using (Acc; acc)

open import Data.Fin
  using    (Fin; zero)
  renaming (_≟_ to _≟f_; suc to fsuc)

open import Data.Vec
  using (Vec; []; _∷_; _[_]=_; _[_]≔_; lookup; tabulate)

open import Data.Vec.Properties
  using (lookup∘tabulate; lookup∘update; lookup∘update′)

open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe.Base using (just; nothing)
open import Function     using (_∘_)

open import Relation.Nullary using (¬_; yes; no)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; sym)

open import Utils.Fin using (lookup-get; reflect-lookup)
open import Definitions

import SubstitutionProperties

module Safety {N : ℕ}{B : BTheory N}(BP : BT-Prop B) where
  open module SP = SubstitutionProperties(BP)
  open SP.M
  open SP.M.Subst

  td/lookup :
    ∀ {M G P Pr}
    → ⊢s M ∶ G
    → M [ P ]= Pr
    → [] & [] ⊢p P ◂ Pr ∶ G
  td/lookup {P = P} ts luP with ts P
  ... | ptd rewrite reflect-lookup luP = ptd

  ⊢s-update :
    ∀ (M : Session) {G P Pr}
    → ⊢s M ∶ G
    → [] & [] ⊢p P ◂ Pr ∶ G
    → ⊢s M [ P ]≔ Pr ∶ G

  ⊢s-update M {P = P} {Pr = Pr} M⊢G Pr⊢G Q
    with Q ≟f P
  ... | yes refl
    rewrite lookup∘update P M Pr =
    Pr⊢G
  ... | no Q≢P
    rewrite lookup∘update′ Q≢P M Pr =
    M⊢G Q


  t/if/inv :
    ∀ {G P E Pr Pr′ Pr″}
    → Pr ≡ ifp E then Pr′ else Pr″
    → [] & [] ⊢p P ◂ Pr ∶ G
    → ([] ⊢e E ∶ s/bool)
    × ([] & [] ⊢p P ◂ Pr′ ∶ G)
    × ([] & [] ⊢p P ◂ Pr″ ∶ G)

  t/if/inv refl (t/if e ptd′ ptd″) =
    e , ptd′ , ptd″

  t/if/inv refl (t/skip gr na ktd) =
    proj₁ (t/if/inv refl (ktd gr)) ,
    t/skip gr na (proj₁ ∘ proj₂ ∘ t/if/inv refl ∘ ktd) ,
    t/skip gr na (proj₂ ∘ proj₂ ∘ t/if/inv refl ∘ ktd)

  t/if/inv refl (t/unskip tr td)
    with t/if/inv refl td
  ... | e , ptd′ , ptd″ =
    e ,
    t/unskip tr ptd′ ,
    t/unskip tr ptd″

  t/rec/unfold :
    ∀ {G P Pr}
    → [] & [] ⊢p P ◂ rec Pr ∶ G
    → [] & [] ⊢p P ◂ unfold/proc Pr ∶ G

  t/rec/unfold (t/rec mmg ptd) =
    proc-subst-lemma (t/rec mmg ptd) ptd

  t/rec/unfold (t/skip gr na ktd) =
    t/skip gr na (t/rec/unfold ∘ ktd)

  t/rec/unfold (t/unskip tr td) =
    t/unskip tr (t/rec/unfold td)


  subject-reduction/τ :
    ∀ {G M'}
    → (M : Session)
    → ⊢s M ∶ G
    → M [ nothing ]⇒ M'
    → ⊢s M' ∶ G

  subject-reduction/τ M M⊢G (s/if/true P Ptt e⇓true)
    with t/if/inv refl (td/lookup M⊢G Ptt)
  ... | _ , ptd-then , _ =
    ⊢s-update M M⊢G ptd-then

  subject-reduction/τ M M⊢G (s/if/false P Ptt e⇓false)
    with t/if/inv refl (td/lookup M⊢G Ptt)
  ... | _ , _ , ptd-else =
    ⊢s-update M M⊢G ptd-else

  subject-reduction/τ M M⊢G (s/rec P Prec) =
    ⊢s-update M M⊢G (t/rec/unfold (td/lookup M⊢G Prec))

  subject-reduction/τ* :
    ∀ {G M M'}
    → ⊢s M ∶ G
    → M τ⇒ M'
    → ⊢s M' ∶ G

  subject-reduction/τ* M⊢G s/zero =
    M⊢G
  subject-reduction/τ* M⊢G (s/more st tr) =
    subject-reduction/τ* (subject-reduction/τ _ M⊢G st) tr

  permute/unskip :
    ∀ {γ P Pr G G′}
      {Γ : Vec Sort γ}
    → G -[¬ P ]->* G′
    → Γ & [] ⊢p P ◂ Pr ∶ G
    → Γ & [] ⊢p P ◂ Pr ∶ G′
  permute/unskip tr (t/unskip tr′ td) =
    permute/unskip (unskip/cat tr′ tr) td
  permute/unskip unskip/refl td =
    td
  permute/unskip tr (t/send gr etd td) =
    t/send
      (unskip/advance-step tr gr (∈S refl))
      etd
      (permute/unskip (unskip/advance-trace tr gr (∈S refl)) td)
  permute/unskip tr (t/recv gr conts) =
    t/recv (unskip/advance-step tr gr (∈R refl)) λ gr″ →
      permute/unskip
        (branch/before-trace tr gr gr″)
        (conts (branch/before-step tr gr gr″))
  permute/unskip (unskip/step gr _ tr) (t/skip _ _ ktd) =
    permute/unskip tr (ktd gr)
  permute/unskip tr (t/if etd ttd ftd) =
    t/if etd (permute/unskip tr ttd) (permute/unskip tr ftd)
  permute/unskip tr td@(t/rec _ _) =
    t/unskip tr td
  permute/unskip tr (t/var {X = ()} _)
  permute/unskip tr (t/end done) =
    t/end (done ∘ unskip/∈T-back tr)

  data TypingHead {γ}
    (Γ : Vec Sort γ)
    (P : Part)
    : Proc γ 0 → Behav → Set
    where

    h/send :
      ∀ {Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {E : Exp γ}
        {Pr : Proc γ 0}
        {G G′ : Behav}
      → G -< P ⟶ Q # i < S > >-> G′
      → Γ ⊢e E ∶ S
      → Γ & [] ⊢p P ◂ Pr ∶ G′
      → TypingHead Γ P (Q ! i < E >∙ Pr) G

    h/recv :
      ∀ {Q I}
        {i : Fin (suc I)}
        {T : Sort}
        {S : Vec Sort (suc I)}
        {Br : Vec (Proc (suc γ) 0) (suc I)}
        {G G′ : Behav}
      → G -< Q ⟶ P # i < T > >-> G′
      → (∀ {j U G″}
          → G -< Q ⟶ P # j < U > >-> G″
          → (U ∷ Γ) & [] ⊢p P ◂ lookup Br j ∶ G″)
      → TypingHead Γ P (Σ Q ？[ S ]· Br) G

    h/skip :
      ∀ {Pr : Proc γ 0}
        {G G′ : Behav}
        {α : Action}
      → (gr : G -< α >-> G′)
      → (na : P not-active-in G)
      → (ktd :
          ∀ {G″ α′}
          → G -< α′ >-> G″
          → TypingHead Γ P Pr G″)
      → TypingHead Γ P Pr G

    h/if :
      ∀ {E : Exp γ}
        {Pr Pr′ : Proc γ 0}
        {G : Behav}
      → Γ ⊢e E ∶ s/bool
      → TypingHead Γ P Pr G
      → TypingHead Γ P Pr′ G
      → TypingHead Γ P (ifp E then Pr else Pr′) G

    h/rec :
      ∀ {Pr : Proc γ 1}
        {G G′ : Behav}
      → G -[¬ P ]->* G′
      → MessageGuarded Pr
      → Γ & G ∷ [] ⊢p P ◂ Pr ∶ G
      → TypingHead Γ P (rec Pr) G′

    h/end :
      ∀ {G : Behav}
      → ¬ P ∈T G
      → TypingHead Γ P ∅ G

  td/head :
    ∀ {γ P Pr G G′}
      {Γ : Vec Sort γ}
    → G -[¬ P ]->* G′
    → Γ & [] ⊢p P ◂ Pr ∶ G
    → TypingHead Γ P Pr G′

  td/head tr (t/unskip tr′ td) =
    td/head (unskip/cat tr′ tr) td

  td/head tr (t/send gr etd td) =
    h/send
      (unskip/advance-step tr gr (∈S refl))
      etd
      (permute/unskip (unskip/advance-trace tr gr (∈S refl)) td)

  td/head tr (t/recv gr conts) =
    h/recv (unskip/advance-step tr gr (∈R refl)) λ gr″ →
      permute/unskip
        (branch/before-trace tr gr gr″)
        (conts (branch/before-step tr gr gr″))

  td/head unskip/refl (t/skip gr na ktd) =
    h/skip gr na (td/head unskip/refl ∘ ktd)

  td/head (unskip/step gr _ tr) (t/skip _ _ ktd) =
    td/head tr (ktd gr)

  td/head tr (t/if etd ttd ftd) =
    h/if etd (td/head tr ttd) (td/head tr ftd)

  td/head tr (t/rec guarded td) =
    h/rec tr guarded td

  td/head _ (t/var {X = ()} _)

  td/head tr (t/end done) =
    h/end (done ∘ unskip/∈T-back tr)

  data ProcessStatus
    (G : Behav)
    (P : Part)
    : Proc 0 0 → Set
    where

    ps/step :
      ∀ {Pr α G′}
      → G -< α >-> G′
      → ProcessStatus G P Pr

    ps/if :
      ∀ {Pr E Pr′ Pr″}
      → [] ⊢e E ∶ s/bool
      → Pr ≡ ifp E then Pr′ else Pr″
      → ProcessStatus G P Pr

    ps/rec :
      ∀ {Pr Pr′}
      → Pr ≡ rec Pr′
      → ProcessStatus G P Pr

    ps/end :
      ∀ {Pr}
      → P ∉T G
      → ProcessStatus G P Pr

  process/status/head :
    ∀ {G P Pr}
    → TypingHead [] P Pr G
    → ProcessStatus G P Pr
  process/status/head (h/send gr _ _) =
    ps/step gr
  process/status/head (h/recv gr _) =
    ps/step gr
  process/status/head (h/skip gr _ _) =
    ps/step gr
  process/status/head (h/if etd _ _) =
    ps/if etd refl
  process/status/head (h/rec _ _ _) =
    ps/rec refl
  process/status/head (h/end done) =
    ps/end done

  process/status :
    ∀ {G P Pr}
    → [] & [] ⊢p P ◂ Pr ∶ G
    → ProcessStatus G P Pr
  process/status =
    process/status/head ∘ td/head unskip/refl

  message-guarded/∈T/head :
    ∀ {γ G P Pr}
      {Γ : Vec Sort γ}
    → MessageGuarded Pr
    → TypingHead Γ P Pr G
    → P ∈T G
  message-guarded/∈T/head mg/send (h/send gr _ _) =
    in/send gr
  message-guarded/∈T/head mg/send (h/skip gr _ ktd) =
    in/later gr (message-guarded/∈T/head mg/send (ktd gr))
  message-guarded/∈T/head mg/recv (h/recv gr _) =
    in/recv gr
  message-guarded/∈T/head mg/recv (h/skip gr _ ktd) =
    in/later gr (message-guarded/∈T/head mg/recv (ktd gr))
  message-guarded/∈T/head (mg/if mg₁ _) (h/if _ head₁ _) =
    message-guarded/∈T/head mg₁ head₁
  message-guarded/∈T/head guarded@(mg/if _ _) (h/skip gr _ ktd) =
    in/later gr (message-guarded/∈T/head guarded (ktd gr))

  message-guarded/∈T/unskip :
    ∀ {γ δ G G′ P Pr}
      {Γ : Vec Sort γ}
      {Δ : Vec Behav δ}
    → G -[¬ P ]->* G′
    → MessageGuarded Pr
    → Γ & Δ ⊢p P ◂ Pr ∶ G
    → P ∈T G′
  message-guarded/∈T/unskip tr mg/send (t/send gr _ _) =
    in/send (unskip/advance-step tr gr (∈S refl))
  message-guarded/∈T/unskip tr mg/recv (t/recv gr _) =
    in/recv (unskip/advance-step tr gr (∈R refl))
  message-guarded/∈T/unskip unskip/refl guarded (t/skip gr _ ktd) =
    in/later gr (message-guarded/∈T/unskip unskip/refl guarded (ktd gr))
  message-guarded/∈T/unskip (unskip/step gr _ tr) guarded (t/skip _ _ ktd) =
    message-guarded/∈T/unskip tr guarded (ktd gr)
  message-guarded/∈T/unskip tr guarded (t/unskip tr′ td) =
    message-guarded/∈T/unskip (unskip/cat tr′ tr) guarded td
  message-guarded/∈T/unskip tr (mg/if guarded _) (t/if _ ttd _) =
    message-guarded/∈T/unskip tr guarded ttd

  not-in-type/done/head :
    ∀ {G P Pr}
    → P ∉T G
    → TypingHead [] P Pr G
    → done/proc Pr
  not-in-type/done/head P∉G (h/send gr _ _) =
    ⊥-elim (P∉G (in/send gr))
  not-in-type/done/head P∉G (h/recv gr _) =
    ⊥-elim (P∉G (in/recv gr))
  not-in-type/done/head P∉G (h/skip gr _ ktd) =
    not-in-type/done/head
      (λ P∈G′ → P∉G (in/later gr P∈G′))
      (ktd gr)
  not-in-type/done/head P∉G (h/if _ head₁ head₂) =
    done-if
      (not-in-type/done/head P∉G head₁)
      (not-in-type/done/head P∉G head₂)
  not-in-type/done/head P∉G (h/rec tr guarded td) =
    ⊥-elim (P∉G (message-guarded/∈T/unskip tr guarded td))
  not-in-type/done/head _ (h/end _) =
    done-∅

  not-in-type/done :
    ∀ {G P Pr}
    → P ∉T G
    → [] & [] ⊢p P ◂ Pr ∶ G
    → done/proc Pr
  not-in-type/done P∉G td =
    not-in-type/done/head P∉G (td/head unskip/refl td)

  data SendView
    (P : Part)
    (G : Behav)
    (Pr : Proc 0 0)
    : Set
    where

    sv/send :
      ∀ {Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {E : Exp 0}
        {Pr′ : Proc 0 0}
        {G′ : Behav}
      → [] ⊢e E ∶ S
      → G -< P ⟶ Q # i < S > >-> G′
      → Pr ≡ Q ! i < E >∙ Pr′
      → SendView P G Pr

    sv/if :
      ∀ {E Pr′ Pr″}
      → [] ⊢e E ∶ s/bool
      → Pr ≡ ifp E then Pr′ else Pr″
      → SendView P G Pr

    sv/rec :
      ∀ {Pr′}
      → Pr ≡ rec Pr′
      → SendView P G Pr

  send/view/head :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {Pr : Proc 0 0}
    → G -< P ⟶ Q # i < S > >-> G′
    → TypingHead [] P Pr G
    → SendView P G Pr
  send/view/head _ (h/send gr etd _) =
    sv/send etd gr refl
  send/view/head gr (h/recv gr′ _)
    with recv-overlap⇒same-comm gr′ gr (∈S refl)
  ... | refl =
    ⊥-elim (sender≢receiver gr refl)
  send/view/head gr (h/skip _ P∉G _) =
    ⊥-elim (∉c→¬∈c (P∉G gr) (∈S refl))
  send/view/head _ (h/if etd _ _) =
    sv/if etd refl
  send/view/head _ (h/rec _ _ _) =
    sv/rec refl
  send/view/head gr (h/end done) =
    ⊥-elim (done (in/send gr))

  send/view :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {Pr : Proc 0 0}
    → G -< P ⟶ Q # i < S > >-> G′
    → [] & [] ⊢p P ◂ Pr ∶ G
    → SendView P G Pr
  send/view gr td =
    send/view/head gr (td/head unskip/refl td)

  data RecvView
    (P Q : Part)
    {I : ℕ}
    (i : Fin (suc I))
    (G : Behav)
    (Pr : Proc 0 0)
    : Set
    where

    rv/recv :
      ∀ {S : Vec Sort (suc I)}
        {Br : Vec (Proc 1 0) (suc I)}
      → Pr ≡ Σ P ？[ S ]· Br
      → RecvView P Q i G Pr

    rv/if :
      ∀ {E Pr′ Pr″}
      → [] ⊢e E ∶ s/bool
      → Pr ≡ ifp E then Pr′ else Pr″
      → RecvView P Q i G Pr

    rv/rec :
      ∀ {Pr′}
      → Pr ≡ rec Pr′
      → RecvView P Q i G Pr

  recv/view/head :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {Pr : Proc 0 0}
    → G -< P ⟶ Q # i < S > >-> G′
    → TypingHead [] Q Pr G
    → RecvView P Q i G Pr
  recv/view/head gr (h/send gr′ _ _)
    with recv-overlap⇒same-comm gr gr′ (∈S refl)
  ... | refl =
    ⊥-elim (sender≢receiver gr refl)
  recv/view/head gr (h/recv gr′ _)
    with recv-overlap⇒same-comm gr gr′ (∈R refl)
  ... | refl
    with step-arity-deterministic gr gr′
  ...   | refl =
    rv/recv refl
  recv/view/head gr (h/skip _ Q∉G _) =
    ⊥-elim (∉c→¬∈c (Q∉G gr) (∈R refl))
  recv/view/head _ (h/if etd _ _) =
    rv/if etd refl
  recv/view/head _ (h/rec _ _ _) =
    rv/rec refl
  recv/view/head gr (h/end done) =
    ⊥-elim (done (in/recv gr))

  recv/view :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {Pr : Proc 0 0}
    → G -< P ⟶ Q # i < S > >-> G′
    → [] & [] ⊢p Q ◂ Pr ∶ G
    → RecvView P Q i G Pr
  recv/view gr td =
    recv/view/head gr (td/head unskip/refl td)

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

  session/status :
    ∀ {I M G}
    → (Ps : Vec Part I)
    → ⊢s M ∶ G
    → SessionStatus M G Ps

  session/status [] M⊢G =
    ss/end λ ()

  session/status {M = M} (P ∷ Ps) M⊢G
    with process/status (M⊢G P)
  ... | ps/step gr =
    ss/step gr
  ... | ps/if etd eq =
    ss/if etd (lookup-get eq)
  ... | ps/rec eq =
    ss/rec (lookup-get eq)
  ... | ps/end P∉G
    with session/status Ps M⊢G
  ...   | ss/step gr =
    ss/step gr
  ...   | ss/if etd luP =
    ss/if etd luP
  ...   | ss/rec luP =
    ss/rec luP
  ...   | ss/end done =
    ss/end λ
      { zero     → P∉G
      ; (fsuc i) → done i
      }

  ⊢s-comm-update :
    ∀ (M : Session)
      {G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {Pr Pr′}
    → (gr : G -< P ⟶ Q # i < S > >-> G′)
    → ⊢s M ∶ G
    → [] & [] ⊢p P ◂ Pr  ∶ G′
    → [] & [] ⊢p Q ◂ Pr′ ∶ G′
    → ⊢s M [ P ]≔ Pr [ Q ]≔ Pr′ ∶ G′

  ⊢s-comm-update M {P = P} {Q = Q} {Pr = Pr} {Pr′ = Pr′} gr M⊢G Ptd Qtd R
    with R ≟f Q
  ... | yes refl
    rewrite lookup∘update Q (M [ P ]≔ Pr) Pr′ =
    Qtd
  ... | no R≢Q
    rewrite lookup∘update′ R≢Q (M [ P ]≔ Pr) Pr′
    with R ≟f P
  ...   | yes refl
    rewrite lookup∘update P M Pr =
    Ptd
  ...   | no R≢P
    rewrite lookup∘update′ R≢P M Pr =
    permute/unskip (unskip/one gr (R≢P , R≢Q)) (M⊢G R)

  t/send/cont-branch :
    ∀ {G G′ G″ P Q I}
      {i : Fin (suc I)}
      {S T : Sort}
      {E : Exp 0}
      {Pr : Proc 0 0}
    → [] ⊢e E ∶ T
    → [] & [] ⊢p P ◂ Pr ∶ G″
    → G -< P ⟶ Q # i < S > >-> G′
    → G -< P ⟶ Q # i < T > >-> G″
    → [] ⊢e E ∶ S × [] & [] ⊢p P ◂ Pr ∶ G′
  t/send/cont-branch etd td gr gr₀
    with step-sort-deterministic gr gr₀
  ... | refl
    rewrite step-deterministic gr gr₀ =
    etd , td

  t/send/cont :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {E : Exp 0}
      {Pr : Proc 0 0}
    → [] & [] ⊢p P ◂ Q ! i < E >∙ Pr ∶ G
    → G -< P ⟶ Q # i < S > >-> G′
    → [] ⊢e E ∶ S × [] & [] ⊢p P ◂ Pr ∶ G′

  t/send/cont td gr
    with td/head unskip/refl td
  ... | h/send gr₀ etd td′ =
    t/send/cont-branch
      etd
      td′
      gr
      gr₀
  ... | h/skip _ na _ =
    ⊥-elim (∉c→¬∈c (na gr) (∈S refl))

  t/comm/ready/head :
    ∀ {G P Q I}
      {i : Fin (suc I)}
      {E : Exp 0}
      {Pr : Proc 0 0}
      {S : Vec Sort (suc I)}
      {Br : Vec (Proc 1 0) (suc I)}
    → TypingHead [] P (Q ! i < E >∙ Pr) G
    → TypingHead [] Q (Σ P ？[ S ]· Br) G
    → ∃[ T ] ∃[ G′ ] G -< P ⟶ Q # i < T > >-> G′

  t/comm/ready/head (h/send gr _ _) (h/skip _ Q∉G _) =
    ⊥-elim (∉c→¬∈c (Q∉G gr) (∈R refl))

  t/comm/ready/head (h/send gr _ _) _ =
    _ , _ , gr

  t/comm/ready/head (h/skip _ P∉G _) (h/recv gr _) =
    ⊥-elim (∉c→¬∈c (P∉G gr) (∈S refl))

  t/comm/ready/head
    (h/skip grα P∉G headP)
    (h/skip _ Q∉G headQ) =
    let headP′ = headP grα
        headQ′ = headQ grα
        T , _ , grβ = t/comm/ready/head headP′ headQ′
        G′ , gr =
          no-new-comm/step
            grα
            (P∉G grα)
            (Q∉G grα)
            grβ
    in T , G′ , gr

  t/comm/ready :
    ∀ {G P Q I}
      {i : Fin (suc I)}
      {E : Exp 0}
      {Pr : Proc 0 0}
      {S : Vec Sort (suc I)}
      {Br : Vec (Proc 1 0) (suc I)}
    → [] & [] ⊢p P ◂ Q ! i < E >∙ Pr ∶ G
    → [] & [] ⊢p Q ◂ Σ P ？[ S ]· Br ∶ G
    → ∃[ T ] ∃[ G′ ] G -< P ⟶ Q # i < T > >-> G′

  t/comm/ready ptd qtd =
    t/comm/ready/head
      (td/head unskip/refl ptd)
      (td/head unskip/refl qtd)

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

  recv/progress :
    ∀ {M G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {E : Exp 0}
      {Pr : Proc 0 0}
    → ⊢s M ∶ G
    → [] ⊢e E ∶ S
    → G -< P ⟶ Q # i < S > >-> G′
    → M [ P ]= Q ! i < E >∙ Pr
    → RecvView P Q i G (M [ Q ]s)
    → ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′
  recv/progress {P = P} {Q = Q} {i = i} M⊢G etd gr send≡ (rv/recv recv≡)
    with eval-exp etd
  ... | V , e⇓v =
    just (P ⟶ Q # i < sort/value V >) , _ ,
    s/comm P Q send≡ e⇓v (lookup-get recv≡)
  recv/progress M⊢G etd gr send≡ (rv/if etd′ recv≡) =
    if/progress etd′ (lookup-get recv≡)
  recv/progress M⊢G etd gr send≡ (rv/rec recv≡) =
    nothing , _ , s/rec _ (lookup-get recv≡)

  step/progress :
    ∀ {M G G′ α}
    → ⊢s M ∶ G
    → G -< α >-> G′
    → ∃[ β ] ∃[ M′ ] M [ β ]⇒ M′
  step/progress {α = P ⟶ Q # i < S >} M⊢G gr
    with send/view gr (M⊢G P)
  ... | sv/send {Q = Q′} etd gr′ send≡ =
    recv/progress M⊢G etd gr′ (lookup-get send≡) (recv/view gr′ (M⊢G Q′))
  ... | sv/if etd send≡ =
    if/progress etd (lookup-get send≡)
  ... | sv/rec send≡ =
    nothing , _ , s/rec P (lookup-get send≡)

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
      not-in-type/done (all-parts/end ended P) (M⊢G P)

  stepper :
    ∀ {M M′}
    → M [ nothing ]⇒ M′
    → Part
  stepper (s/if/true P _ _) =
    P
  stepper (s/if/false P _ _) =
    P
  stepper (s/rec P _) =
    P

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

  t/rec/message-guarded :
    ∀ {G P Pr}
    → [] & [] ⊢p P ◂ rec Pr ∶ G
    → MessageGuarded Pr
  t/rec/message-guarded (t/skip gr _ ktd) =
    t/rec/message-guarded (ktd gr)
  t/rec/message-guarded (t/unskip _ td) =
    t/rec/message-guarded td
  t/rec/message-guarded (t/rec guarded _) =
    guarded

  τ-depth/stepper-decrease :
    ∀ {G M M′}
    → (M⊢G : ⊢s M ∶ G)
    → (st : M [ nothing ]⇒ M′)
    → τ-depth/proc (M′ [ stepper st ]s)
      < τ-depth/proc (M  [ stepper st ]s)
  τ-depth/stepper-decrease
    {M = M}
    M⊢G
    (s/if/true {E = E} {Pr = Pr} {Pr' = Pr′} P proc≡ _)
    rewrite lookup∘update P M Pr
          | reflect-lookup proc≡ =
    τ-depth/if-then {E = E} {Pr = Pr} {Pr′ = Pr′}
  τ-depth/stepper-decrease
    {M = M}
    M⊢G
    (s/if/false {E = E} {Pr = Pr} {Pr' = Pr′} P proc≡ _)
    rewrite lookup∘update P M Pr′
          | reflect-lookup proc≡ =
    τ-depth/if-else {E = E} {Pr = Pr} {Pr′ = Pr′}
  τ-depth/stepper-decrease
    {M = M}
    M⊢G
    (s/rec {Pr = Pr} P proc≡)
    rewrite lookup∘update P M (unfold/proc Pr)
          | reflect-lookup proc≡ =
    τ-depth/unfold<rec
      (t/rec/message-guarded (td/lookup M⊢G proc≡))

  τ-depth/step-nonincreasing :
    ∀ {G M M′}
    → (P : Part)
    → (M⊢G : ⊢s M ∶ G)
    → (st : M [ nothing ]⇒ M′)
    → τ-depth/proc (M′ [ P ]s)
      ≤ τ-depth/proc (M  [ P ]s)
  τ-depth/step-nonincreasing P M⊢G st
    with P ≟f stepper st
  ... | yes refl =
    <⇒≤ (τ-depth/stepper-decrease M⊢G st)
  τ-depth/step-nonincreasing {M = M} P M⊢G (s/if/true {Pr = Pr} Q _ _) | no P≢Q
    rewrite lookup∘update′ P≢Q M Pr =
    ≤-refl
  τ-depth/step-nonincreasing {M = M} P M⊢G (s/if/false {Pr' = Pr′} Q _ _) | no P≢Q
    rewrite lookup∘update′ P≢Q M Pr′ =
    ≤-refl
  τ-depth/step-nonincreasing {M = M} P M⊢G (s/rec {Pr = Pr} Q _) | no P≢Q
    rewrite lookup∘update′ P≢Q M (unfold/proc Pr) =
    ≤-refl

  τ-depth/session-aux :
    ∀ {I}
    → Vec Part I
    → Session
    → ℕ
  τ-depth/session-aux [] M =
    0
  τ-depth/session-aux (P ∷ Ps) M =
    τ-depth/proc (M [ P ]s) + τ-depth/session-aux Ps M

  τ-depth/session :
    Session
    → ℕ
  τ-depth/session M =
    τ-depth/session-aux (tabulate (λ P → P)) M

  τ-depth/session-aux-nonincreasing :
    ∀ {I G M M′}
    → (Ps : Vec Part I)
    → (M⊢G : ⊢s M ∶ G)
    → (st : M [ nothing ]⇒ M′)
    → τ-depth/session-aux Ps M′
      ≤ τ-depth/session-aux Ps M
  τ-depth/session-aux-nonincreasing [] M⊢G st =
    ≤-refl
  τ-depth/session-aux-nonincreasing (P ∷ Ps) M⊢G st =
    +-mono-≤
      (τ-depth/step-nonincreasing P M⊢G st)
      (τ-depth/session-aux-nonincreasing Ps M⊢G st)

  τ-depth/session-aux-decrease :
    ∀ {I G M M′}
    → (i  : Fin I)
    → (Ps : Vec Part I)
    → (M⊢G : ⊢s M ∶ G)
    → (st : M [ nothing ]⇒ M′)
    → lookup Ps i ≡ stepper st
    → τ-depth/session-aux Ps M′
      < τ-depth/session-aux Ps M
  τ-depth/session-aux-decrease zero (_ ∷ Ps) M⊢G st refl =
    +-mono-<-≤
      (τ-depth/stepper-decrease M⊢G st)
      (τ-depth/session-aux-nonincreasing Ps M⊢G st)
  τ-depth/session-aux-decrease (fsuc i) (P ∷ Ps) M⊢G st eq =
    +-mono-≤-<
      (τ-depth/step-nonincreasing P M⊢G st)
      (τ-depth/session-aux-decrease i Ps M⊢G st eq)

  τ-depth/decrease :
    ∀ {G M M′}
    → (M⊢G : ⊢s M ∶ G)
    → (st : M [ nothing ]⇒ M′)
    → τ-depth/session M′ < τ-depth/session M
  τ-depth/decrease M⊢G st =
    τ-depth/session-aux-decrease
      (stepper st)
      (tabulate (λ P → P))
      M⊢G
      st
      (lookup∘tabulate (λ P → P) (stepper st))

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
    rewrite sym (reflect-lookup proc≡) =
    doneM P

  done-rec⊥ :
    ∀ {γ δ}
      {Pr : Proc γ (suc δ)}
    → done/proc (rec Pr)
    → ⊥
  done-rec⊥ ()

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
  still-done {M = M} (s/rec {Pr = Pr} P proc≡) doneM Q
    with Q ≟f P
  ... | yes refl =
    ⊥-elim (done-rec⊥ (lookup-done doneM proc≡))
  ... | no Q≢P
    rewrite lookup∘update′ Q≢P M (unfold/proc Pr) =
    doneM Q

  still-done* :
    ∀ {M M′}
    → M τ⇒ M′
    → done M
    → done M′
  still-done* s/zero doneM =
    doneM
  still-done* (s/more st tr) doneM =
    still-done* tr (still-done st doneM)

  ifp≢∅ :
    ∀ {γ δ E}
      {Pr Pr′ : Proc γ δ}
    → ifp E then Pr else Pr′ ≡ ∅
    → ⊥
  ifp≢∅ ()

  rec≢∅ :
    ∀ {γ δ}
      {Pr : Proc γ (suc δ)}
    → rec Pr ≡ ∅
    → ⊥
  rec≢∅ ()

  still-ended :
    ∀ {M M′}
    → (P : Part)
    → M [ nothing ]⇒ M′
    → M  [ P ]s ≡ ∅
    → M′ [ P ]s ≡ ∅
  still-ended {M = M} P (s/if/true {E = E} {Pr = Pr} {Pr' = Pr′} Q proc≡ _) ended
    with P ≟f Q
  ... | yes refl
    rewrite lookup∘update Q M Pr
          | reflect-lookup proc≡ =
    ⊥-elim (ifp≢∅ ended)
  ... | no P≢Q
    rewrite lookup∘update′ P≢Q M Pr =
    ended
  still-ended {M = M} P (s/if/false {E = E} {Pr = Pr} {Pr' = Pr′} Q proc≡ _) ended
    with P ≟f Q
  ... | yes refl
    rewrite lookup∘update Q M Pr′
          | reflect-lookup proc≡ =
    ⊥-elim (ifp≢∅ ended)
  ... | no P≢Q
    rewrite lookup∘update′ P≢Q M Pr′ =
    ended
  still-ended {M = M} P (s/rec {Pr = Pr} Q proc≡) ended
    with P ≟f Q
  ... | yes refl
    rewrite lookup∘update Q M (unfold/proc Pr)
          | reflect-lookup proc≡ =
    ⊥-elim (rec≢∅ ended)
  ... | no P≢Q
    rewrite lookup∘update′ P≢Q M (unfold/proc Pr) =
    ended

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
    with t/if/inv
           refl
           (td/lookup
             {M = M}
             {P = P}
             M⊢G
             (lookup-get {V = M} {x = P} proc≡))
  ... | etd , _ , _
    with eval-bool etd
  ...   | inj₁ e⇓true =
    let st = s/if/true P (lookup-get {V = M} {x = P} proc≡) e⇓true
        M′ , tr , ended =
          final-run/proc
            {M = M [ P ]≔ Pr}
            {P = P}
            Pr
            (subject-reduction/τ M M⊢G st)
            (lookup∘update P M Pr)
            donePr
    in M′ , s/more st tr , ended
  ...   | inj₂ e⇓false =
    let st = s/if/false P (lookup-get {V = M} {x = P} proc≡) e⇓false
        M′ , tr , ended =
          final-run/proc
            {M = M [ P ]≔ Pr′}
            {P = P}
            Pr′
            (subject-reduction/τ M M⊢G st)
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
           (subject-reduction/τ* M⊢G tr)
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
             (subject-reduction/τ M M⊢G st)
             (rs (τ-depth/decrease M⊢G st))
    ...   | M″ , inj₁ (tr , finishedM″) =
      M″ , inj₁ (s/more st tr , finishedM″)
    ...   | M″ , inj₂ (α , tr) =
      M″ , inj₂ (α , s/more st tr)

  t/recv/cont :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {T : Sort}
      {S : Vec Sort (suc I)}
      {Br : Vec (Proc 1 0) (suc I)}
    → [] & [] ⊢p Q ◂ Σ P ？[ S ]· Br ∶ G
    → (gr : G -< P ⟶ Q # i < T > >-> G′)
    → (T ∷ []) & [] ⊢p Q ◂ lookup Br i ∶ G′

  t/recv/cont td gr
    with td/head unskip/refl td
  ... | h/recv _ conts =
    conts gr
  ... | h/skip _ na _ =
    ⊥-elim (∉c→¬∈c (na gr) (∈R refl))

  session-fidelity/comm :
    ∀ (M : Session)
      {G P Q I}
      {i : Fin (suc I)}
      {S : Vec Sort (suc I)}
      {E V Pr Br}
    → ⊢s M ∶ G
    → [] & [] ⊢p P ◂ Q ! i < E >∙ Pr ∶ G
    → [] & [] ⊢p Q ◂ Σ P ？[ S ]· Br ∶ G
    → E ⇓ V
    → ∃[ G′ ]
        G -< P ⟶ Q # i < sort/value V > >-> G′
      × ⊢s M [ P ]≔ Pr [ Q ]≔ ([ val V / zero ]e lookup Br i) ∶ G′

  session-fidelity/comm M M⊢G ptd qtd e⇓v
    with t/comm/ready ptd qtd
  ... | T , G′ , gr =
    let etd , ptd′ = t/send/cont ptd gr
        vtd = exp-pres etd e⇓v
    in
    G′ ,
    subst
      (λ U → _ -< _ ⟶ _ # _ < U > >-> _)
      (sort/value-typed vtd)
      gr ,
    ⊢s-comm-update M gr M⊢G ptd′
      (proc-subst-lemma-expr
        (te/val vtd)
        (t/recv/cont qtd gr))

  session-fidelity :
    ∀ (M : Session)
      {G M' α}
    → ⊢s M ∶ G
    → M [ just α ]⇒ M'
    → ∃[ G' ] G -< α >-> G' × ⊢s M' ∶ G'

  session-fidelity M std (s/comm P Q Psnd e⇓v Precv) =
    session-fidelity/comm
      M
      std
      (td/lookup std Psnd)
      (td/lookup std Precv)
      e⇓v
