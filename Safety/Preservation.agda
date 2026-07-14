{-# OPTIONS --guardedness #-}

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero) renaming (_≟_ to _≟f_)
open import Data.Vec
  using (Vec; []; _∷_; _[_]=_; _[_]≔_; lookup)
open import Data.Vec.Properties
  using (lookup∘update; lookup∘update′)
open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open import Function using (_∘_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)
open import Utils.Fin using (reflect-lookup)
open import Definitions

import SubstitutionProperties
import Safety.Head

module Safety.Preservation {N : ℕ}{B : BTheory N}(BP : BT-Prop B) where
  private
    module SP = SubstitutionProperties BP
    module H = Safety.Head BP
  open SP
  open SP.M
  open SP.M.Subst
  open H

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
    head/typing (td/head (M⊢G R) (skip/one gr (R≢P , R≢Q)))

  mutual

    t/send/cont-head :
      ∀ {G G′ P Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {E : Exp 0}
        {Pr : Proc 0 0}
      → [] ⊢head P ◂ Q ! i < E >∙ Pr ∶ G
      → G -< P ⟶ Q # i < S > >-> G′
      → [] ⊢e E ∶ S × [] & [] ⊢p P ◂ Pr ∶ G′

    t/send/cont-head (h/send gr₀ etd td′) gr
      with step-sort-deterministic gr gr₀
    ... | refl
      rewrite step-deterministic gr gr₀ =
      etd , head/typing td′
    t/send/cont-head (h/skip std) gr =
      t/send/cont-hskip std gr

    t/send/cont-hskip :
      ∀ {G G′ P Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {E : Exp 0}
        {Pr : Proc 0 0}
      → [] & [] ⊢hskip[ prod ] P ◂ Q ! i < E >∙ Pr ∶ G
      → G -< P ⟶ Q # i < S > >-> G′
      → [] ⊢e E ∶ S × [] & [] ⊢p P ◂ Pr ∶ G′

    t/send/cont-hskip (skip/main head) gr =
      t/send/cont-head head gr
    t/send/cont-hskip (skip/step gr′ na ktd mode-gr) gr =
      ⊥-elim (∉c→¬∈c (na gr) (∈S refl))

  mutual

    t/comm/ready/head :
      ∀ {G P Q I}
        {i : Fin (suc I)}
        {E : Exp 0}
        {Pr : Proc 0 0}
        {S : Vec Sort (suc I)}
        {Br : Vec (Proc 1 0) (suc I)}
      → [] ⊢head P ◂ Q ! i < E >∙ Pr ∶ G
      → [] ⊢head Q ◂ Σ P ？[ S ]· Br ∶ G
      → ∃[ T ] ∃[ G′ ] G -< P ⟶ Q # i < T > >-> G′

    t/comm/ready/head (h/send gr _ _) _ =
      _ , _ , gr

    t/comm/ready/head (h/skip stdP) headQ =
      t/comm/ready/hskip-hskip stdP refl (skip/main headQ)

    t/comm/ready/hskip-hskip :
      ∀ {ξ m m′ G P Q I}
        {Ξ : Vec Behav ξ}
        {i : Fin (suc I)}
        {E : Exp 0}
        {Pr : Proc 0 0}
        {S : Vec Sort (suc I)}
        {Br : Vec (Proc 1 0) (suc I)}
      → [] & Ξ ⊢hskip[ m′ ] P ◂ Q ! i < E >∙ Pr ∶ G
      → m′ ≡ prod
      → [] & [] ⊢hskip[ m ] Q ◂ Σ P ？[ S ]· Br ∶ G
      → ∃[ T ] ∃[ G′ ] G -< P ⟶ Q # i < T > >-> G′

    t/comm/ready/hskip-hskip (skip/main headP) refl (skip/main headQ) =
      t/comm/ready/head headP headQ

    t/comm/ready/hskip-hskip (skip/main headP) refl (skip/step gr na ktd x) =
      t/comm/ready/head headP (h/skip (skip/step gr na ktd x))

    t/comm/ready/hskip-hskip
      (skip/step gr na ktd x)
      refl
      (skip/main (h/recv x₁ x₂)) =
      ⊥-elim (_∉c_.∉S (na x₁) refl)

    t/comm/ready/hskip-hskip
      (skip/step grα P∉G headP prodP)
      refl
      (skip/main (h/skip stdQ)) =
      t/comm/ready/hskip-hskip
        (skip/step grα P∉G headP prodP)
        refl
        stdQ

    t/comm/ready/hskip-hskip
      (skip/step grα P∉G headP prodP)
      refl
      (skip/step grQ Q∉G headQ modeQ) =
      let _ , stdQ , _ =
            hskip/unfold-cycle
              (skip/main (h/skip (skip/step grQ Q∉G headQ modeQ)))
              (headQ grα .proj₂)
          T , _ , grβ =
            t/comm/ready/hskip-hskip
              (headP grα .proj₂)
              prodP
              stdQ
          G′ , gr =
            no-new-comm/step
              grα
              (P∉G grα)
              (Q∉G grα)
              grβ
      in T , G′ , gr

  mutual

    t/recv/cont-head :
      ∀ {G G′ P Q I}
        {i : Fin (suc I)}
        {T : Sort}
        {S : Vec Sort (suc I)}
        {Br : Vec (Proc 1 0) (suc I)}
      → [] ⊢head Q ◂ Σ P ？[ S ]· Br ∶ G
      → (gr : G -< P ⟶ Q # i < T > >-> G′)
      → (T ∷ []) & [] ⊢p Q ◂ lookup Br i ∶ G′

    t/recv/cont-head (h/recv _ conts) gr =
      head/typing (conts gr)
    t/recv/cont-head (h/skip std) gr =
      t/recv/cont-hskip std gr

    t/recv/cont-hskip :
      ∀ {G G′ P Q I}
        {i : Fin (suc I)}
        {T : Sort}
        {S : Vec Sort (suc I)}
        {Br : Vec (Proc 1 0) (suc I)}
      → [] & [] ⊢hskip[ prod ] Q ◂ Σ P ？[ S ]· Br ∶ G
      → (gr : G -< P ⟶ Q # i < T > >-> G′)
      → (T ∷ []) & [] ⊢p Q ◂ lookup Br i ∶ G′

    t/recv/cont-hskip (skip/main head) gr =
      t/recv/cont-head head gr
    t/recv/cont-hskip (skip/step gr′ na ktd mode-gr) gr =
      ⊥-elim (∉c→¬∈c (na gr) (∈R refl))

  preservation/τ :
    ∀ {G M'}
    → (M : Session)
    → ⊢s M ∶ G
    → M [ nothing ]⇒ M'
    → ⊢s M' ∶ G

  preservation/τ M M⊢G (s/if/true P Ptt e⇓true)
    with t/if/inv refl (td/lookup M⊢G Ptt)
  ... | _ , ptd-then , _ =
    ⊢s-update M M⊢G ptd-then

  preservation/τ M M⊢G (s/if/false P Ptt e⇓false)
    with t/if/inv refl (td/lookup M⊢G Ptt)
  ... | _ , _ , ptd-else =
    ⊢s-update M M⊢G ptd-else

  preservation/τ M M⊢G (s/rec P Prec) =
    ⊢s-update M M⊢G (t/rec/unfold (td/lookup M⊢G Prec))


  preservation/comm :
    ∀ (M : Session)
      {G M' α}
    → ⊢s M ∶ G
    → M [ just α ]⇒ M'
    → ∃[ G' ] G -< α >-> G' × ⊢s M' ∶ G'

  preservation/comm M M⊢G (s/comm P Q Psnd e⇓v Precv)
    with t/comm/ready/head
      (td/head (td/lookup M⊢G Psnd) skip/refl)
      (td/head (td/lookup M⊢G Precv) skip/refl)
  ... | T , G′ , gr =
    let ptd = td/lookup M⊢G Psnd
        qtd = td/lookup M⊢G Precv
        etd , ptd′ =
          t/send/cont-head (td/head ptd skip/refl) gr
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
        (t/recv/cont-head (td/head qtd skip/refl) gr))

  Step : Behav → Maybe Action → Behav → Set
  Step G (just α) G′ = G -< α >-> G′
  Step G nothing G′ = G ≡ G′

  preservation :
    ∀ {G M' α}
      (M : Session)
    → ⊢s M ∶ G
    → M [ α ]⇒ M'
    → ∃[ G' ] Step G α G' × ⊢s M' ∶ G'
  preservation {α = just x} M td sr =
    preservation/comm M td sr
  preservation {G = G} {α = nothing} M td sr =
    _ , refl , preservation/τ M td sr

  preservation/τ* :
    ∀ {G M M'}
    → ⊢s M ∶ G
    → M τ⇒ M'
    → ⊢s M' ∶ G

  preservation/τ* M⊢G s/zero =
    M⊢G
  preservation/τ* M⊢G (s/more st tr) =
    preservation/τ* (preservation/τ _ M⊢G st) tr
