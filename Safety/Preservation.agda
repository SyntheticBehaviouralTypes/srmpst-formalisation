{-# OPTIONS --guardedness #-}

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero) renaming (_≟_ to _≟f_)
open import Data.Vec
  using (Vec; []; _∷_; _[_]=_; _[_]≔_; lookup)
open import Data.Vec.Properties
  using ([]=⇒lookup; lookup∘update; lookup∘update′)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (_∘_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε)
open import Data.Empty using (⊥)
open import Definitions.Typing

module Safety.Preservation {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  private
    module M = MPST wb
  open M
  open M.Subst
  open import Definitions.Typing.Substitution wb
  open import Definitions.Typing.Alg wb
    using ( Behavs; Closed; WaitV; wv/leaf; wv/cycle; wv/step
          ; waitLeaf; waitV/unfold-top
          ; _⊢at_∶_; at/if-inv; at/send-inv; at/recv-inv )
  open import Definitions.Typing.AlgNorm wb using (td⇒at)
  open import Definitions.Typing.AlgDeclarative wb using (at⇒typing)
  open import Definitions.Typing.Properties wb

  td/lookup :
    ∀ {M G P Pr}
    → ⊢s M ∶ G
    → M [ P ]= Pr
    → [] & [] ⊢p P ◂ Pr ∶ G
  td/lookup {P = P} ts luP with ts P
  ... | ptd rewrite []=⇒lookup luP = ptd

  -- THE BOUNDARY.  `⊢s` is stated over `⊢p`, so coming IN is `td⇒at`
  -- (`AlgNorm.agda`) and going OUT is `at⇒typing` (`AlgDeclarative.agda`).
  -- Everything downstream consumes `at/lookup`.
  at/lookup :
    ∀ {M G P Pr}
    → ⊢s M ∶ G
    → M [ P ]= Pr
    → [] ⊢at P ◂ Pr ∶ ([] , G)
  at/lookup ts luP = td⇒at (td/lookup ts luP)

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
    -- R is uninvolved, so its typing rides the step across: `t/unskip`.
    t/unskip (skip/one gr (R≢P , R≢Q)) (M⊢G R)

  -- `P` is the sender, so `P` is ACTIVE at `G` and `waitLeaf` says the `Wait`
  -- is a leaf: the send is enabled at `G` itself, with the rule's sort.
  send/cont :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {E : Exp 0}
      {Pr : Proc 0 0}
    → [] ⊢at P ◂ Q ! i < E >∙ Pr ∶ ([] , G)
    → G -< P ⟶ Q # i < S > >-> G′
    → [] ⊢e E ∶ S × [] ⊢at P ◂ Pr ∶ ([] , G′)

  send/cont td gr
    with at/send-inv td
  ... | _ , etd , w , k
    with waitLeaf gr (∈S refl) w
  ...   | _ , gr₀
    with step-sort-deterministic gr gr₀
  ...     | refl =
    etd , k ε gr

  recv/cont :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {T : Sort}
      {Br : Vec (Proc 1 0) (suc I)}
    → [] ⊢at Q ◂ Σ P ？· Br ∶ ([] , G)
    → G -< P ⟶ Q # i < T > >-> G′
    → (T ∷ []) ⊢at Q ◂ lookup Br i ∶ ([] , G′)

  recv/cont td gr = proj₂ (at/recv-inv td) ε gr

  -- ══════════════════════════════════════════════════════════════════
  --  The two-sided readiness argument
  -- ══════════════════════════════════════════════════════════════════
  --
  -- Stated over ARBITRARY leaf families, so the send/recv specifics enter
  -- only as the two projections `fP`/`fQ` supplied by `comm/ready`.

  -- The fast path: drive P's side structurally, carrying Q's along and
  -- advancing it by the SAME edge at every step.  `no-new-comm/step` pushes a
  -- communication found one level down back to the current state.
  comm/ready-or-∈T :
    ∀ {G P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {𝒮P 𝒮Q V : Behavs}
    → (∀ {u} → 𝒮P u → ∃[ u′ ] (u -< P ⟶ Q # i < S > >-> u′))
    → (∀ {u} → 𝒮Q u → ∃[ α ] ∃[ t ] (u -< α >-> t) × P ∈α α)
    → Closed 𝒮Q
    → WaitV P 𝒮P V G
    → WaitV Q 𝒮Q (λ _ → ⊥) G
    → (∃[ T ] ∃[ G′ ] G -< P ⟶ Q # i < T > >-> G′) ⊎ P ∈T G

  comm/ready-or-∈T fP fQ cQ (wv/leaf x) _ =
    inj₁ (_ , proj₁ (fP x) , proj₂ (fP x))

  comm/ready-or-∈T fP fQ cQ (wv/cycle _ inT) _ =
    inj₂ inT

  comm/ready-or-∈T fP fQ cQ (wv/step na _ _) (wv/leaf y)
    with fQ y
  ... | _ , _ , grQ , px =
    ⊥-elim (∉c→¬∈c (na grQ) px)

  comm/ready-or-∈T fP fQ cQ (wv/step _ _ _) (wv/cycle (_ , () , _) _)

  comm/ready-or-∈T fP fQ cQ (wv/step na gr k) topQ@(wv/step naQ _ kQ)
    with comm/ready-or-∈T fP fQ cQ (k gr)
           (waitV/unfold-top cQ topQ (λ w → w) (kQ gr))
  ... | inj₁ (T , _ , grβ) =
    let G′ , g = no-new-comm/step gr (na gr) (naQ gr) grβ
    in inj₁ (T , G′ , g)
  ... | inj₂ pInT =
    inj₂ (in/later gr pInT)

  -- The fold path: a cycle WAS hit on P's side, so walk the `P ∈T G` witness
  -- instead, decreasing on it and re-rooting both trees in lockstep.
  comm/ready-from-∈T :
    ∀ {G P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {𝒮P 𝒮Q : Behavs}
    → (∀ {u} → 𝒮P u → ∃[ u′ ] (u -< P ⟶ Q # i < S > >-> u′))
    → (∀ {u} → 𝒮Q u → ∃[ α ] ∃[ t ] (u -< α >-> t) × P ∈α α)
    → Closed 𝒮P
    → Closed 𝒮Q
    → WaitV P 𝒮P (λ _ → ⊥) G
    → P ∈T G
    → WaitV Q 𝒮Q (λ _ → ⊥) G
    → ∃[ T ] ∃[ G′ ] G -< P ⟶ Q # i < T > >-> G′

  comm/ready-from-∈T fP fQ cP cQ (wv/leaf x) _ _ =
    _ , proj₁ (fP x) , proj₂ (fP x)

  comm/ready-from-∈T fP fQ cP cQ (wv/cycle (_ , () , _) _) _ _

  comm/ready-from-∈T fP fQ cP cQ
    (wv/step na _ _) (_ , _ , tr/step gr′ _ , here px) _ =
    ⊥-elim (∉c→¬∈c (na gr′) px)

  comm/ready-from-∈T fP fQ cP cQ
    (wv/step na _ _) _ (wv/leaf y)
    with fQ y
  ... | _ , _ , grQ , px =
    ⊥-elim (∉c→¬∈c (na grQ) px)

  comm/ready-from-∈T fP fQ cP cQ
    (wv/step _ _ _) _ (wv/cycle (_ , () , _) _)

  comm/ready-from-∈T fP fQ cP cQ
    topP@(wv/step na _ kP)
    (_ , H , tr/step gr′ tr , there mem)
    topQ@(wv/step naQ _ kQ) =
    let T , _ , grβ =
          comm/ready-from-∈T fP fQ cP cQ
            (waitV/unfold-top cP topP (λ w → w) (kP gr′))
            (_ , H , tr , mem)
            (waitV/unfold-top cQ topQ (λ w → w) (kQ gr′))
        G′ , gr″ = no-new-comm/step gr′ (na gr′) (naQ gr′) grβ
    in T , G′ , gr″

  comm/ready :
    ∀ {G P Q I}
      {i : Fin (suc I)}
      {E : Exp 0}
      {Pr : Proc 0 0}
      {Br : Vec (Proc 1 0) (suc I)}
    → [] ⊢at P ◂ Q ! i < E >∙ Pr ∶ ([] , G)
    → [] ⊢at Q ◂ Σ P ？· Br ∶ ([] , G)
    → ∃[ T ] ∃[ G′ ] G -< P ⟶ Q # i < T > >-> G′

  -- The send/recv specifics enter here and nowhere else: `fP`/`fQ` project the
  -- edge out of each rule's leaf family, and `cP`/`cQ` close them under `~`.
  comm/ready tdP tdQ
    with at/send-inv tdP | proj₁ (at/recv-inv tdQ)
  ... | _ , _ , wP , _ | wQ =
    go (comm/ready-or-∈T fP fQ cQ wP wQ)
    where
      fP : ∀ {u} → ∃[ u′ ] (u -< _ >-> u′) → ∃[ u′ ] (u -< _ >-> u′)
      fP x = x

      fQ : ∀ {u} → (Σ[ j ∈ _ ] ∃[ U ] ∃[ t ] (u -< _ ⟶ _ # j < U > >-> t))
                 → ∃[ α ] ∃[ t ] (u -< α >-> t) × _ ∈α α
      fQ (_ , _ , _ , gr) = _ , _ , gr , ∈S refl

      cP : Closed (λ u → ∃[ u′ ] (u -< _ >-> u′))
      cP G~H (_ , gr) = _ , ~L→ G~H gr

      cQ : Closed (λ u → Σ[ j ∈ _ ] ∃[ U ] ∃[ t ] (u -< _ ⟶ _ # j < U > >-> t))
      cQ G~H (j , U , _ , gr) = j , U , _ , ~L→ G~H gr

      go :
        ((∃[ T ] ∃[ G′ ] _ -< _ ⟶ _ # _ < T > >-> G′) ⊎ _ ∈T _)
        → ∃[ T ] ∃[ G′ ] _ -< _ ⟶ _ # _ < T > >-> G′
      go (inj₁ res)  = res
      go (inj₂ pInT) = comm/ready-from-∈T fP fQ cP cQ wP pInT wQ

  preservation/τ :
    ∀ {G M'}
    → (M : Session)
    → ⊢s M ∶ G
    → M [ nothing ]⇒ M'
    → ⊢s M' ∶ G

  preservation/τ M M⊢G (s/if/true P Ptt e⇓true)
    with at/if-inv (at/lookup M⊢G Ptt)
  ... | _ , std-then , _ =
    ⊢s-update M M⊢G (at⇒typing std-then)

  preservation/τ M M⊢G (s/if/false P Ptt e⇓false)
    with at/if-inv (at/lookup M⊢G Ptt)
  ... | _ , _ , std-else =
    ⊢s-update M M⊢G (at⇒typing std-else)

  preservation/τ M M⊢G (s/rec P Prec) =
    ⊢s-update M M⊢G
      (at⇒typing (at/rec/unfold (at/lookup M⊢G Prec)))

  preservation/comm :
    ∀ (M : Session)
      {G M' α}
    → ⊢s M ∶ G
    → M [ just α ]⇒ M'
    → ∃[ G' ] G -< α >-> G' × ⊢s M' ∶ G'

  preservation/comm M M⊢G (s/comm P Q Psnd e⇓v Precv)
    with comm/ready
      (at/lookup M⊢G Psnd)
      (at/lookup M⊢G Precv)
  ... | T , G′ , gr =
    let etd , std′ = send/cont (at/lookup M⊢G Psnd) gr
        vtd        = exp-pres etd e⇓v
    in
    G′ ,
    subst
      (λ U → _ -< _ ⟶ _ # _ < U > >-> _)
      (sort/value-typed vtd)
      gr ,
    ⊢s-comm-update M gr M⊢G (at⇒typing std′)
      (at⇒typing
        (at/subst-expr
          (te/val vtd)
          (recv/cont (at/lookup M⊢G Precv) gr)))

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
