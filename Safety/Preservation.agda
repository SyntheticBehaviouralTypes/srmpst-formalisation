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
open import Data.Empty using (⊥)
open import Definitions.Typing

module Safety.Preservation {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  private
    module M = MPST wb
  open M
  open M.Subst
  open import Definitions.Typing.Substitution wb
  open import Definitions.Typing.Alg wb
    using ( _&_⊢a_∶_; a/send; a/recv; a/if; a/end; a/var; a/rec
          ; Pred; Closed; WaitV; wv/leaf; wv/cycle; wv/step
          ; waitLeaf; waitV/unfold-top
          ; _&_⊨_∶_; ⊨/if-inv; ⊨/rec-guarded; ⊨/end-inv )
  open import Definitions.Typing.AlgNorm wb using (td⇒⊨)
  open import Definitions.Typing.AlgDeclarative wb using (⊨⇒typing)
  open import Definitions.Typing.Properties wb

  td/lookup :
    ∀ {M G P Pr}
    → ⊢s M ∶ G
    → M [ P ]= Pr
    → [] & [] ⊢p P ◂ Pr ∶ G
  td/lookup {P = P} ts luP with ts P
  ... | ptd rewrite []=⇒lookup luP = ptd

  -- THE BOUNDARY.  `⊢s` is stated over `⊢p`, so coming IN needs
  -- `⊢p → ⊢a` — `td⇒⊨` (`AlgNorm.agda`).  Going OUT is `⊨⇒typing`
  -- (`AlgDeclarative.agda`).  Both are direct; the old, deleted two-tier
  -- `⊢a` is gone from the development and neither direction passes through
  -- anything else.  Everything downstream consumes `⊨/lookup`.
  ⊨/lookup :
    ∀ {M G P Pr}
    → ⊢s M ∶ G
    → M [ P ]= Pr
    → [] & [] ⊨ P ◂ Pr ∶ G
  ⊨/lookup ts luP = td⇒⊨ (td/lookup ts luP)

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
    -- R is uninvolved, so its typing rides the step across — and that is
    -- exactly `t/unskip`.  This used to detour `⊢p → ⊢a → ⊨ → ⊢p` because
    -- `norm` was the only thing that could absorb a trace; the declarative
    -- rule could do it all along.
    t/unskip (skip/one gr (R≢P , R≢Q)) (M⊢G R)

  -- `P` is the sender, so `P` is ACTIVE at `G` and `waitLeaf` says the `Wait`
  -- can only be a leaf.  That is the whole of what `send/cont-skip` was.
  send/cont :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {E : Exp 0}
      {Pr : Proc 0 0}
    → [] & [] ⊨ P ◂ Q ! i < E >∙ Pr ∶ G
    → G -< P ⟶ Q # i < S > >-> G′
    → [] ⊢e E ∶ S × [] & [] ⊨ P ◂ Pr ∶ G′

  send/cont (_ , a/send etd td _ sub , mem) gr
    with waitLeaf gr (∈S refl) (sub mem)
  ... | _ , gr₀ , 𝒯u′
    with step-sort-deterministic gr gr₀
  ...   | refl
    rewrite step-deterministic gr gr₀ =
    etd , (_ , td , 𝒯u′)

  -- Same, on the receiving side; `conts` turns the leaf's obligation into the
  -- branch's own set derivation.
  recv/cont :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {T : Sort}
      {Br : Vec (Proc 1 0) (suc I)}
    → [] & [] ⊨ Q ◂ Σ P ？· Br ∶ G
    → (gr : G -< P ⟶ Q # i < T > >-> G′)
    → (T ∷ []) & [] ⊨ Q ◂ lookup Br i ∶ G′

  recv/cont (_ , a/recv conts _ sub , mem) gr
    with waitLeaf gr (∈R refl) (sub mem)
  ... | _ , k =
    _ , conts (k gr) , k gr

  -- ══════════════════════════════════════════════════════════════════
  --  The two-sided readiness argument
  -- ══════════════════════════════════════════════════════════════════
  --
  -- Under `⊢head` this was FIVE functions in two mutual blocks; under the
  -- old, deleted two-tier `⊢a` three.  Over these rules it is still three,
  -- but they are stated over ARBITRARY leaf families rather than over the
  -- judgment, so the send/recv specifics enter only as the two projections
  -- `fP`/`fQ` supplied by `comm/ready` at the bottom.
  --
  -- The re-rooting that `bskip/unfold-top` did is `waitV/unfold-top`, and the
  -- `Closed` it needs is the `tclosed` premise of `a/send`/`a/recv`.

  -- The fast path: drive P's side structurally, carrying Q's along and
  -- advancing it by the SAME edge at every step.  `no-new-comm/step` pushes a
  -- communication found one level down back to the current state.
  comm/ready-or-∈T :
    ∀ {G P Q I}
      {i : Fin (suc I)}
      {S : Sort}
      {𝒮P 𝒮Q V : Pred}
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
      {𝒮P 𝒮Q : Pred}
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
    → [] & [] ⊨ P ◂ Q ! i < E >∙ Pr ∶ G
    → [] & [] ⊨ Q ◂ Σ P ？· Br ∶ G
    → ∃[ T ] ∃[ G′ ] G -< P ⟶ Q # i < T > >-> G′

  -- The send/recv specifics enter here and nowhere else: `fP`/`fQ` project the
  -- edge out of each rule's leaf family, and `cP`/`cQ` are the two `tclosed`
  -- premises, lifted from the continuation sets to the leaf families.
  comm/ready
    {P = P} {Q = Q} {i = i}
    (_ , a/send {S = S} {𝒯 = 𝒯P} _ _ tcP subP , memP)
    (_ , a/recv {𝒯 = 𝒯Q} _ tcQ subQ , memQ) =
    go (comm/ready-or-∈T fP fQ cQ (subP memP) (subQ memQ))
    where
      fP :
        ∀ {u} → (∃[ u′ ] (u -< P ⟶ Q # i < S > >-> u′) × 𝒯P u′)
              → ∃[ u′ ] (u -< P ⟶ Q # i < S > >-> u′)
      fP (u′ , gr , _) = u′ , gr

      fQ :
        ∀ {u}
        → ((Σ[ j ∈ _ ] ∃[ U ] ∃[ t ] (u -< P ⟶ Q # j < U > >-> t))
           × (∀ {j U t} → u -< P ⟶ Q # j < U > >-> t → 𝒯Q j U t))
        → ∃[ α ] ∃[ t ] (u -< α >-> t) × P ∈α α
      fQ ((_ , _ , _ , gr) , _) = _ , _ , gr , ∈S refl

      cP : Closed (λ u → ∃[ u′ ] (u -< P ⟶ Q # i < S > >-> u′) × 𝒯P u′)
      cP G~H (_ , gr , t) = _ , ~L→ G~H gr , tcP (~L→~ G~H gr) t

      cQ :
        Closed (λ u → (Σ[ j ∈ _ ] ∃[ U ] ∃[ t ] (u -< P ⟶ Q # j < U > >-> t))
                    × (∀ {j U t} → u -< P ⟶ Q # j < U > >-> t → 𝒯Q j U t))
      cQ G~H ((j , U , _ , gr) , k) =
        (j , U , _ , ~L→ G~H gr) ,
        λ gr′ → tcQ (~R→~ G~H gr′) (k (~R→ G~H gr′))

      go :
        ((∃[ T ] ∃[ G′ ] _ -< P ⟶ Q # i < T > >-> G′) ⊎ P ∈T _)
        → ∃[ T ] ∃[ G′ ] _ -< P ⟶ Q # i < T > >-> G′
      go (inj₁ res)  = res
      go (inj₂ pInT) =
        comm/ready-from-∈T fP fQ cP cQ (subP memP) pInT (subQ memQ)

  preservation/τ :
    ∀ {G M'}
    → (M : Session)
    → ⊢s M ∶ G
    → M [ nothing ]⇒ M'
    → ⊢s M' ∶ G

  -- `⊨/lookup` in, `⊨⇒typing` out: the work in between is the set judgment,
  -- and `⊢p` reappears only because `⊢s-update` has to rebuild a session
  -- derivation, which is stated over `⊢s`.
  preservation/τ M M⊢G (s/if/true P Ptt e⇓true)
    with ⊨/if-inv (⊨/lookup M⊢G Ptt)
  ... | _ , std-then , _ =
    ⊢s-update M M⊢G (⊨⇒typing std-then)

  preservation/τ M M⊢G (s/if/false P Ptt e⇓false)
    with ⊨/if-inv (⊨/lookup M⊢G Ptt)
  ... | _ , _ , std-else =
    ⊢s-update M M⊢G (⊨⇒typing std-else)

  preservation/τ M M⊢G (s/rec P Prec) =
    ⊢s-update M M⊢G
      (⊨⇒typing (⊨/rec/unfold (⊨/lookup M⊢G Prec)))

  preservation/comm :
    ∀ (M : Session)
      {G M' α}
    → ⊢s M ∶ G
    → M [ just α ]⇒ M'
    → ∃[ G' ] G -< α >-> G' × ⊢s M' ∶ G'

  preservation/comm M M⊢G (s/comm P Q Psnd e⇓v Precv)
    with comm/ready
      (⊨/lookup M⊢G Psnd)
      (⊨/lookup M⊢G Precv)
  ... | T , G′ , gr =
    let etd , std′ = send/cont (⊨/lookup M⊢G Psnd) gr
        vtd        = exp-pres etd e⇓v
    in
    G′ ,
    subst
      (λ U → _ -< _ ⟶ _ # _ < U > >-> _)
      (sort/value-typed vtd)
      gr ,
    -- `⊨⇒typing` only at the very end, where `⊢s-comm-update` needs to rebuild
    -- the session derivation.
    ⊢s-comm-update M gr M⊢G (⊨⇒typing std′)
      (⊨⇒typing
        (⊨/subst-expr
          (te/val vtd)
          (recv/cont (⊨/lookup M⊢G Precv) gr)))

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
