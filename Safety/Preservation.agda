{-# OPTIONS --guardedness #-}

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero) renaming (_≟_ to _≟f_)
open import Data.Vec
  using (Vec; []; _∷_; _[_]=_; _[_]≔_; lookup)
open import Data.Vec.Properties
  using ([]=⇒lookup; lookup∘update; lookup∘update′)
open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (_∘_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)
open import Definitions.Typing
import Definitions.Typing.Algorithmic as Alg

module Safety.Preservation {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  private
    module M = MPST wb
  open M
  open Alg wb using (_&_⊢a_∶_; _&_⊢blocked_∶_; a/skip; a/if; a/end;
                     blocked/send; blocked/recv; blocked/var; blocked/rec;
                     alg/typing)
  open M.Subst
  open import Definitions.Typing.Substitution wb
  open import Definitions.Typing.Properties wb
  open import Definitions.Typing.Norm wb
    using (norm; a/if/inv; a/rec/guarded; bskip/unfold-top)

  td/lookup :
    ∀ {M G P Pr}
    → ⊢s M ∶ G
    → M [ P ]= Pr
    → [] & [] ⊢p P ◂ Pr ∶ G
  td/lookup {P = P} ts luP with ts P
  ... | ptd rewrite []=⇒lookup luP = ptd

  -- THE BOUNDARY.  `⊢s` is stated over `⊢p`, so this is where `⊢p` is
  -- allowed to appear — and it is immediately left behind.  Everything
  -- downstream in `Safety/*` consumes `alg/lookup`, never `td/lookup`.
  alg/lookup :
    ∀ {M G P Pr}
    → ⊢s M ∶ G
    → M [ P ]= Pr
    → [] & [] ⊢a P ◂ Pr ∶ G
  alg/lookup ts luP = norm (td/lookup ts luP) skip/refl

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
    -- R is uninvolved, so its typing rides the step across.  `norm` does
    -- in one call what `head/typing ∘ td/head` did in two.
    alg/typing (norm (M⊢G R) (skip/one gr (R≢P , R≢Q)))

  mutual

    -- Note the continuation comes back as `⊢a` with no conversion: under
    -- `⊢head` this clause had to call `head/typing td′`, because `h/send`
    -- stores a `⊢head` and the caller wanted `⊢p`.  `blocked/send` stores
    -- an `⊢a` already.
    send/cont :
      ∀ {G G′ P Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {E : Exp 0}
        {Pr : Proc 0 0}
      → [] & [] ⊢a P ◂ Q ! i < E >∙ Pr ∶ G
      → G -< P ⟶ Q # i < S > >-> G′
      → [] ⊢e E ∶ S × [] & [] ⊢a P ◂ Pr ∶ G′

    send/cont (a/skip std) gr =
      send/cont-skip std gr

    send/cont-skip :
      ∀ {G G′ P Q I}
        {i : Fin (suc I)}
        {S : Sort}
        {E : Exp 0}
        {Pr : Proc 0 0}
      → ([] & [] ⊢blocked_∶_) & [] ⊢skip P ◂ Q ! i < E >∙ Pr ∶ G
      → G -< P ⟶ Q # i < S > >-> G′
      → [] ⊢e E ∶ S × [] & [] ⊢a P ◂ Pr ∶ G′

    send/cont-skip (skip/main (blocked/send gr₀ etd td′)) gr
      with step-sort-deterministic gr gr₀
    ... | refl
      rewrite step-deterministic gr gr₀ =
      etd , td′
    send/cont-skip (skip/step gr′ na ktd) gr =
      ⊥-elim (∉c→¬∈c (na gr) (∈S refl))

  -- The two-sided readiness argument.
  --
  -- Under `⊢head` this was FIVE functions in two mutual blocks
  -- (`comm/ready`, `-skip`, `-or-∈T`, `-from-∈T`, `-from-∈T-skip`), and
  -- the reason was `h/skip`: a `skip/main` leaf could be *another*
  -- `h/skip`, so each side needed a leaf/tree pair, and the leaf case had
  -- to re-enter the tree case with a fresh, unrelated `P ∈T G` witness —
  -- which is what forced `-from-∈T` to be kept separate from `comm/ready`
  -- in the first place.
  --
  -- `⊢a` removes the nesting outright: a `skip/main` leaf is a
  -- `blocked/send` or `blocked/recv`, never another tree.  So there are
  -- three functions, none of them mutual, and the leaf cases just return.

  -- The fold path: a cycle WAS hit on P's side, so walk the `P ∈T G`
  -- witness instead, decreasing on it and folding both trees through
  -- `bskip/unfold-top` in lockstep.  `Ξ = []` throughout, so `skip/cycle`
  -- is absurd on P's side.
  comm/ready-from-∈T :
    ∀ {G P Q I}
      {i : Fin (suc I)}
      {E : Exp 0}
      {Pr : Proc 0 0}
      {Br : Vec (Proc 1 0) (suc I)}
    → ([] & [] ⊢blocked_∶_) & [] ⊢skip P ◂ Q ! i < E >∙ Pr ∶ G
    → P ∈T G
    → ([] & [] ⊢blocked_∶_) & [] ⊢skip Q ◂ Σ P ？· Br ∶ G
    → ∃[ T ] ∃[ G′ ] G -< P ⟶ Q # i < T > >-> G′

  comm/ready-from-∈T (skip/main (blocked/send gr _ _)) _ _ =
    _ , _ , gr

  comm/ready-from-∈T
    (skip/step gr na ktdP) (_ , H , tr/step gr' tr , here px) _ =
    ⊥-elim (∉c→¬∈c (na gr') px)

  comm/ready-from-∈T
    (skip/step gr na ktdP) _ (skip/main (blocked/recv grQ _)) =
    ⊥-elim (∉c→¬∈c (na grQ) (∈S refl))

  comm/ready-from-∈T
    stdP@(skip/step gr na ktdP)
    (_ , H , tr/step gr' tr , there mem)
    stdQ@(skip/step grQ Q∉G ktdQ) =
    let stdP′ = bskip/unfold-top stdP (ktdP gr')
        stdQ′ = bskip/unfold-top stdQ (ktdQ gr')
        T , _ , grβ =
          comm/ready-from-∈T stdP′ (_ , H , tr , mem) stdQ′
        G′ , gr″ =
          no-new-comm/step gr' (na gr') (Q∉G gr') grβ
    in T , G′ , gr″

  comm/ready-from-∈T (skip/cycle {X = ()} _ _) _ _

  -- The fast path: drive P's side structurally (`ktdP gr` is a genuine
  -- subterm), carrying Q's tree along and advancing it by the SAME edge at
  -- every step.  `no-new-comm/step` pushes a communication found one level
  -- down back to the current state.
  comm/ready-or-∈T :
    ∀ {ξ G P Q I}
      {Ξ : Vec Behav ξ}
      {i : Fin (suc I)}
      {E : Exp 0}
      {Pr : Proc 0 0}
      {Br : Vec (Proc 1 0) (suc I)}
    → ([] & [] ⊢blocked_∶_) & Ξ ⊢skip P ◂ Q ! i < E >∙ Pr ∶ G
    → ([] & [] ⊢blocked_∶_) & [] ⊢skip Q ◂ Σ P ？· Br ∶ G
    → (∃[ T ] ∃[ G′ ] G -< P ⟶ Q # i < T > >-> G′) ⊎ P ∈T G

  -- Under `⊢head` this clause had to call back into `comm/ready`; the leaf
  -- now IS the edge.
  comm/ready-or-∈T (skip/main (blocked/send gr _ _)) _ =
    inj₁ (_ , _ , gr)

  comm/ready-or-∈T (skip/step gr na ktdP) (skip/main (blocked/recv grQ _)) =
    ⊥-elim (∉c→¬∈c (na grQ) (∈S refl))

  comm/ready-or-∈T (skip/cycle _ inT) _ =
    inj₂ inT

  comm/ready-or-∈T (skip/step gr na ktdP) stdQ@(skip/step grQ Q∉G ktdQ)
    with comm/ready-or-∈T (ktdP gr) (bskip/unfold-top stdQ (ktdQ gr))
  ... | inj₁ (T , _ , grβ) =
    let G′ , g = no-new-comm/step gr (na gr) (Q∉G gr) grβ
    in inj₁ (T , G′ , g)
  ... | inj₂ pInT =
    inj₂ (in/later gr pInT)

  comm/ready :
    ∀ {G P Q I}
      {i : Fin (suc I)}
      {E : Exp 0}
      {Pr : Proc 0 0}
      {Br : Vec (Proc 1 0) (suc I)}
    → [] & [] ⊢a P ◂ Q ! i < E >∙ Pr ∶ G
    → [] & [] ⊢a Q ◂ Σ P ？· Br ∶ G
    → ∃[ T ] ∃[ G′ ] G -< P ⟶ Q # i < T > >-> G′
  comm/ready (a/skip stdP) (a/skip stdQ)
    with comm/ready-or-∈T stdP stdQ
  ... | inj₁ res  = res
  ... | inj₂ pInT = comm/ready-from-∈T stdP pInT stdQ

  -- Same collapse as `send/cont`: one function instead of a mutual pair,
  -- and `blocked/recv`'s `conts` already yields `⊢a`.
  recv/cont-skip :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {T : Sort}
      {Br : Vec (Proc 1 0) (suc I)}
    → ([] & [] ⊢blocked_∶_) & [] ⊢skip Q ◂ Σ P ？· Br ∶ G
    → (gr : G -< P ⟶ Q # i < T > >-> G′)
    → (T ∷ []) & [] ⊢a Q ◂ lookup Br i ∶ G′
  recv/cont-skip (skip/main (blocked/recv _ conts)) gr = conts gr
  recv/cont-skip (skip/step gr′ na ktd) gr =
    ⊥-elim (∉c→¬∈c (na gr) (∈R refl))

  recv/cont :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {T : Sort}
      {Br : Vec (Proc 1 0) (suc I)}
    → [] & [] ⊢a Q ◂ Σ P ？· Br ∶ G
    → (gr : G -< P ⟶ Q # i < T > >-> G′)
    → (T ∷ []) & [] ⊢a Q ◂ lookup Br i ∶ G′
  recv/cont (a/skip std) gr = recv/cont-skip std gr

  preservation/τ :
    ∀ {G M'}
    → (M : Session)
    → ⊢s M ∶ G
    → M [ nothing ]⇒ M'
    → ⊢s M' ∶ G

  -- `alg/lookup` in, `alg/typing` out: the work in between is `⊢a`, and
  -- `⊢p` reappears only because `⊢s-update` has to rebuild a session
  -- derivation, which is stated over `⊢s`.
  preservation/τ M M⊢G (s/if/true P Ptt e⇓true)
    with a/if/inv refl (alg/lookup M⊢G Ptt)
  ... | _ , atd-then , _ =
    ⊢s-update M M⊢G (alg/typing atd-then)

  preservation/τ M M⊢G (s/if/false P Ptt e⇓false)
    with a/if/inv refl (alg/lookup M⊢G Ptt)
  ... | _ , _ , atd-else =
    ⊢s-update M M⊢G (alg/typing atd-else)

  preservation/τ M M⊢G (s/rec P Prec) =
    ⊢s-update M M⊢G
      (alg/typing (a/rec/unfold (alg/lookup M⊢G Prec)))

  preservation/comm :
    ∀ (M : Session)
      {G M' α}
    → ⊢s M ∶ G
    → M [ just α ]⇒ M'
    → ∃[ G' ] G -< α >-> G' × ⊢s M' ∶ G'

  preservation/comm M M⊢G (s/comm P Q Psnd e⇓v Precv)
    with comm/ready
      (alg/lookup M⊢G Psnd)
      (alg/lookup M⊢G Precv)
  ... | T , G′ , gr =
    let etd , atd′ = send/cont (alg/lookup M⊢G Psnd) gr
        vtd        = exp-pres etd e⇓v
    in
    G′ ,
    subst
      (λ U → _ -< _ ⟶ _ # _ < U > >-> _)
      (sort/value-typed vtd)
      gr ,
    -- `alg/typing` only at the very end, where `⊢s-comm-update` needs to
    -- rebuild the session derivation.
    ⊢s-comm-update M gr M⊢G (alg/typing atd′)
      (alg/typing
        (alg/subst-expr
          (te/val vtd)
          (recv/cont (alg/lookup M⊢G Precv) gr)))

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
