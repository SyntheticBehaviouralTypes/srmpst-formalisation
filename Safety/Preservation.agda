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
open import Data.Fin.Subset using (_∈_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε)
open import Data.Empty using (⊥)
open import Definitions.Typing

module Safety.Preservation
  {N : ℕ}{B : BTheory N}(wb : WellBehaved B)(sync : Synchronous B) where
  private
    module M = MPST wb
  open M
  open M.Subst
  open Synchronous sync
  open import Definitions.Typing.Substitution wb
  open import Definitions.Typing.Alg wb
    using ( Behavs; Closed; WaitV; wv/leaf; wv/cycle; wv/step
          ; waitV/unfold-top; Wait; Dom; Offers
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
  at/lookup ts luP = td⇒at sync (td/lookup ts luP)

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
      {G G′ P Qs c Pr}
      {F : ∀ R → R ∈ Qs → Proc 0 0}
    → (gr : G -< P ⟶ Qs # c >-> G′)
    → ⊢s M ∶ G
    → [] & [] ⊢p P ◂ Pr ∶ G′
    → (∀ R (m : R ∈ Qs) → [] & [] ⊢p R ◂ F R m ∶ G′)
    → ⊢s M [ P ↦ Pr ∣ Qs ↦ F ] ∶ G′

  ⊢s-comm-update M {P = P} {Qs} {c} {Pr} {F} gr M⊢G Ptd Rtd R
    with R ≟f P
  ... | yes refl
    rewrite upd-sender {M} {R} {Pr} {Qs} {F} =
    Ptd
  ... | no R≢P
    with R ∈? Qs
  ...   | yes m
    rewrite upd-recv {M} {P} {Pr} {Qs} {F} {R} R≢P m =
    Rtd R m
  ...   | no R∉
    rewrite upd-other {M} {P} {Pr} {Qs} {F} {R} R≢P R∉ =
    -- R is uninvolved, so its typing rides the step across: `t/unskip`.
    t/unskip (skip/one {P = R} gr (ev-other {P} {Qs} {c} {R} R≢P R∉))
      (M⊢G R)

  recv/cont :
    ∀ {G G′ P Q I}
      {i : Fin (suc I)}
      {T : Sort}
      {Br : Vec (Proc 1 0) (suc I)}
    → [] ⊢at Q ◂ Σ P ？· Br ∶ ([] , G)
    → G -<[ Q ↦ (？ P) # i < T > ]>-> G′
    → (T ∷ []) ⊢at Q ◂ lookup Br i ∶ ([] , G′)

  recv/cont td gr = proj₂ (at/recv-inv td) ε gr

  -- ══════════════════════════════════════════════════════════════════
  --  The multi-sided readiness argument
  -- ══════════════════════════════════════════════════════════════════
  --
  -- Stated over ARBITRARY leaf families, so the send/recv specifics enter
  -- only as the projections `fP`/`fR` supplied by `comm/ready`.  One sender
  -- tree `P`, one receiver tree per `R ∈ Qs`.

  -- While `P` is idle, each receiver tree is a `wv/step` too: a leaf would
  -- be a step in which `P` is active.
  receiver-step :
    ∀ {G P R}{L : Behavs}
    → P not-active-in G
    → (∀ {u} → L u → ∃[ α ] ∃[ t ] (u -< α >-> t) × P ∈α α)
    → WaitV R L (λ _ → ⊥) G
    → R not-active-in G
    × (∀ {β u} → G -< β >-> u → WaitV R L (λ v → ⊥ ⊎ (G ~ v)) u)

  receiver-step {P = P} na f (wv/leaf x)
    with f x
  ... | α , _ , grR , px =
    ⊥-elim (∉α→¬∈α {P} {α} (na grR) px)

  receiver-step na f (wv/cycle (_ , () , _) _)

  receiver-step na f (wv/step naR _ kR) =
    naR , kR

  -- A multicast by `P` found after a step `β` in which `P` and every
  -- receiver are idle involves nobody `β` involves.
  multicast-idle :
    ∀ {G t G″ β γ P Qs c}
    → P not-active-in G
    → G -< β >-> t
    → (∀ R → R ∈ Qs → R not-active-in G)
    → t -< γ >-> G″
    → ev γ P ≡ just ((! Qs) # c)
    → ∀ X → X ∈α γ → X ∉α β

  multicast-idle {P = P} {Qs} {c} na gr naR g eq X (_ , eqX)
    with send-action g eq
  ... | _ , refl
    with ev-inv {P} {Qs} {c} {X} eqX
  ...   | inj₁ (refl , _)     = na gr
  ...   | inj₂ (_ , m , _)    = naR X m gr

  -- The fast path: drive P's side structurally, carrying the receivers'
  -- along and advancing them by the SAME edge at every step.
  -- `no-new-comm/step` pushes a communication found one level down back to
  -- the current state.
  comm/ready-or-∈T :
    ∀ {G P Qs c}
      {𝒮P V : Behavs}
      {𝒮R : Part → Behavs}
    → (∀ {u} → 𝒮P u → ∃[ u′ ] u -<[ P ↦ (! Qs) # c ]>-> u′)
    → (∀ {R u} → 𝒮R R u → ∃[ α ] ∃[ t ] (u -< α >-> t) × P ∈α α)
    → (∀ {R} → Closed (𝒮R R))
    → WaitV P 𝒮P V G
    → (∀ R → R ∈ Qs → WaitV R (𝒮R R) (λ _ → ⊥) G)
    → (∃[ G′ ] G -<[ P ↦ (! Qs) # c ]>-> G′) ⊎ P ∈T G

  comm/ready-or-∈T fP fR cR (wv/leaf x) _ =
    inj₁ (fP x)

  comm/ready-or-∈T fP fR cR (wv/cycle _ inT) _ =
    inj₂ inT

  comm/ready-or-∈T fP fR cR (wv/step na gr k) wR
    with comm/ready-or-∈T fP fR cR (k gr)
           (λ R m → waitV/unfold-top cR (wR R m) (λ w → w)
                      (proj₂ (receiver-step na fR (wR R m)) gr))
  ... | inj₁ (_ , (γ , eq , g)) =
    let naR : ∀ R → R ∈ _ → R not-active-in _
        naR R m = proj₁ (receiver-step na fR (wR R m))
        G′ , g′ = no-new-comm/step gr (multicast-idle na gr naR g eq) g
    in inj₁ (G′ , (γ , eq , g′))
  ... | inj₂ pInT =
    inj₂ (in/later gr pInT)

  -- The fold path: a cycle WAS hit on P's side, so walk the `P ∈T G` witness
  -- instead, decreasing on it and re-rooting all trees in lockstep.
  comm/ready-from-∈T :
    ∀ {G P Qs c}
      {𝒮P : Behavs}
      {𝒮R : Part → Behavs}
    → (∀ {u} → 𝒮P u → ∃[ u′ ] u -<[ P ↦ (! Qs) # c ]>-> u′)
    → (∀ {R u} → 𝒮R R u → ∃[ α ] ∃[ t ] (u -< α >-> t) × P ∈α α)
    → Closed 𝒮P
    → (∀ {R} → Closed (𝒮R R))
    → WaitV P 𝒮P (λ _ → ⊥) G
    → P ∈T G
    → (∀ R → R ∈ Qs → WaitV R (𝒮R R) (λ _ → ⊥) G)
    → ∃[ G′ ] G -<[ P ↦ (! Qs) # c ]>-> G′

  comm/ready-from-∈T fP fR cP cR (wv/leaf x) _ _ =
    fP x

  comm/ready-from-∈T fP fR cP cR (wv/cycle (_ , () , _) _) _ _

  comm/ready-from-∈T {P = P} fP fR cP cR
    (wv/step na _ _) (_ , _ , tr/step {α = α} gr′ _ , here px) _ =
    ⊥-elim (∉α→¬∈α {P} {α} (na gr′) px)

  comm/ready-from-∈T fP fR cP cR
    topP@(wv/step na _ kP)
    (_ , H , tr/step gr′ tr , there mem)
    wR =
    let _ , (γ , eq , g) =
          comm/ready-from-∈T fP fR cP cR
            (waitV/unfold-top cP topP (λ w → w) (kP gr′))
            (_ , H , tr , mem)
            (λ R m → waitV/unfold-top cR (wR R m) (λ w → w)
                       (proj₂ (receiver-step na fR (wR R m)) gr′))
        naR : ∀ R → R ∈ _ → R not-active-in _
        naR R m = proj₁ (receiver-step na fR (wR R m))
        G′ , g′ = no-new-comm/step gr′ (multicast-idle na gr′ naR g eq) g
    in G′ , (γ , eq , g′)

  -- The send/recv specifics enter here and nowhere else: `fP`/`fR` project
  -- the edge out of each rule's leaf family, and `cP`/`cR` close them
  -- under `~`.
  comm/ready :
    ∀ {G P Qs I}
      {i : Fin (suc I)}
      {S : Sort}
    → Wait P (Dom P ((! Qs) # i < S >)) ([] , G)
    → (∀ R → R ∈ Qs → Wait R (Offers P R I) ([] , G))
    → ∃[ G′ ] G -<[ P ↦ (! Qs) # i < S > ]>-> G′

  comm/ready {G} {P} {Qs} {I} {i} {S} wP wR =
    go (comm/ready-or-∈T {𝒮R = 𝒮R} fP fR cR wP wR)
    where
      e = (! Qs) # i < S >

      𝒮P : Behavs
      𝒮P u = Dom P e ([] , u)

      𝒮R : Part → Behavs
      𝒮R R u = Offers P R I ([] , u)

      fP : ∀ {u} → 𝒮P u → ∃[ u′ ] u -<[ P ↦ e ]>-> u′
      fP x = x

      fR : ∀ {R u} → 𝒮R R u → ∃[ α ] ∃[ t ] (u -< α >-> t) × P ∈α α
      fR (_ , _ , _ , (α , eq , g)) = α , _ , g , recv-sender g eq

      cP : Closed 𝒮P
      cP G~H (_ , (α , eq , g)) = _ , (α , eq , ~L→ G~H g)

      cR : ∀ {R} → Closed (𝒮R R)
      cR G~H (j , U , _ , (α , eq , g)) = j , U , _ , (α , eq , ~L→ G~H g)

      go :
        (∃[ G′ ] G -<[ P ↦ e ]>-> G′) ⊎ P ∈T G
        → ∃[ G′ ] G -<[ P ↦ e ]>-> G′
      go (inj₁ res)  = res
      go (inj₂ pInT) =
        comm/ready-from-∈T {𝒮R = 𝒮R} fP fR cP cR wP pInT wR

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
      (at⇒typing (at/rec/unfold sync (at/lookup M⊢G Prec)))

  preservation/comm :
    ∀ (M : Session)
      {G M' α}
    → ⊢s M ∶ G
    → M [ just α ]⇒ M'
    → ∃[ G' ] G -< α >-> G' × ⊢s M' ∶ G'

  -- `P`'s own `Wait` fixes the sort `S`; the step found is `P`'s multicast
  -- (`send-action`), and each receiver's continuation is read off it.
  preservation/comm M M⊢G (s/comm {Qs = Qs} {i = i} P Psnd e⇓v recvs)
    with at/send-inv (at/lookup M⊢G Psnd)
  ... | S , etd , wP , k
    with comm/ready wP
           (λ R m → proj₁ (at/recv-inv (at/lookup M⊢G (recvs R m))))
  ...   | G′ , (α , eq , g)
    with send-action g eq
  ...     | P∉Qs , refl =
    let vtd  = exp-pres etd e⇓v
        std′ = k ε (_ , eq , g)
        rtd  = λ R m →
          let R≢P = λ { refl → P∉Qs m }
              eqR = ev-recv {P} {Qs} {i < S >} {R} R≢P m
          in at⇒typing
               (at/subst-expr sync (te/val vtd)
                 (recv/cont (at/lookup M⊢G (recvs R m)) (_ , eqR , g)))
    in
    G′ ,
    subst
      (λ U → _ -< P ⟶ Qs # i < U > >-> G′)
      (sort/value-typed vtd)
      g ,
    ⊢s-comm-update M g M⊢G (at⇒typing std′) rtd

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
