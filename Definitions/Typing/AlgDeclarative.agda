{-# OPTIONS --guardedness #-}

-- `⊢a → ⊢` (`alg⇒typing`), for every theory: the paper's judgement at the
-- class of every state of the set.  Each `Wait` becomes a skip tree
-- (`wait⇒skip`), then the paper's skipping judgement (`skipT⇒`); a state's
-- anchors, as classes, are the paper's `Δ`.

open import Data.Nat using (ℕ)

open import Data.Fin using (zero; suc)

open import Data.Vec using (Vec; _∷_; map) renaming (lookup to lu)

open import Data.Vec.Properties using (lookup-map)

open import Data.Vec.Relation.Unary.Any using (here; there)

open import Data.Product using (_,_)

open import Relation.Binary.PropositionalEquality using (sym; subst)

open import Relation.Unary using (_∈_)

open import Definitions.Typing.Declarative

module Definitions.Typing.AlgDeclarative
  {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where

  open MPST wb

  open import Definitions.Typing.Alg wb
  open import Definitions.Typing.AlgEquiv wb
    using (SkipT; st/main; st/step; st/cycle; wait⇒skip; skipT/map)
  open import Definitions.Typing.Properties wb using (td/≐; skip-td/≐; ≐ᵛ-refl)

  private
    variable
      γ δ ξ : ℕ

  ∈ᵛclasses : ∀ {Ξ : Vec Behav ξ} X {G} → lu Ξ X ~ G → [ G ] ∈ᵛ (classes Ξ)
  ∈ᵛclasses {Ξ = _ ∷ _} zero    eq = here eq
  ∈ᵛclasses {Ξ = _ ∷ _} (suc X) eq = there (∈ᵛclasses X eq)

  ∶∈classes : ∀ {ws : Vec Behav δ} X {G} → lu ws X ~ G → X ∶ [ G ] ∈ (classes ws)
  ∶∈classes {ws = ws} X eq =
    subst (_≐ [ _ ]) (sym (lookup-map X [_] ws)) eq

  -- A skip tree on states, with typed leaves, is the paper's skipping
  -- judgement at the classes.
  skipT⇒ :
    ∀ {Γ : Vec Sort γ}{Δ : Vec Cls δ}{R}{P : Proc γ δ}{𝒮 : Behavs}
      {Ξ : Vec Behav ξ}{G}
    → (∀ {H} → 𝒮 H → Γ & Δ ⊢[ R ] P ∶ [ H ])
    → SkipT R 𝒮 Ξ G
    → Γ & Δ & (classes Ξ) ⊢[ R ] P ∶ [ G ]

  skipT⇒ f (st/main x) =
    skip-main (f x)

  skipT⇒ f (st/cycle {X = X} eq inT) =
    skip-cycle (∈ᵛclasses X eq) (∈T⇒ᶜ inT)

  skipT⇒ {R = R} f (st/step gr na k) =
    skip-step (_ , _ , step⇒ᶜ gr)
      (λ act → na (actᶜ⇒ act))
      (λ st →
        let H″ , gr′ , H″~ = stepᶜ⇒ st
        in skip-td/≐ ≐ᵛ-refl ≐ᵛ-refl H″~ (skipT⇒ f (k gr′)))

  -- A `Wait` at the root, with leaves typed, is a `skip`.
  wait⇒typing :
    ∀ {Γ : Vec Sort γ}{Δ : Vec Cls δ}{R}{P : Proc γ δ}{𝒮 : Behavs}{G}
    → (∀ {H} → 𝒮 H → Γ & Δ ⊢[ R ] P ∶ [ H ])
    → WaitV R 𝒮 _ G
    → Γ & Δ ⊢[ R ] P ∶ [ G ]
  wait⇒typing f w = skip (skipT⇒ f (wait⇒skip _ _ w))

  alg⇒typing :
    ∀ {Γ : Vec Sort γ}{R}{P : Proc γ δ}{𝒮 : States δ}{ws G}
    → Γ ⊢a R ◂ P ∶ 𝒮
    → (ws , G) ∈ 𝒮
    → Γ & (classes ws) ⊢[ R ] P ∶ [ G ]

  alg⇒typing {ws = ws}{G}
             (a/send {Q = Q} Q∈ etd rdy td) mem =
    wait⇒typing
      (λ { ((fi , _ , (α , eq , g)) , run) →
           send (first-in⇒ᶜ fi) (ev⇒ᶜ (α , eq , g)) etd
             (alg⇒typing td
               (_ , ((G , mem , run) , (_ , α , g , (_ , Q∈ , _ , eq)))
                  , (α , eq , g))) })
      (waitV/walk (rdy {ws , G} mem))

  alg⇒typing {ws = ws}{G}
             (a/recv {R = R} R∈ rdy conts) mem =
    wait⇒typing
      (λ { ((fi , P∉ , _ , _ , _ , (α , eq , g)) , run) →
           recv (first-in⇒ᶜ fi) P∉ (_ , _ , ev⇒ᶜ (α , eq , g))
             (λ gr′ →
               let t′ , (α′ , eq′ , g′) , t′~ = evᶜ⇒ gr′
                   x∈ = _ , ((G , mem , run)
                              , (_ , α , g , (_ , R∈ , _ , eq)))
                          , (α′ , eq′ , g′)
                   Pr , br , td = conts (_ , x∈)
               in Pr , br , td/≐ ≐ᵛ-refl t′~ (alg⇒typing td x∈)) })
      (waitV/walk (rdy {ws , G} mem))

  alg⇒typing (a/let etd td) mem =
    let′ etd (alg⇒typing td mem)

  alg⇒typing (a/if etd ttd ftd) mem =
    if etd (alg⇒typing ttd mem) (alg⇒typing ftd mem)

  alg⇒typing {ws = ws}{G} (a/end done) mem =
    end λ inT → done {ws , G} mem (∈Tᶜ⇒ inT)

  alg⇒typing {ws = ws}{G} (a/var {X = X} rdy) mem =
    wait⇒typing
      (λ { (_ , W~a , _ , run , eq) →
           td/≐ ≐ᵛ-refl eq
             (forward (var (∶∈classes {ws = ws} X W~a)) (run⇒ᶜ run)) })
      (rdy {ws , G} mem)

  alg⇒typing {ws = ws}{G} (a/rec guarded td rdy) mem =
    wait⇒typing
      (λ { (_ , a∈ , _ , run , eq) →
           td/≐ ≐ᵛ-refl eq
             (forward (rec (alg⇒typing td (a∈ , ~refl)) guarded) (run⇒ᶜ run)) })
      (rdy {ws , G} mem)

  at⇒typing :
    ∀ {Γ : Vec Sort γ}{R}{P : Proc γ δ}{ws G}
    → Γ ⊢at R ◂ P ∶ (ws , G)
    → Γ & (classes ws) ⊢[ R ] P ∶ [ G ]

  at⇒typing (_ , d , mem) = alg⇒typing d mem
