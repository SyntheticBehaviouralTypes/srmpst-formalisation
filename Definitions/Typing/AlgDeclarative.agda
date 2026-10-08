{-# OPTIONS --guardedness #-}

-- `⊢a → ⊢p` (`alg⇒typing`), for every theory.  Each `Wait` becomes a
-- `t/skip` tree (`wait⇒skip`); a state's anchors are the declarative `Δ`.

open import Data.Nat using (ℕ)

open import Data.Vec using (Vec)

open import Data.Product using (_,_)

open import Relation.Unary using (_∈_)

open import Definitions.Typing.Declarative

module Definitions.Typing.AlgDeclarative
  {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where

  open MPST wb

  open import Definitions.Typing.Alg wb
  open import Definitions.Typing.AlgEquiv wb using (wait⇒skip)
  open import Definitions.Typing.Properties wb using (skip/map)

  private
    variable
      γ δ : ℕ

  alg⇒typing :
    ∀ {Γ : Vec Sort γ}{PPr : NProc γ δ}{𝒮 : States δ}{ws G}
    → Γ ⊢a PPr ∶ 𝒮
    → (ws , G) ∈ 𝒮
    → Γ & ws ⊢p PPr ∶ G

  alg⇒typing {ws = ws}{G}
             (a/send {P = P}{Q}{Qs}{i = i}{E = E}{Pr} Q∈ etd rdy td) mem =
    t/skip
      (skip/map
        (λ { ((foc , _ , (α , eq , g)) , run) →
             t/send Q∈ foc (α , eq , g) etd
               (alg⇒typing td
                 (_ , ((G , mem , run) , (α , _ , g , (_ , Q∈ , _ , eq)))
                    , (α , eq , g))) })
        (wait⇒skip P (Q ⇒ Qs ! i < E >∙ Pr) _
          (waitV/walk (rdy {ws , G} mem))))

  alg⇒typing {ws = ws}{G}
             (a/recv {P = P}{Q}{R}{Br = Br} R∈ rdy conts) mem =
    t/skip
      (skip/map
        (λ { ((foc , _ , _ , _ , (α , eq , g , fr)) , run) →
             t/recv R∈ foc (α , eq , g , fr)
               (λ gr′ →
                 let x∈ = _ , ((G , mem , run)
                                , (α , _ , g , (_ , R∈ , _ , eq))) , gr′
                 in alg⇒typing (conts (_ , x∈)) x∈) })
        (wait⇒skip Q (R ⇐ P ？· Br) _ (waitV/walk (rdy {ws , G} mem))))

  alg⇒typing (a/if etd ttd ftd) mem =
    t/if etd (alg⇒typing ttd mem) (alg⇒typing ftd mem)

  alg⇒typing {ws = ws}{G} (a/end done) mem =
    t/end (done {ws , G} mem)

  alg⇒typing {ws = ws}{G} (a/var {P = P}{X} rdy) mem =
    t/skip
      (skip/map
        (λ { (_ , W~a , _ , tr , eq) → t/unskip tr eq (t/var W~a) })
        (wait⇒skip P (v X) _ (rdy {ws , G} mem)))

  alg⇒typing {ws = ws}{G} (a/rec {P = P}{Pr} guarded td rdy) mem =
    t/skip
      (skip/map
        (λ { (_ , a∈ , _ , tr , eq) →
             t/unskip tr eq (t/rec guarded (alg⇒typing td (a∈ , ~refl))) })
        (wait⇒skip P (rec Pr) _ (rdy {ws , G} mem)))

  at⇒typing :
    ∀ {Γ : Vec Sort γ}{PPr : NProc γ δ}{ws G}
    → Γ ⊢at PPr ∶ (ws , G)
    → Γ & ws ⊢p PPr ∶ G

  at⇒typing (_ , d , mem) = alg⇒typing d mem
