{-# OPTIONS --guardedness #-}

-- `⊢a → ⊢p`, for every theory.
--
-- Each `Wait` premise becomes a `t/skip` tree (`wait⇒skip`), whose leaves
-- are mapped to the declarative rule.  For `a/send`/`a/recv` the leaf must
-- also be in `Front`, so the tree is first decorated with the idle walk from
-- its root (`waitV/walk`).  `a/var`/`a/rec` are one `t/unskip` away: their
-- leaves are `Unskip`, which is exactly `t/unskip`'s premise.
--
-- The anchors of a state are the declarative `Δ`.
--
-- The other direction is `AlgNorm.agda`'s `typing⇒alg`.

open import Data.Nat using (ℕ; suc)

open import Data.Vec using (Vec; []; _∷_)

open import Data.Product using (_,_)

open import Relation.Binary.PropositionalEquality using (refl)

open import Relation.Unary using (_∈_)

open import Definitions.Typing

module Definitions.Typing.AlgDeclarative
  {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where

  open module M = MPST(wb)
  open M

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
             (a/send {P = P}{Qs}{i = i}{E = E}{Pr} etd rdy td) mem =
    t/skip
      (skip/map
        (λ { ((_ , (α , eq , g)) , run) →
             t/send (α , eq , g) etd
               (alg⇒typing td
                 (_ , ((G , mem , run) , (α , _ , g , (_ , eq)))
                    , (α , eq , g))) })
        (wait⇒skip P (Qs ! i < E >∙ Pr) _ (waitV/walk (rdy {ws , G} mem))))

  alg⇒typing {ws = ws}{G} (a/recv {P = P}{Q}{Br = Br} rdy conts) mem =
    t/skip
      (skip/map
        (λ { ((_ , _ , _ , (α , eq , g)) , run) →
             t/recv (α , eq , g)
               (λ gr′ →
                 let x∈ = _ , ((G , mem , run) , (α , _ , g , (_ , eq))) , gr′
                 in alg⇒typing (conts (_ , x∈)) x∈) })
        (wait⇒skip Q (Σ P ？· Br) _ (waitV/walk (rdy {ws , G} mem))))

  alg⇒typing (a/if etd ttd ftd) mem =
    t/if etd (alg⇒typing ttd mem) (alg⇒typing ftd mem)

  alg⇒typing {ws = ws}{G} (a/end done) mem =
    t/end (done {ws , G} mem)

  alg⇒typing {ws = ws}{G} (a/var {P = P}{X} rdy) mem =
    t/skip
      (skip/map
        (λ { (_ , W~a , tr) → t/unskip tr (t/var W~a) })
        (wait⇒skip P (v X) _ (rdy {ws , G} mem)))

  alg⇒typing {ws = ws}{G} (a/rec {P = P}{Pr} guarded td rdy) mem =
    t/skip
      (skip/map
        (λ { (_ , a∈ , tr) →
             t/unskip tr (t/rec guarded (alg⇒typing td (a∈ , ~refl))) })
        (wait⇒skip P (rec Pr) _ (rdy {ws , G} mem)))

  at⇒typing :
    ∀ {Γ : Vec Sort γ}{PPr : NProc γ δ}{ws G}
    → Γ ⊢at PPr ∶ (ws , G)
    → Γ & ws ⊢p PPr ∶ G

  at⇒typing (_ , d , mem) = alg⇒typing d mem
