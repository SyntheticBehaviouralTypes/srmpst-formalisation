{-# OPTIONS --guardedness #-}

-- `⊢set → ⊢p` DIRECTLY — no `⊢a` anywhere in it.
--
-- `SetsAlg.agda`'s `set⇒alg` lands in `⊢a`, and `Safety/` then crossed to `⊢p`
-- with `alg/typing`, which is why `⊢a` still appeared at the `⊢s` boundary.
-- This file removes that hop: the two proofs have the same shape, and the only
-- difference is which leaf the `skip/map` builds — `blocked/send` there,
-- `t/send` here.
--
-- The two rules whose leaf is not literally a declarative rule are `s/var` and
-- `s/rec`, and both are one `t/unskip` away: their leaf family is `Reach₀`, and
-- `t/unskip` is exactly "walk forward along a `¬P` run", which is what `Reach₀`
-- records.
--
-- The other direction is `SetsNorm.agda`'s `typing⇒set`, also direct.  With
-- the two together `⊢a` is gone: there are TWO systems, the declarative one
-- and the set-based one, and nothing in between.

open import Data.Nat using (ℕ; suc)

open import Data.Fin using (Fin)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_)

open import Definitions.Typing

module Definitions.Typing.SetsDeclarative
  {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where

  open module M = MPST(wb)
  open M

  open import Definitions.Typing.Sets wb
  open import Definitions.Typing.SetsEquiv wb using (wait⇒skip)
  open import Definitions.Typing.Properties wb using (skip/map)

  private
    variable
      γ δ : ℕ

  -- Soundness against the DECLARATIVE system, stated the same way `set⇒alg` is
  -- stated against the algorithmic one.
  set⇒typing :
    ∀ {Γ : Vec Sort γ}{Δ : Vec Behav δ}{PPr}{𝒮 : Pred}{G}
    → Γ & Δ ⊢ PPr ∶ 𝒮
    → 𝒮 G
    → Γ & Δ ⊢p PPr ∶ G

  set⇒typing (s/send {P = P}{Q = Q}{i = i}{E = E}{Pr = Pr} etd td _ sub) 𝒮G =
    t/skip
      (skip/map
        (λ { (_ , gr , 𝒯u′) → t/send gr etd (set⇒typing td 𝒯u′) })
        (wait⇒skip P (Q ! i < E >∙ Pr) _ (sub 𝒮G)))

  set⇒typing (s/recv {P = P}{Q = Q}{Br = Br} conts _ sub) 𝒮G =
    t/skip
      (skip/map
        (λ { ((_ , _ , _ , gr) , k) →
               t/recv gr (λ gr′ → set⇒typing (conts (k gr′)) (k gr′)) })
        (wait⇒skip Q (Σ P ？· Br) _ (sub 𝒮G)))

  set⇒typing (s/if etd ttd ftd) 𝒮G =
    t/if etd (set⇒typing ttd 𝒮G) (set⇒typing ftd 𝒮G)

  set⇒typing (s/end done) 𝒮G =
    t/end (done 𝒮G)

  -- `Reach₀ P ⌈ lu Δ X ⌉ H` is `lu Δ X ~ a` and `a -[¬ P ]->* H`: the first is
  -- `t/var`'s premise verbatim, the second is `t/unskip`'s.
  set⇒typing (s/var {P = P}{X = X} sub) 𝒮G =
    t/skip
      (skip/map
        (λ { (_ , W~a , tr) → t/unskip tr (t/var W~a) })
        (wait⇒skip P (v X) _ (sub 𝒮G)))

  set⇒typing (s/rec {P = P}{Pr = Pr} guarded td sub) 𝒮G =
    t/skip
      (skip/map
        (λ { (_ , 𝒜W , tr) →
               t/unskip tr (t/rec guarded (set⇒typing (td 𝒜W) ~refl)) })
        (wait⇒skip P (rec Pr) _ (sub 𝒮G)))

  -- The pointwise form, for `Safety/`'s `⊢s` boundary.
  ⊨⇒typing :
    ∀ {Γ : Vec Sort γ}{Δ : Vec Behav δ}{PPr}{G}
    → Γ & Δ ⊨ PPr ∶ G
    → Γ & Δ ⊢p PPr ∶ G

  ⊨⇒typing (_ , d , mem) = set⇒typing d mem
