{-# OPTIONS --guardedness #-}

-- `⊢a → ⊢p` DIRECTLY — no old, deleted two-tier `⊢a` anywhere in it.
--
-- The old, deleted `SetsAlg.agda`'s `set⇒alg` landed in that old `⊢a`, and
-- `Safety/` then crossed to `⊢p` with `alg/typing`, which is why the old
-- `⊢a` still appeared at the `⊢s` boundary.  This file removes that hop:
-- the two proofs have the same shape, and the only difference is which leaf
-- the `skip/map` builds — `blocked/send` there, `t/send` here.
--
-- The two rules whose leaf is not literally a declarative rule are `a/var`
-- and `a/rec`, and both are one `t/unskip` away: their leaf family is
-- `Reach₀`, and `t/unskip` is exactly "walk forward along a `¬P` run",
-- which is what `Reach₀` records.
--
-- The other direction is `AlgNorm.agda`'s `typing⇒alg`, also direct.  With
-- the two together the old two-tier `⊢a` is gone: there are TWO systems, the
-- declarative one and this one, and nothing in between.

open import Data.Nat using (ℕ; suc)

open import Data.Fin using (Fin)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_)

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

  -- Soundness against the DECLARATIVE system, stated the same way the old,
  -- deleted `SetsAlg.agda`'s `set⇒alg` was stated against the old `⊢a`.
  alg⇒typing :
    ∀ {Γ : Vec Sort γ}{Δ : Vec Behav δ}{PPr}{𝒮 : Pred}{G}
    → Γ & Δ ⊢a PPr ∶ 𝒮
    → 𝒮 G
    → Γ & Δ ⊢p PPr ∶ G

  alg⇒typing (a/send {P = P}{Q = Q}{i = i}{E = E}{Pr = Pr} etd td _ sub) 𝒮G =
    t/skip
      (skip/map
        (λ { (_ , gr , 𝒯u′) → t/send gr etd (alg⇒typing td 𝒯u′) })
        (wait⇒skip P (Q ! i < E >∙ Pr) _ (sub 𝒮G)))

  alg⇒typing (a/recv {P = P}{Q = Q}{Br = Br} conts _ sub) 𝒮G =
    t/skip
      (skip/map
        (λ { ((_ , _ , _ , gr) , k) →
               t/recv gr (λ gr′ → alg⇒typing (conts (k gr′)) (k gr′)) })
        (wait⇒skip Q (Σ P ？· Br) _ (sub 𝒮G)))

  alg⇒typing (a/if etd ttd ftd) 𝒮G =
    t/if etd (alg⇒typing ttd 𝒮G) (alg⇒typing ftd 𝒮G)

  alg⇒typing (a/end done) 𝒮G =
    t/end (done 𝒮G)

  -- `Reach₀ P ⌈ lu Δ X ⌉ H` is `lu Δ X ~ a` and `a -[¬ P ]->* H`: the first is
  -- `t/var`'s premise verbatim, the second is `t/unskip`'s.
  alg⇒typing (a/var {P = P}{X = X} sub) 𝒮G =
    t/skip
      (skip/map
        (λ { (_ , W~a , tr) → t/unskip tr (t/var W~a) })
        (wait⇒skip P (v X) _ (sub 𝒮G)))

  alg⇒typing (a/rec {P = P}{Pr = Pr} guarded td sub) 𝒮G =
    t/skip
      (skip/map
        (λ { (_ , 𝒜W , tr) →
               t/unskip tr (t/rec guarded (alg⇒typing (td 𝒜W) ~refl)) })
        (wait⇒skip P (rec Pr) _ (sub 𝒮G)))

  -- The pointwise form, for `Safety/`'s `⊢s` boundary.
  ⊨⇒typing :
    ∀ {Γ : Vec Sort γ}{Δ : Vec Behav δ}{PPr}{G}
    → Γ & Δ ⊨ PPr ∶ G
    → Γ & Δ ⊢p PPr ∶ G

  ⊨⇒typing (_ , d , mem) = alg⇒typing d mem
