{-# OPTIONS --guardedness #-}

-- Bisimilarity transport for the ALGORITHMIC judgment.
--
-- `Properties.agda` has this for `⊢p` (`td/bisim`/`skip-td/bisim`); this is the
-- same recursion one level down, over `⊢a`/`⊢blocked`/the `⊢blocked`-leaved
-- `⊢skip` tree.  Going through the round trip instead — `alg/typing`, then
-- `td/bisim`, then `norm` — would drag in `Norm.agda`'s `MainLeaf` hypothesis
-- for no gain, since the direct recursion is the same length as `td/bisim`.
--
-- Needed by `SetsAlg.agda`'s completeness half at `s/rec`, whose premise is
-- stated at the `~`-closed anchor `⌈ W ⌉` (TODO.md §5.2): showing that every
-- state bisimilar to `W` is algorithmically typeable is exactly this lemma.

open import Data.Nat using (ℕ)

open import Data.Vec using (Vec; []; _∷_)

open import Data.Product using (_,_)

open import Function using (_∘_)

open import Definitions.Typing
import Definitions.Typing.Properties as Props

module Definitions.Typing.AlgProperties {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  open module M = MPST(wb)
  open M

  open Props wb using (skip/bisim; skip/bisim-back)

  open import Definitions.Typing.Algorithmic wb

  mutual

    blocked/bisim :
      ∀ {γ δ G G′ P}
        {Pr : Proc γ δ}
        {Γ : Vec Sort γ}
        {Δ Δ′ : Vec Behav δ}
      → Δ ~ᵛ Δ′
      → G ~ G′
      → Γ & Δ  ⊢blocked P ◂ Pr ∶ G
      → Γ & Δ′ ⊢blocked P ◂ Pr ∶ G′

    blocked/bisim Δ~ G~ (blocked/send gr etd td) =
      blocked/send
        (~L→ G~ gr)
        etd
        (alg/bisim Δ~ (~L→~ G~ gr) td)

    -- The anchor moves with `Δ`, so the run is transported at its SOURCE.
    blocked/bisim Δ~ G~ (blocked/var {X = X} tr H~G) =
      let _ , tr′ , H″~H = skip/bisim-back (lookup/~ᵛ Δ~ X ~refl) tr
      in blocked/var tr′ (~trans H″~H (~trans H~G G~))

    blocked/bisim Δ~ G~ (blocked/recv gr conts) =
      blocked/recv
        (~L→ G~ gr)
        (λ gr′ →
          alg/bisim Δ~ (~R→~ G~ gr′) (conts (~R→ G~ gr′)))

    -- Here the run is transported at its TARGET, which moves the anchor `W`
    -- too — hence the `~ᵛ/∷` on the body's environment.
    blocked/bisim Δ~ G~ (blocked/rec tr guarded td) =
      let _ , W~W′ , tr′ = skip/bisim G~ tr
      in blocked/rec tr′ guarded (alg/bisim (~ᵛ/∷ W~W′ Δ~) W~W′ td)

    skipA/bisim :
      ∀ {γ δ ξ G G′ P Pr}
        {Γ : Vec Sort γ}
        {Δ Δ′ : Vec Behav δ}
        {Ξ Ξ′ : Vec Behav ξ}
      → Δ ~ᵛ Δ′
      → Ξ ~ᵛ Ξ′
      → G ~ G′
      → (Γ & Δ  ⊢blocked_∶_) & Ξ  ⊢skip P ◂ Pr ∶ G
      → (Γ & Δ′ ⊢blocked_∶_) & Ξ′ ⊢skip P ◂ Pr ∶ G′

    skipA/bisim Δ~ Ξ~ G~ (skip/main x) =
      skip/main (blocked/bisim Δ~ G~ x)

    skipA/bisim Δ~ Ξ~ G~ (skip/step gr na ktd) =
      skip/step
        (~L→ G~ gr)
        (na ∘ ~R→ G~)
        (λ gr′ →
          skipA/bisim
            Δ~
            (~ᵛ/∷ G~ Ξ~)
            (~R→~ G~ gr′)
            (ktd (~R→ G~ gr′)))

    skipA/bisim Δ~ Ξ~ G~ (skip/cycle eq inT) =
      skip/cycle (~trans (lookup/~ᵛ Ξ~ _ eq) G~) (∈~ G~ inT)

    alg/bisim :
      ∀ {γ δ G G′ P}
        {Pr : Proc γ δ}
        {Γ : Vec Sort γ}
        {Δ Δ′ : Vec Behav δ}
      → Δ ~ᵛ Δ′
      → G ~ G′
      → Γ & Δ  ⊢a P ◂ Pr ∶ G
      → Γ & Δ′ ⊢a P ◂ Pr ∶ G′

    alg/bisim Δ~ G~ (a/skip std) =
      a/skip (skipA/bisim Δ~ ~ᵛ/[] G~ std)

    alg/bisim Δ~ G~ (a/if etd ttd ftd) =
      a/if etd (alg/bisim Δ~ G~ ttd) (alg/bisim Δ~ G~ ftd)

    alg/bisim Δ~ G~ (a/end done) =
      a/end (done ∘ ∈~ (~sym G~))

  -- The common case: only the state moves.
  alg/~ :
    ∀ {γ δ G G′ P}
      {Pr : Proc γ δ}
      {Γ : Vec Sort γ}
      {Δ : Vec Behav δ}
    → G ~ G′
    → Γ & Δ ⊢a P ◂ Pr ∶ G
    → Γ & Δ ⊢a P ◂ Pr ∶ G′

  alg/~ =
    alg/bisim ~ᵛ-refl
