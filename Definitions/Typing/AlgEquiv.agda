{-# OPTIONS --guardedness #-}

-- TODO.md §7 step 4/4b: the `Wait` characterisation, BOTH directions.
--
--     Wait P 𝒮 G  ⟺  (Leaf = 𝒮) & [] ⊢skip P ◂ Pr ∶ G
--
-- `⟸` is what makes the rules complete for `⊢a`, `⟹` is what makes them
-- sound.  With the old ν-based `Wait` the `⟹` half was FALSE
-- (`Tests/WaitNotSkip.agda`); with `WaitV`'s visited set both halves are plain
-- structural recursions and hold for every theory — no finiteness assumption,
-- nothing graph-specific.
--
-- The whole content is the translation between the two representations of the
-- ancestor context:
--
--     Ξ : Vec Behav ξ      ↦      Vof Ξ = { s | ∃ X. lu Ξ X ~ s }
--
-- under which `skip/main ↔ wv/leaf`, `skip/step ↔ wv/step` and
-- `skip/cycle ↔ wv/cycle` correspond one for one.
--
-- One thing that shapes the file.  `wv/step`'s subtree is indexed by
-- `Vof Ξ ∪ ⌈G⌉`, which is not syntactically `Vof (G ∷ Ξ)`, so the two have to
-- be reconciled at every step.  Doing that on the ARGUMENT of the recursive
-- call — `waitV⇒skip (waitV/mono … (k gr′))` — costs structurality and Agda
-- rejects it (CLAUDE.md: a recursion stops being structural the moment you
-- repack its argument).  So `waitV⇒skip` is generalised over an arbitrary `V`
-- together with an inclusion `V ⊆ Vof Ξ`, and the reconciliation happens in
-- that inclusion instead, leaving `k gr′` untouched.  `skip⇒waitV` has no such
-- problem: there the repacking lands on the RESULT.

open import Data.Nat using (ℕ; suc)

open import Data.Fin using (Fin; zero; suc)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Data.Product using (∃-syntax; _,_; _×_; proj₂)

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Empty using (⊥)

open import Relation.Nullary using (¬_)

open import Definitions.Typing

module Definitions.Typing.AlgEquiv {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  open module M = MPST(wb)
  open M

  open import Definitions.Typing.Alg wb
  open import Definitions.Typing.MainLeaf wb using (findMain)

  module _ {γ δ : ℕ}
           (P : Part)
           (Pr : Proc γ δ)
           (𝒮 : Behavs)
           where

    -- "(Leaf = 𝒮)": the leaf family ignores the process.
    Lf : NProc γ δ → Behav → Set
    Lf _ G = 𝒮 G

    -- ═════════════════════════════════════════════════════════════════
    --  ⟸  a `⊢skip` tree is a `WaitV`
    -- ═════════════════════════════════════════════════════════════════

    skip⇒waitV :
      ∀ {ξ}{Ξ : Vec Behav ξ}{G}
      → (Lf & Ξ ⊢skip P ◂ Pr ∶ G)
      → WaitV P 𝒮 (Vof Ξ) G

    skip⇒waitV (skip/main leaf) =
      wv/leaf leaf

    skip⇒waitV (skip/cycle {X = X} eq inT) =
      wv/cycle (_ , (X , ~refl) , eq) inT

    skip⇒waitV (skip/step gr na ktd) =
      wv/step na gr
        (λ gr′ →
          waitV/mono
            (λ { (zero  , eq) → inj₂ eq
               ; (suc X , eq) → inj₁ (X , eq) })
            (skip⇒waitV (ktd gr′)))

    -- ═════════════════════════════════════════════════════════════════
    --  ⟹  a `WaitV` is a `⊢skip` tree
    -- ═════════════════════════════════════════════════════════════════

    waitV⇒skip :
      ∀ {ξ}{Ξ : Vec Behav ξ}{V : Behavs}{G}
      → (∀ {s} → V s → Vof Ξ s)
      → WaitV P 𝒮 V G
      → Lf & Ξ ⊢skip P ◂ Pr ∶ G

    waitV⇒skip f (wv/leaf x) =
      skip/main x

    -- The ancestor is reached up to `~` on both sides, so `~trans` is the
    -- whole of it — closing against a DISTANT ancestor costs nothing extra.
    waitV⇒skip f (wv/cycle (a , a∈ , a~G) inT)
      with f a∈
    ... | X , luX~a =
      skip/cycle (~trans luX~a a~G) inT

    waitV⇒skip f (wv/step na gr k) =
      skip/step gr na
        (λ gr′ →
          waitV⇒skip
            (λ { (inj₁ x)   → let X , eq = f x in suc X , eq
               ; (inj₂ G~v) → zero , G~v })
            (k gr′))

    -- ═════════════════════════════════════════════════════════════════
    --  The characterisation at the root, where `Ξ = []` and `V = ∅`
    -- ═════════════════════════════════════════════════════════════════

    skip⇒wait :
      ∀ {G}
      → (Lf & [] ⊢skip P ◂ Pr ∶ G)
      → WaitV P 𝒮 (λ _ → ⊥) G

    skip⇒wait d =
      waitV/mono (λ { (() , _) }) (skip⇒waitV d)

    wait⇒skip :
      ∀ {G}
      → WaitV P 𝒮 (λ _ → ⊥) G
      → (Lf & [] ⊢skip P ◂ Pr ∶ G)

    wait⇒skip w =
      waitV⇒skip (λ ()) w

  -- D4 (TODO.md §5.1) for the set formulation, now a transport rather than a
  -- second proof: `Wait P ∅` is empty because a leafless `⊢skip` tree has
  -- no main leaf to find (`findMain` at the empty leaf family).
  -- This is what licenses `a/if`/`a/end` carrying no `Wait` premise.
  wait/∅ :
    ∀ {γ δ}{P}{Pr : Proc γ δ}{G}
    → ¬ WaitV P (λ _ → ⊥) (λ _ → ⊥) G

  wait/∅ {P = P}{Pr = Pr} w =
    proj₂ (findMain P Pr (λ _ _ → ⊥) (wait⇒skip P Pr (λ _ → ⊥) w))
