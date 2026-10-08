{-# OPTIONS --guardedness #-}

-- `Wait P 𝒮 G ⟺ (Leaf = 𝒮) & [] ⊢skip P ◂ Pr ∶ G`, for every theory.  The
-- visited vector `Ξ` corresponds to the set `Vof Ξ`.  `waitV⇒skip` takes an
-- inclusion `V ⊆ Vof Ξ` so that its recursion stays structural.

open import Data.Nat using (ℕ; suc)

open import Data.Fin using (zero; suc)

open import Data.Vec using (Vec; [])

open import Data.Product using (_,_)

open import Data.Sum using (inj₁; inj₂)

open import Data.Empty using (⊥)

open import Definitions.Typing.Declarative

module Definitions.Typing.AlgEquiv {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  open MPST wb

  open import Definitions.Typing.Alg wb

  module _ {γ δ : ℕ}
           (P : PartSet)
           (Pr : Proc γ δ)
           (𝒮 : Behavs)
           where

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
