{-# OPTIONS --guardedness #-}

-- `Wait P 𝒮 G ⟺ SkipT P 𝒮 [] G`, for every theory.  `SkipT` is the shape
-- of the paper's skipping judgement on states, with leaves in a set `𝒮`;
-- `AlgDeclarative` turns it into the judgement.  The visited vector `Ξ`
-- corresponds to the set `Vof Ξ`.  `waitV⇒skip` takes an inclusion
-- `V ⊆ Vof Ξ` so that its recursion stays structural.

open import Data.Nat using (ℕ; suc)

open import Data.Fin using (Fin; zero; suc)

open import Data.Vec using (Vec; []; _∷_) renaming (lookup to lu)

open import Data.Product using (_,_)

open import Data.Sum using (inj₁; inj₂)

open import Relation.Unary using () renaming (∅ to ∅S)

open import Relation.Nullary using (¬_)

open import Definitions.Typing.Declarative

module Definitions.Typing.AlgEquiv {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  open MPST wb

  open import Definitions.Typing.Alg wb

  -- ═════════════════════════════════════════════════════════════════
  --  Skip trees on states
  -- ═════════════════════════════════════════════════════════════════

  data SkipT (P : PartSet) (𝒮 : Behavs) {ξ} (Ξ : Vec Behav ξ) : Behav → Set where

    st/main :
      ∀ {G}
      → 𝒮 G
      → SkipT P 𝒮 Ξ G

    st/step :
      ∀ {α G G′}
      → G -< α >-> G′
      → ¬ G -⟨ P ⟩->
      → (∀ {G″ β} → G -< β >-> G″ → SkipT P 𝒮 (G ∷ Ξ) G″)
      → SkipT P 𝒮 Ξ G

    st/cycle :
      ∀ {X G}
      → lu Ξ X ~ G
      → P ∈T G
      → SkipT P 𝒮 Ξ G

  module _ (P : PartSet) (𝒮 : Behavs) where

    -- ═════════════════════════════════════════════════════════════════
    --  ⟸  a skip tree is a `WaitV`
    -- ═════════════════════════════════════════════════════════════════

    skip⇒waitV :
      ∀ {ξ}{Ξ : Vec Behav ξ}{G}
      → SkipT P 𝒮 Ξ G
      → WaitV P 𝒮 (Vof Ξ) G

    skip⇒waitV (st/main leaf) =
      wv/leaf leaf

    skip⇒waitV (st/cycle {X = X} eq inT) =
      wv/cycle (_ , (X , ~refl) , eq) inT

    skip⇒waitV (st/step gr na ktd) =
      wv/step na gr
        (λ gr′ →
          waitV/mono
            (λ { (zero  , eq) → inj₂ eq
               ; (suc X , eq) → inj₁ (X , eq) })
            (skip⇒waitV (ktd gr′)))

    -- ═════════════════════════════════════════════════════════════════
    --  ⟹  a `WaitV` is a skip tree
    -- ═════════════════════════════════════════════════════════════════

    waitV⇒skip :
      ∀ {ξ}{Ξ : Vec Behav ξ}{V : Behavs}{G}
      → (∀ {s} → V s → Vof Ξ s)
      → WaitV P 𝒮 V G
      → SkipT P 𝒮 Ξ G

    waitV⇒skip f (wv/leaf x) =
      st/main x

    waitV⇒skip f (wv/cycle (a , a∈ , a~G) inT)
      with f a∈
    ... | X , luX~a =
      st/cycle (~trans luX~a a~G) inT

    waitV⇒skip f (wv/step na gr k) =
      st/step gr na
        (λ gr′ →
          waitV⇒skip
            (λ { (inj₁ x)   → let X , eq = f x in suc X , eq
               ; (inj₂ G~v) → zero , G~v })
            (k gr′))

    -- ═════════════════════════════════════════════════════════════════
    --  The characterisation at the root, where `Ξ = []` and `V = ∅`
    -- ═════════════════════════════════════════════════════════════════

    skip⇒wait : ∀ {G} → SkipT P 𝒮 [] G → WaitV P 𝒮 ∅S G
    skip⇒wait d =
      waitV/mono (λ { (() , _) }) (skip⇒waitV d)

    wait⇒skip : ∀ {G} → WaitV P 𝒮 ∅S G → SkipT P 𝒮 [] G
    wait⇒skip w =
      waitV⇒skip (λ ()) w

  -- Rewriting a skip tree's leaves.
  skipT/map :
    ∀ {P}{𝒮 𝒯 : Behavs}{ξ}{Ξ : Vec Behav ξ}{G}
    → (∀ {H} → 𝒮 H → 𝒯 H)
    → SkipT P 𝒮 Ξ G → SkipT P 𝒯 Ξ G
  skipT/map f (st/main x)         = st/main (f x)
  skipT/map f (st/step gr na ktd) = st/step gr na (λ gr′ → skipT/map f (ktd gr′))
  skipT/map f (st/cycle eq inT)   = st/cycle eq inT
