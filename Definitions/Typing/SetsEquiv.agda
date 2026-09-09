{-# OPTIONS --guardedness #-}

-- TODO.md §7 step 4: the `Wait` characterisation,
--
--     s ∈ Wait P 𝒮  ⟺  (Leaf = 𝒮) & [] ⊢skip P ◂ Pr ∶ s
--
-- This file has the `⟸` half — from a `⊢skip` derivation, build a `Wait`.
-- (`⟹` is the direction that turns a coinductive object into a finite tree
-- and so needs a finiteness assumption; `WellBehaved` has none.  See §7.)
--
-- Two things that shape the whole file.
--
-- **The bisimilarity is carried INTO the statement** (`… ∶ G → G ~ s → Wait P 𝒮 s`)
-- rather than applied afterwards.  Transporting after the fact, as
-- `wait/~ c G~s (…)`, puts the corecursive call in an ARGUMENT position, where
-- it is not guarded and Agda rejects it.  Carrying the `~` keeps every
-- corecursive call directly under a constructor.
--
-- **`Anc` stores each ancestor's `skip/step` PREMISES, not its derivation.**
-- Storing the derivation looks tidier but does not typecheck: `Reach∀⁺` admits
-- no guard leaf at depth 0, so the function a cycle jumps back into must be
-- known to be at a `skip/step` node.  Every entry of `Ξ` is one, because `Ξ`
-- only ever grows at `skip/step` — but that fact has to be in the type.

open import Data.Nat using (ℕ; suc)

open import Data.Fin using (Fin; zero; suc)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Data.Product using (_,_; _×_)

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Definitions.Typing

module Definitions.Typing.SetsEquiv {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  open module M = MPST(wb)
  open M

  open import Definitions.Typing.Sets wb

  module _ {γ δ : ℕ}
           (P : Part)
           (Pr : Proc γ δ)
           (𝒮 : Pred)
           (c : Closed 𝒮)
           where

    -- "(Leaf = 𝒮)": the leaf family ignores the process.
    Lf : NProc γ δ → Behav → Set
    Lf _ G = 𝒮 G

    -- The visited vector, with each entry's `skip/step` premises attached.
    data Anc : ∀ {ξ} → Vec Behav ξ → Set where

      anc/nil : Anc []

      anc/cons :
        ∀ {ξ}{Ξ : Vec Behav ξ}{A α A′}
        → (na  : P not-active-in A)
        → (gr  : A -< α >-> A′)
        → (ktd : ∀ {A″ β} → A -< β >-> A″ → Lf & A ∷ Ξ ⊢skip P ◂ Pr ∶ A″)
        → Anc Ξ
        → Anc (A ∷ Ξ)

    -- What a `skip/cycle` needs about the ancestor it closes against.  Packaged
    -- as a record purely to keep `ancLu`'s result type readable; it is defined
    -- after `Anc`, so nothing here is circular.
    record Step (A : Behav) : Set where
      constructor mkStep
      field
        {ξ}  : ℕ
        {Ξ}  : Vec Behav ξ
        {α}  : Action
        {A′} : Behav
        anc  : Anc Ξ
        na   : P not-active-in A
        gr   : A -< α >-> A′
        ktd  : ∀ {A″ β} → A -< β >-> A″ → Lf & A ∷ Ξ ⊢skip P ◂ Pr ∶ A″

    open Step

    ancLu :
      ∀ {ξ}{Ξ : Vec Behav ξ}
      → Anc Ξ
      → (X : Fin ξ)
      → Step (lu Ξ X)

    ancLu (anc/cons na gr ktd anc) zero =
      mkStep anc na gr ktd

    ancLu (anc/cons na gr ktd anc) (suc X) =
      ancLu anc X

    leafWait : ∀ {s} → 𝒮 s → Wait P 𝒮 s
    force (leafWait x) = r/leaf⁺ x

    mutual

      -- Corecursive half: a `skip/step` node at `A` yields a `Wait` at anything
      -- bisimilar to `A`.  This is the only place a `Wait` is produced, and the
      -- `r/step⁺` is what discharges `Reach∀⁺`'s progress condition.
      stepNode :
        ∀ {ξ}{Ξ : Vec Behav ξ}{A α A′ s}
        → Anc Ξ
        → P not-active-in A
        → A -< α >-> A′
        → (∀ {A″ β} → A -< β >-> A″ → Lf & A ∷ Ξ ⊢skip P ◂ Pr ∶ A″)
        → A ~ s
        → Wait P 𝒮 s

      force (stepNode anc na gr ktd A~s) =
        r/step⁺
          (na-bisim A~s na)
          (~L→ A~s gr)
          (λ gr′ →
            toReach (anc/cons na gr ktd anc) (ktd (~R→ A~s gr′)) (~R→~ A~s gr′))

      -- Inductive half: an arbitrary derivation at `G` yields a `Reach∀` at
      -- anything bisimilar to `G`.  Guard leaves ARE available here, which is
      -- exactly right — this is only ever reached strictly below a step.
      toReach :
        ∀ {ξ}{Ξ : Vec Behav ξ}{G s}
        → Anc Ξ
        → (Lf & Ξ ⊢skip P ◂ Pr ∶ G)
        → G ~ s
        → Reach∀ P (λ v → 𝒮 v ⊎ (P ∈T v × Wait P 𝒮 v)) s

      toReach anc (skip/main leaf) G~s =
        r/leaf (inj₁ (c G~s leaf))

      toReach anc (skip/step gr na ktd) G~s =
        r/step
          (na-bisim G~s na)
          (~L→ G~s gr)
          (λ gr′ →
            toReach (anc/cons na gr ktd anc) (ktd (~R→ G~s gr′)) (~R→~ G~s gr′))

      -- `eq : lu Ξ X ~ G` and `G ~ s`, so the ancestor is bisimilar to `s` and
      -- `stepNode` re-enters its subtree there.  Closing against a DISTANT
      -- ancestor costs nothing extra: `~trans` is the whole of it.
      toReach anc (skip/cycle {X = X} eq inT) G~s
        with ancLu anc X
      ... | mkStep anc′ na′ gr′ ktd′ =
        r/leaf (inj₂ (∈~ G~s inT , stepNode anc′ na′ gr′ ktd′ (~trans eq G~s)))

    -- `skip/cycle` cannot fire at the root: `Ξ = []`, so there is no `X`.
    skip⇒wait~ :
      ∀ {G s}
      → (Lf & [] ⊢skip P ◂ Pr ∶ G)
      → G ~ s
      → Wait P 𝒮 s

    skip⇒wait~ (skip/main leaf) G~s =
      leafWait (c G~s leaf)

    skip⇒wait~ (skip/step gr na ktd) G~s =
      stepNode anc/nil na gr ktd G~s

    skip⇒wait~ (skip/cycle {X = ()} _ _) _

    -- The `⟸` half of TODO.md §7 step 4.
    skip⇒wait :
      ∀ {G}
      → (Lf & [] ⊢skip P ◂ Pr ∶ G)
      → Wait P 𝒮 G

    skip⇒wait d =
      skip⇒wait~ d ~refl
