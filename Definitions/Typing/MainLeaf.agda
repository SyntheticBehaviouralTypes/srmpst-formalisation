{-# OPTIONS --guardedness #-}

-- Constructive main-leaf existence: every `⊢skip` tree HAS a `skip/main` leaf.
--
--     findMain : Leaf & [] ⊢skip P ◂ Pr ∶ G → ∃[ H ] Leaf (P ◂ Pr) H
--
-- This is `NoLoop.agda` generalised from the empty leaf family to an arbitrary
-- one, and from `⊥` to the leaf it finds.  `NoLoop`'s D4 is the special case:
-- with `Leaf = ⊥` the result is absurd, which is exactly `Loop-empty`.
--
-- Why it is not just "descend until you stop": descending along `skip/step`'s
-- own step witness terminates (the tree is inductive) but can land on a
-- `skip/cycle`, which is not a main leaf.  `NoLoop`'s argument is what rules
-- that out — a cycle leaf demands `P ∈T` at its own node, while every ancestor
-- on the path to it is `P`-inactive — and it is constructive, so it yields the
-- leaf rather than `¬¬∃`.  `findRun` is that argument, returning the leaf it
-- passes through instead of `⊥`; the `skip/main` case is the only one that
-- differs from `NoLoop.noLoop`.
--
-- NOTE this is the statement `Declarative.agda:173`'s `MainLeaf` is about and
-- that `Norm.agda:169` takes as a HYPOTHESIS.  TODO.md §5.1 records it as open
-- because the leafless argument was thought to give only `¬¬∃`; following the
-- `P ∈T` run, as `NoLoop` does, avoids that.  Discharging `Norm.agda`'s
-- hypothesis from this is not done here — its `MainLeaf` is an inductive
-- *relation* on a derivation, not a bare existential.

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)

open import Data.Empty using (⊥; ⊥-elim)

open import Data.List.Relation.Unary.Any using (Any; here; there)

open import Definitions.Typing

module Definitions.Typing.MainLeaf {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  open module M = MPST(wb)
  open M

  private
    variable
      γ δ ξ : ℕ

  module _ {γ δ : ℕ}
           (P : Part)
           (Pr : Proc γ δ)
           (Leaf : NProc γ δ → Behav → Set)
           where

    Found : Set
    Found = ∃[ H ] Leaf (P ◂ Pr) H

    -- Every entry of the visited vector is a `skip/step` node.
    data Anc : ∀ {ξ} → Vec Behav ξ → Set where

      anc/nil : Anc []

      anc/cons :
        ∀ {ξ}{Ξ : Vec Behav ξ}{A}
        → (na : P not-active-in A)
        → (ktd :
            ∀ {A′ β}
            → (gr′ : A -< β >-> A′)
            → Leaf & A ∷ Ξ ⊢skip P ◂ Pr ∶ A′)
        → Anc Ξ
        → Anc (A ∷ Ξ)

    ancLu :
      ∀ {ξ}{Ξ : Vec Behav ξ}
      → Anc Ξ
      → (X : Fin ξ)
      → (P not-active-in lu Ξ X)
      × (∀ {A′ β}
         → lu Ξ X -< β >-> A′
         → ∃[ ζ ] Σ[ Ξ′ ∈ Vec Behav ζ ]
             Anc Ξ′ × (Leaf & Ξ′ ⊢skip P ◂ Pr ∶ A′))

    ancLu (anc/cons na ktd anc) zero =
      na , λ gr′ → _ , _ , anc/cons na ktd anc , ktd gr′

    ancLu (anc/cons na ktd anc) (suc X) =
      ancLu anc X

    -- Follow a `P`-reaching run down the tree.  Structural on the `Any`
    -- witness, not on the tree — the `skip/cycle` jump walks back UP.
    findRun :
      ∀ {ξ}{Ξ : Vec Behav ξ}{G H αs}
      → Anc Ξ
      → Leaf & Ξ ⊢skip P ◂ Pr ∶ G
      → G -[ αs ]-> H
      → Any (P ∈α_) αs
      → Found

    -- The only case that differs from `NoLoop.noLoop`.
    findRun anc (skip/main x) _ _ =
      _ , x

    findRun anc (skip/step _ _ _) tr/refl ()

    findRun anc (skip/cycle _ _) tr/refl ()

    -- The run's first action is `P`'s, but this node is `P`-inactive.
    findRun anc (skip/step _ na _) (tr/step gr tr) (here px) =
      ⊥-elim (∉c→¬∈c (na gr) px)

    findRun anc (skip/step _ na ktd) (tr/step gr tr) (there mem) =
      findRun (anc/cons na ktd anc) (ktd gr) tr mem

    -- At a cycle leaf, replay the run at the ancestor it is `~` to.
    findRun anc (skip/cycle {X = X} eq _) (tr/step gr tr) (here px) =
      ⊥-elim (∉c→¬∈c (proj₁ (ancLu anc X) (~R→ eq gr)) px)

    findRun anc (skip/cycle {X = X} eq _) (tr/step gr tr) (there mem) =
      let A′ , grA , A′~G′  = ~R eq gr
          _ , tr′ , _       = tr-transport (~sym A′~G′) tr
          _ , _ , anc′ , d′ = proj₂ (ancLu anc X) grA
      in findRun anc′ d′ tr′ mem

    -- Descend along `skip/step`'s own step witness.  A `skip/cycle` at the
    -- bottom carries its own `P ∈T` run, which `findRun` follows.
    findMain/anc :
      ∀ {ξ}{Ξ : Vec Behav ξ}{G}
      → Anc Ξ
      → Leaf & Ξ ⊢skip P ◂ Pr ∶ G
      → Found

    findMain/anc anc (skip/main x) =
      _ , x

    findMain/anc anc (skip/step gr na ktd) =
      findMain/anc (anc/cons na ktd anc) (ktd gr)

    findMain/anc anc (skip/cycle eq inT) =
      let _ , _ , tr , mem = inT
      in findRun anc (skip/cycle eq inT) tr mem

    findMain :
      ∀ {G}
      → Leaf & [] ⊢skip P ◂ Pr ∶ G
      → Found

    findMain =
      findMain/anc anc/nil
