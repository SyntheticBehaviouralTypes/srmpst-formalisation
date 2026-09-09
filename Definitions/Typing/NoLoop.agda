{-# OPTIONS --guardedness #-}

-- TODO.md §5.1 (D4): is `Loop P = Wait P ∅` empty?
--
-- `Loop P` is the set of states carrying a skip tree built ONLY from
-- `skip/step` and `skip/cycle` — i.e. a `⊢skip` derivation over the EMPTY
-- leaf family.  This file answers the question: yes, `Loop P = ∅`.
--
-- The argument, in one paragraph.  A leafless tree covers a set of states
-- that is (i) everywhere `P`-inactive and (ii) closed under stepping,
-- modulo `~`: `skip/step` covers *every* successor of its node (`ktd` is
-- universally quantified), and every `skip/cycle` leaf is `~` to an
-- ancestor, which is a `skip/step` node and so covered.  Hence no state in
-- that set can reach a `P`-action, i.e. `¬ P ∈T` everywhere on it.  But
-- `skip/cycle` *demands* `P ∈T` at its own node.  So a leafless tree has no
-- way to terminate, and being an inductive object it must.
--
-- Mechanically the two halves are `noLoop` and `loop/empty` below.  The
-- recursion in `noLoop` is structural on the `Any (P ∈α_) αs` witness — not
-- on the tree, which the `skip/cycle` jump walks back UP.  That works
-- because `P ∈T G` is an existential over a *run* (`Definitions/Behav.agda:73`)
-- and bisimulation transport (`tr-transport`, `:249`) keeps the label list
-- `αs` — and hence the `Any` witness — literally unchanged.
--
-- `Anc` is the invariant carried down the tree: every entry of the visited
-- vector `Ξ` is a `skip/step` node, so it is `P`-inactive and its `ktd`
-- covers all of its successors.  `Ξ` is exactly the ancestor list, so this
-- is a restatement of `skip/step`'s premises, one per ancestor.

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)

open import Data.Empty using (⊥)

open import Data.List.Relation.Unary.Any using (Any; here; there)

open import Relation.Nullary using (¬_)

open import Definitions.Typing

module Definitions.Typing.NoLoop {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  open module M = MPST(wb)
  open M

  private
    variable
      γ δ ξ : ℕ

  -- The empty leaf family: `Wait P ∅`.
  Empty : NProc γ δ → Behav → Set
  Empty _ _ = ⊥

  module _ {γ δ : ℕ}(P : Part)(Pr : Proc γ δ) where

    -- Every entry of the visited vector is a `skip/step` node.
    data Anc : ∀ {ξ} → Vec Behav ξ → Set where

      anc/nil : Anc []

      anc/cons :
        ∀ {ξ}{Ξ : Vec Behav ξ}{A}
        → (na : P not-active-in A)
        → (ktd :
            ∀ {A′ β}
            → (gr′ : A -< β >-> A′)
            → Empty & A ∷ Ξ ⊢skip P ◂ Pr ∶ A′)
        → Anc Ξ
        → Anc (A ∷ Ξ)

    -- Projection at an arbitrary ancestor.  The ancestor's own visited
    -- vector is a suffix of `Ξ`; it is existentially quantified here rather
    -- than computed as `drop X Ξ`, since nothing downstream needs to know
    -- which suffix it is.
    ancLu :
      ∀ {ξ}{Ξ : Vec Behav ξ}
      → Anc Ξ
      → (X : Fin ξ)
      → (P not-active-in lu Ξ X)
      × (∀ {A′ β}
         → lu Ξ X -< β >-> A′
         → ∃[ ζ ] Σ[ Ξ′ ∈ Vec Behav ζ ]
             Anc Ξ′ × (Empty & Ξ′ ⊢skip P ◂ Pr ∶ A′))

    ancLu (anc/cons na ktd anc) zero =
      na , λ gr′ → _ , _ , anc/cons na ktd anc , ktd gr′

    ancLu (anc/cons na ktd anc) (suc X) =
      ancLu anc X

    -- No state covered by a leafless tree can reach a `P`-action.  Stated
    -- over an explicit run so that the `Any` witness is available as the
    -- structurally decreasing argument.
    noLoop :
      ∀ {ξ}{Ξ : Vec Behav ξ}{G H αs}
      → Anc Ξ
      → Empty & Ξ ⊢skip P ◂ Pr ∶ G
      → G -[ αs ]-> H
      → Any (P ∈α_) αs
      → ⊥

    noLoop anc (skip/main ()) _ _

    noLoop anc (skip/step _ _ _) tr/refl ()

    noLoop anc (skip/cycle _ _) tr/refl ()

    -- The run's first action is `P`'s, but this node is `P`-inactive.
    noLoop anc (skip/step _ na _) (tr/step gr tr) (here px) =
      ∉c→¬∈c (na gr) px

    -- Descend: `ktd` covers this successor, and the node joins `Ξ`.
    noLoop anc (skip/step _ na ktd) (tr/step gr tr) (there mem) =
      noLoop (anc/cons na ktd anc) (ktd gr) tr mem

    -- At a cycle leaf, replay the run at the ancestor it is `~` to.  The
    -- ancestor is `P`-inactive, so its first step cannot be `P`'s either.
    noLoop anc (skip/cycle {X = X} eq _) (tr/step gr tr) (here px) =
      ∉c→¬∈c (proj₁ (ancLu anc X) (~R→ eq gr)) px

    -- Same jump, one step in: the ancestor's `ktd` hands back a leafless
    -- tree at the matching successor, and `tr-transport` moves the rest of
    -- the run there with `αs`, hence `mem`, untouched.
    noLoop anc (skip/cycle {X = X} eq _) (tr/step gr tr) (there mem) =
      let A′ , grA , A′~G′         = ~R eq gr
          _ , tr′ , _              = tr-transport (~sym A′~G′) tr
          _ , _ , anc′ , d′        = proj₂ (ancLu anc X) grA
      in noLoop anc′ d′ tr′ mem

    -- A leafless tree cannot exist.  Descend along `skip/step`'s own step
    -- witness — the tree is inductive, so this reaches a leaf, and every
    -- leaf is a `skip/cycle` whose `P ∈T` premise `noLoop` refutes.
    loop/empty :
      ∀ {ξ}{Ξ : Vec Behav ξ}{G}
      → Anc Ξ
      → Empty & Ξ ⊢skip P ◂ Pr ∶ G
      → ⊥

    loop/empty anc (skip/main ())

    loop/empty anc (skip/step gr na ktd) =
      loop/empty (anc/cons na ktd anc) (ktd gr)

    loop/empty anc (skip/cycle eq inT) =
      let _ , _ , tr , mem = inT
      in noLoop anc (skip/cycle eq inT) tr mem

  -- D4, as it is stated in TODO.md §5.1.
  Loop-empty :
    ∀ {P}{Pr : Proc γ δ}{G}
    → ¬ (Empty & [] ⊢skip P ◂ Pr ∶ G)
  Loop-empty {P = P}{Pr = Pr} =
    loop/empty P Pr anc/nil
