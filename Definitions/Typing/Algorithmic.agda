{-# OPTIONS --guardedness #-}

-- The *algorithmic* typing judgment: the normal form that the checker
-- decides, as opposed to `Declarative.agda`'s paper-style `_&_⊢p_∶_`.
--
-- The point (TODO.md §0) is that `t/skip` and `t/unskip` may wrap *any*
-- process, so every clause of a decision procedure over `_&_⊢p_∶_` has to
-- re-solve "could this have been derived by walking the graph instead?".
-- Here each of the two is confined to the one position it cannot be pushed
-- past:
--
--   * `t/unskip` survives only in front of `rec` and `v` — past an action
--     it is absorbed by `skip/advance`/`branch/before`, past `if` it
--     distributes, and in front of `∅` it dies by `skip/∈T-back`.  So it
--     appears as the trace of `a/rec` and inside `blocked/var`.
--   * `t/skip` survives only in front of an action or a `v` — hence
--     `a/skip` carries a `⊢skip` tree whose leaves are the blocked forms.
--     A zero-height tree (`skip/main`) is the ordinary "the action is
--     available right here" case.
--
-- A `v X` counts as an action here: jumping back to a recursion point is
-- just as much a step the process takes, and it is blocked by `t/skip` for
-- the same reason a send is.  So there is one leaf family, `_&_⊢blocked_∶_`,
-- with `blocked/send`, `blocked/recv` and `blocked/var` — not a separate variable
-- judgment.  (This also keeps `γ` inferable: a standalone variable family
-- indexed only by `Δ` leaves `γ` un-pinned.)
--
-- `t/skip` in front of a `v` really is necessary — see
-- `Tests/SkipBeforeVar.agda`: with `Δ = K ∷ []` and `s --β--> K`, `v zero`
-- types at `s` only by walking forward to `K`, and no trace-only form
-- exists because nothing reaches `s`.
--
-- This module is currently *additive*: `Declarative.agda`'s `⊢head` still
-- exists and `Safety/*` still uses it.  Retiring `⊢head` in favour of this
-- judgment is TODO.md Step 4.

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; []; _∷_) renaming (lookup to lu)
open import Function using (_∘_)
open import Relation.Nullary using (¬_)

open import Definitions.Typing
import Definitions.Typing.Properties as Props

module Definitions.Typing.Algorithmic
  {N : ℕ} {B : BTheory N} (wb : WellBehaved B) where

  open module M = MPST(wb)
  open M
  open Props wb using (td/bisim)

  private
    variable
      γ δ ξ : ℕ

  -- ══════════════════════════════════════════════════════════════════
  --  Leaves
  -- ══════════════════════════════════════════════════════════════════

  infix 4 _&_⊢a_∶_
  infix 4 _&_⊢blocked_∶_

  mutual

    -- The skip-blocked form of a communication: the action is available
    -- *at this very state*.
    data _&_⊢blocked_∶_ (Γ : Vec Sort γ) (Δ : Vec Behav δ)
       : NProc γ δ → Behav → Set where

      blocked/send :
        ∀ {P Q I}
          {i  : Fin (suc I)}
          {G G′ : Behav}
          {Pr : Proc γ δ}
          {E  : Exp γ}
          {S  : Sort}
        → G -< P ⟶ Q # i < S > >-> G′
        → Γ ⊢e E ∶ S
        → Γ & Δ ⊢a P ◂ Pr ∶ G′
        → Γ & Δ ⊢blocked P ◂ Q ! i < E >∙ Pr ∶ G

      -- The unskip-blocked form of a variable: the anchor reaches, up to
      -- `~`, the state we are at.  Oriented `reach`-then-`~` rather than
      -- `~`-then-`reach` (interchangeable by `skip/bisim-back`) because
      -- only this way is the *known* state on the left, so deciding it is
      -- one reachability fixed point from `lu Δ X` followed by a
      -- bisimilarity test against `G`.
      blocked/var :
        ∀ {P G H} {X : Fin δ}
        → lu Δ X -[¬ P ]->* H
        → H ~ G
        → Γ & Δ ⊢blocked P ◂ v X ∶ G

      blocked/recv :
        ∀ {P Q I}
          {i  : Fin (suc I)}
          {T  : Sort}
          {G G′ : Behav}
          {S  : Vec Sort (suc I)}
          {Br : Vec (Proc (suc γ) δ) (suc I)}
        → G -< P ⟶ Q # i < T > >-> G′
        → (∀ {j U G″}
            → G -< P ⟶ Q # j < U > >-> G″
            → (U ∷ Γ) & Δ ⊢a Q ◂ lu Br j ∶ G″)
        → Γ & Δ ⊢blocked Q ◂ Σ P ？[ S ]· Br ∶ G

      -- A `rec` blocks a skip too, because `t/unskip` does: the body is
      -- proved at its OWN anchor `W`, and `W` reaches this leaf.  Keeping
      -- it INSIDE the leaf family is what lets the several leaves of one
      -- skip tree carry DIFFERENT anchors.  With `rec` outside the tree
      -- (the old `a/rec`) a single common anchor is forced, and
      -- `Tests/PushRecDerivations.agda`'s `Ex6` is a `⊢p` derivation that
      -- no common anchor can reproduce — see `no-alg` there.
      blocked/rec :
        ∀ {P W L}
          {Pr : Proc γ (suc δ)}
        → W -[¬ P ]->* L
        → MessageGuarded Pr
        → Γ & (W ∷ Δ) ⊢a P ◂ Pr ∶ W
        → Γ & Δ ⊢blocked P ◂ rec Pr ∶ L

    data _&_⊢a_∶_ (Γ : Vec Sort γ) (Δ : Vec Behav δ)
       : NProc γ δ → Behav → Set where

      a/skip :
        ∀ {PPr G}
        → (Γ & Δ ⊢blocked_∶_) & [] ⊢skip PPr ∶ G
        → Γ & Δ ⊢a PPr ∶ G

      a/if :
        ∀ {P G}
          {E : Exp γ}
          {Pr Pr′ : Proc γ δ}
        → Γ ⊢e E ∶ s/bool
        → Γ & Δ ⊢a P ◂ Pr ∶ G
        → Γ & Δ ⊢a P ◂ Pr′ ∶ G
        → Γ & Δ ⊢a P ◂ ifp E then Pr else Pr′ ∶ G

      a/end :
        ∀ {P G}
        → ¬ P ∈T G
        → Γ & Δ ⊢a P ◂ ∅ ∶ G

  -- ══════════════════════════════════════════════════════════════════
  --  Soundness: every algorithmic derivation is a declarative one
  -- ══════════════════════════════════════════════════════════════════

  mutual

    alg/typing :
      ∀ {PPr G} {Γ : Vec Sort γ} {Δ : Vec Behav δ}
      → Γ & Δ ⊢a PPr ∶ G
      → Γ & Δ ⊢p PPr ∶ G
    alg/typing (a/skip std) = t/skip (blocked/skip std)
    alg/typing (a/if etd ttd ftd) =
      t/if etd (alg/typing ttd) (alg/typing ftd)
    alg/typing (a/end done) = t/end done

    blocked/skip :
      ∀ {PPr G} {Γ : Vec Sort γ} {Δ : Vec Behav δ} {Ξ : Vec Behav ξ}
      → (Γ & Δ ⊢blocked_∶_) & Ξ ⊢skip PPr ∶ G
      → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip PPr ∶ G
    blocked/skip (skip/main (blocked/send gr etd td)) =
      skip/main (t/send gr etd (alg/typing td))
    blocked/skip (skip/main (blocked/recv gr conts)) =
      skip/main (t/recv gr (λ gr′ → alg/typing (conts gr′)))
    blocked/skip (skip/main (blocked/var tr eq)) =
      skip/main (td/bisim ~ᵛ-refl eq (t/unskip tr (t/var ~refl)))
    blocked/skip (skip/main (blocked/rec tr guarded td)) =
      skip/main (t/unskip tr (t/rec guarded (alg/typing td)))
    blocked/skip (skip/step gr na ktd) =
      skip/step gr na (λ gr′ → blocked/skip (ktd gr′))
    blocked/skip (skip/cycle eq inT) = skip/cycle eq inT

  -- `⊢head` DELETED 2026-08-05.  It was the previous head-normal judgment,
  -- kept only because `Safety/*` was written against it; `Safety/*` is now
  -- stated over `_&_⊢a_∶_` throughout, so the whole family — `_⊢head_∶_`,
  -- `_&_⊢hskip_∶_`, `head/typing`, `hskip/typing` — went, together with
  -- `Definitions/Typing/Normalise.agda` (661 lines) that supported it.
