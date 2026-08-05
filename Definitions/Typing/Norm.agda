{-# OPTIONS --guardedness #-}

-- Hole-free since 2026-08-04, and in `runall.sh`'s ROOTS.
--
-- The normalisation `⊢p → ⊢a`:
--
--     norm : Γ & Δ ⊢p P ◂ Pr ∶ G → G -[¬ P ]->* G′ → Γ & Δ ⊢a P ◂ Pr ∶ G′
--
-- i.e. `Normalise.agda`'s `td/head`, generalised from `δ = 0` to arbitrary
-- `Δ` and re-targeted from `⊢head` (skip tree *beside* the action) to
-- `⊢a` (skip tree folded *into* the action, `Algorithmic.agda`).  The
-- trace parameter is the accumulated `t/unskip`: `t/unskip tr′ td`
-- recurses with `skip/cat tr′ tr`, which is why no separate
-- unskip-pushing pass is needed (TODO.md Step 2).
--
-- Everything cycle-related is inherited: `skip/unfold-cycle` and
-- `skip-leaf/bisim` in `Properties.agda` are already `Leaf`- *and*
-- `δ`-generic, so only their instantiations move here.

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; _++_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_; yes; no)

open import Definitions.Typing
import Definitions.Typing.Algorithmic as Alg

module Definitions.Typing.Norm
  {N : ℕ} {B : BTheory N} (wb : WellBehaved B) where

  open module M = MPST(wb)
  open M hiding (_,_)
  open import Definitions.Typing.Properties wb
  open Alg wb
    using (_&_⊢a_∶_; _&_⊢blocked_∶_; a/skip; a/if; a/end;
           blocked/send; blocked/recv; blocked/var; blocked/rec)

  private
    variable
      γ δ ξ ξ′ : ℕ

  -- ══════════════════════════════════════════════════════════════════
  --  Leaf-level bisimulation transport, at arbitrary `Δ`
  -- ══════════════════════════════════════════════════════════════════

  -- `Normalise.agda`'s `ptd/bisim`, without the `Δ = []` restriction:
  -- `td/bisim` was always `Δ`-general, only its instantiation was not.
  ptd/bisim :
    ∀ {G G′ PPr} {Γ : Vec Sort γ} {Δ : Vec Behav δ}
    → G ~ G′
    → Γ & Δ ⊢p PPr ∶ G
    → Γ & Δ ⊢p PPr ∶ G′
  ptd/bisim {PPr = P ◂ Pr} = td/bisim ~ᵛ-refl

  -- Cycle unfolding for `⊢p`-leaf trees at arbitrary `Δ`.
  pskip/unfold :
    ∀ {G H P Pr} {Γ : Vec Sort γ} {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ} {Ξ′ : Vec Behav ξ′}
    → Γ & Δ & Ξ′ ++ Ξ ⊢skip P ◂ Pr ∶ G
    → Γ & Δ & Ξ′ ++ (G ∷ Ξ) ⊢skip P ◂ Pr ∶ H
    → Γ & Δ & Ξ′ ++ Ξ ⊢skip P ◂ Pr ∶ H
  pskip/unfold {P = P} {Pr = Pr} =
    skip/unfold-cycle {PPr = P ◂ Pr} ptd/bisim

  pskip/unfold-top :
    ∀ {G H P Pr} {Γ : Vec Sort γ} {Δ : Vec Behav δ}
    → Γ & Δ & [] ⊢skip P ◂ Pr ∶ G
    → Γ & Δ & G ∷ [] ⊢skip P ◂ Pr ∶ H
    → Γ & Δ & [] ⊢skip P ◂ Pr ∶ H
  pskip/unfold-top base inner =
    pskip/unfold {Ξ = []} {Ξ′ = []} base inner

  -- ══════════════════════════════════════════════════════════════════
  --  `⊢a` is closed under bisimilarity
  -- ══════════════════════════════════════════════════════════════════
  --
  -- The `⊢head` analogue is `head/bisim`/`hskip/bisim`.  Here the action
  -- carries its own tree, so the mutual pair is `alg/bisim` (on `⊢a`) and
  -- `blocked/bisim` (on the leaf), with the tree transported by the generic
  -- `skip-leaf/bisim`.

  mutual

    alg/bisim :
      ∀ {G G′ PPr} {Γ : Vec Sort γ} {Δ Δ′ : Vec Behav δ}
      → Δ ~ᵛ Δ′
      → G ~ G′
      → Γ & Δ  ⊢a PPr ∶ G
      → Γ & Δ′ ⊢a PPr ∶ G′
    alg/bisim Δ~Δ′ G~G′ (a/skip std) =
      a/skip (blocked-tree/bisim Δ~Δ′ ~ᵛ-refl G~G′ std)
    alg/bisim Δ~Δ′ G~G′ (a/if etd ttd ftd) =
      a/if etd (alg/bisim Δ~Δ′ G~G′ ttd) (alg/bisim Δ~Δ′ G~G′ ftd)
    alg/bisim Δ~Δ′ G~G′ (a/end done) =
      a/end (done ∘ ∈~ (~sym G~G′))

    blocked/bisim :
      ∀ {G G′ PPr} {Γ : Vec Sort γ} {Δ Δ′ : Vec Behav δ}
      → Δ ~ᵛ Δ′
      → G ~ G′
      → Γ & Δ  ⊢blocked PPr ∶ G
      → Γ & Δ′ ⊢blocked PPr ∶ G′
    blocked/bisim Δ~Δ′ G~G′ (blocked/send gr etd td) =
      blocked/send (~L→ G~G′ gr) etd (alg/bisim Δ~Δ′ (~L→~ G~G′ gr) td)
    blocked/bisim Δ~Δ′ G~G′ (blocked/var {X = X} tr eq)
      with skip/bisim-back (lookup/~ᵛ Δ~Δ′ X ~refl) tr
    ... | _ , tr′ , H″~H =
      blocked/var tr′ (~trans H″~H (~trans eq G~G′))
    blocked/bisim Δ~Δ′ G~G′ (blocked/recv gr conts) =
      blocked/recv (~L→ G~G′ gr)
        (λ gr′ → alg/bisim Δ~Δ′ (~R→~ G~G′ gr′) (conts (~R→ G~G′ gr′)))
    -- The leaf state moves by `~`, so `skip/bisim` steps the anchor back
    -- to a bisimilar `W₀` and re-runs the trace from there.
    blocked/bisim Δ~Δ′ G~G′ (blocked/rec tr guarded body)
      with skip/bisim G~G′ tr
    ... | _ , W~W₀ , tr′ =
      blocked/rec tr′ guarded (alg/bisim (~ᵛ/∷ W~W₀ Δ~Δ′) W~W₀ body)

    -- `skip-leaf/bisim` cannot be reused here: it fixes one `Leaf`, and
    -- moving `Δ` changes the leaf family.  Same proof, one more index.
    blocked-tree/bisim :
      ∀ {G G′ PPr} {Γ : Vec Sort γ} {Δ Δ′ : Vec Behav δ}
        {Ξ Ξ′ : Vec Behav ξ}
      → Δ ~ᵛ Δ′
      → Ξ ~ᵛ Ξ′
      → G ~ G′
      → (Γ & Δ  ⊢blocked_∶_) & Ξ  ⊢skip PPr ∶ G
      → (Γ & Δ′ ⊢blocked_∶_) & Ξ′ ⊢skip PPr ∶ G′
    blocked-tree/bisim Δ~Δ′ _ G~G′ (skip/main l) =
      skip/main (blocked/bisim Δ~Δ′ G~G′ l)
    blocked-tree/bisim Δ~Δ′ Ξ~Ξ′ G~G′ (skip/step gr na ktd) =
      skip/step
        (~L→ G~G′ gr)
        (na ∘ ~R→ G~G′)
        (λ gr′ →
          blocked-tree/bisim
            Δ~Δ′
            (~ᵛ/∷ G~G′ Ξ~Ξ′)
            (~R→~ G~G′ gr′)
            (ktd (~R→ G~G′ gr′)))
    blocked-tree/bisim _ Ξ~Ξ′ G~G′ (skip/cycle eq inT) =
      skip/cycle (~trans (lookup/~ᵛ Ξ~Ξ′ _ eq) G~G′) (∈~ G~G′ inT)

  -- ══════════════════════════════════════════════════════════════════
  --  The normalisation
  -- ══════════════════════════════════════════════════════════════════

  -- ── ported from `Normalise.agda`, Δ-general and targeting `⊢a` ──

  LeafAlg :
    ∀ {γ δ ξ}
      {Γ : Vec Sort γ} {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
      {P : Part}
      {Pr : Proc γ δ}
      {G : Behav}
    → Γ & Δ & Ξ ⊢skip P ◂ Pr ∶ G
    → Set
  LeafAlg {Γ = Γ} {Δ = Δ} {P = P} {Pr = Pr} std =
    ∀ {H H′}
      {td : Γ & Δ ⊢p P ◂ Pr ∶ H}
    → MainLeaf td std
    → H -[¬ P ]->* H′
    → Γ & Δ ⊢a P ◂ Pr ∶ H′

  -- `LeafAlg`'s own analogue at the `remember`/`transport-leaf~`-wrapped
  -- level: `pskip/unfold`'s internal recursion (`unfold-skip-cycle`) stays
  -- at this wrapped level throughout, only ever transporting `base` via
  -- `weaken`, never re-`remember`ing it — so this is the shape that
  -- actually needs to be threaded through `leafAlg/unfold-cycle`'s own
  -- recursion below.
  LeafAlg-remember :
    ∀ {γ δ ξ}
      {Γ : Vec Sort γ} {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
      {P : Part}
      {Pr : Proc γ δ}
      {G : Behav}
    → ~Leaf (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ Pr ∶ G
    → Set
  LeafAlg-remember {Γ = Γ} {Δ = Δ} {P = P} {Pr = Pr} std =
    ∀ {H H′}
      {td : Γ & Δ ⊢p P ◂ Pr ∶ H}
    → MainLeaf td (skip/transport-leaf~ ptd/bisim std)
    → H -[¬ P ]->* H′
    → Γ & Δ ⊢a P ◂ Pr ∶ H′

  -- Converts a plain `LeafAlg std` to `LeafAlg-remember (remember std)`.
  -- This does *not* go through `ptd/bisim ~refl td ≡ td` (which doesn't
  -- hold propositionally — see the note on `leafAlg/bisim-remember`
  -- below): each case instead threads `tr` straight into `leafAlg`'s own,
  -- independently-matched `main/here`/`main/step` witness.
  leafAlg/remember :
    ∀ {γ ξ P Pr G}
      {Γ : Vec Sort γ} {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
    → (std : Γ & Δ & Ξ ⊢skip P ◂ Pr ∶ G)
    → LeafAlg std
    → LeafAlg-remember (skip/remember-leaves std)
  leafAlg/remember (skip/main td₀) leafAlg main/here tr =
    leafAlg main/here tr
  leafAlg/remember (skip/step gr na ktd) leafAlg (main/step gr′ leaf) tr =
    leafAlg/remember (ktd gr′) (leafAlg ∘ main/step gr′) leaf tr
  leafAlg/remember (skip/cycle eq inT) leafAlg ()

  -- Forward transport of a trace *from* `G′`: apply `tr-transport` at the
  -- flipped bisimulation and flip the resulting endpoint bisimulation back.

  mainLeaf/weaken-visited :
    ∀ {γ δ ξ ξ′ P Pr G H K}
      {Γ : Vec Sort γ} {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
      {td : Γ & Δ ⊢p P ◂ Pr ∶ K}
    → (std : Γ & Δ & Ξ′ ++ Ξ ⊢skip P ◂ Pr ∶ G)
    → MainLeaf td (skip/weaken-visited {H = H} {Ξ = Ξ} {Ξ′ = Ξ′} std)
    → MainLeaf td std
  mainLeaf/weaken-visited (skip/main td) main/here =
    main/here
  mainLeaf/weaken-visited (skip/step gr na ktd) (main/step gr′ leaf) =
    main/step gr′ (mainLeaf/weaken-visited (ktd gr′) leaf)
  mainLeaf/weaken-visited (skip/cycle _ _) ()

  leafAlg/bisim :
    ∀ {γ ξ P Pr G G′}
      {Γ : Vec Sort γ} {Δ : Vec Behav δ}
      {Ξ Ξ′ : Vec Behav ξ}
    → (Ξ~Ξ′ : Ξ ~ᵛ Ξ′)
    → (G~G′ : G ~ G′)
    → (std : Γ & Δ & Ξ ⊢skip P ◂ Pr ∶ G)
    → LeafAlg std
    → LeafAlg (skip-leaf/bisim ptd/bisim Ξ~Ξ′ G~G′ std)
  leafAlg/bisim Ξ~Ξ′ G~G′ (skip/main td) leafAlg main/here tr =
    let _ , tr′ , H~H′ = skip/bisim-back G~G′ tr
    in alg/bisim ~ᵛ-refl H~H′ (leafAlg main/here tr′)
  leafAlg/bisim Ξ~Ξ′ G~G′ (skip/step _ _ ktd)
    leafAlg (main/step gr′ leaf) tr =
    let gr″ = ~R→ G~G′ gr′
    in
    leafAlg/bisim
      (~ᵛ/∷ G~G′ Ξ~Ξ′)
      (~R→~ G~G′ gr′)
      (ktd gr″)
      (leafAlg ∘ main/step gr″)
      leaf
      tr
  leafAlg/bisim Ξ~Ξ′ G~G′ (skip/cycle eq inT) leafAlg ()

  -- `leafAlg/bisim`'s own analogue, but taking a `MainLeaf` witness at
  -- the `remember`/`transport-leaf~`-wrapped tree directly (`std` is
  -- already `~Leaf`-wrapped, matching `LeafAlg-remember`), instead of
  -- the plain `skip-leaf/bisim ptd/bisim` tree — needed because
  -- `pskip/unfold`'s own reduction goes through exactly this wrapped
  -- form, and no proposition relates it back to the plain tree at a
  -- *fixed* state without going through `~trans ~refl G~G′ ≡ G~G′`,
  -- which (`_~_` being built from the coinductive `_≲_`) doesn't hold
  -- propositionally in general. Threading `tr` straight through here
  -- (mirroring `leafAlg/bisim` case-for-case) sidesteps the issue
  -- entirely: `skip/bisim-back` works for *any* bisim proof, never
  -- needing it to be a specific one.
  leafAlg/bisim-remember :
    ∀ {γ ξ P Pr G G′}
      {Γ : Vec Sort γ} {Δ : Vec Behav δ}
      {Ξ Ξ′ : Vec Behav ξ}
    → (Ξ~Ξ′ : Ξ ~ᵛ Ξ′)
    → (G~G′ : G ~ G′)
    → (std : ~Leaf (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ Pr ∶ G)
    → LeafAlg-remember std
    → ∀ {H H′} {td : Γ & Δ ⊢p P ◂ Pr ∶ H}
    → MainLeaf td
        (skip/transport-leaf~ ptd/bisim
          (skip-leaf/bisim ~leaf/trans Ξ~Ξ′ G~G′ std))
    → H -[¬ P ]->* H′
    → Γ & Δ ⊢a P ◂ Pr ∶ H′
  leafAlg/bisim-remember Ξ~Ξ′ G~G′ (skip/main td₀) leafAlg main/here tr =
    let _ , tr′ , H~H′ = skip/bisim-back G~G′ tr
    in alg/bisim ~ᵛ-refl H~H′ (leafAlg main/here tr′)
  leafAlg/bisim-remember Ξ~Ξ′ G~G′ (skip/step _ _ ktd)
    leafAlg (main/step gr′ leaf) tr =
    let gr″ = ~R→ G~G′ gr′
    in
    leafAlg/bisim-remember
      (~ᵛ/∷ G~G′ Ξ~Ξ′)
      (~R→~ G~G′ gr′)
      (ktd gr″)
      (leafAlg ∘ main/step gr″)
      leaf
      tr
  leafAlg/bisim-remember Ξ~Ξ′ G~G′ (skip/cycle eq inT) leafAlg ()

  -- Ex-`skip/head`, and the one clause that is *not* a port: `⊢head`
  -- could keep the surviving tree (`h/skip`), `⊢a` cannot — it has to be
  -- folded into the action.  So this dispatches on the process:
  --
  --   * send/recv/`v`  → `a/skip`, grafting each leaf's own tree into the
  --                      surviving one (TODO.md Step 2's `graft`);
  --   * `∅`            → `a/end`, the tree eliminated via `P ∈T`  (5b);
  --   * `if`           → `a/if`, splitting the tree over the branches (5c);
  --   * `rec`          → `a/rec`, the open case                    (5e).
  --
  -- Only reached with `Ξ = []` (from `cancel/unskip-aux`, whose tree is
  -- the top-level one), which is what `a/skip` needs.
  -- `skip/weaken-visited` inserts one entry; grafting needs to lift a
  -- `Ξ = []` tree to an arbitrary `Ξ`, so iterate it.
  skip/weaken* :
    ∀ {G PPr} {Leaf : NProc γ δ → Behav → Set} (Ξ : Vec Behav ξ)
    → Leaf & [] ⊢skip PPr ∶ G
    → Leaf & Ξ ⊢skip PPr ∶ G
  skip/weaken* [] std = std
  skip/weaken* {Leaf = Leaf} (H ∷ Ξ) std =
    skip/weaken-visited {Leaf = Leaf} {Ξ = Ξ} {Ξ′ = []} (skip/weaken* Ξ std)

  -- The graft of TODO.md Step 2: a leaf of the surviving tree normalises
  -- to an `⊢a`, which for an action-headed process is itself `a/skip` of a
  -- tree — so a tree of trees, flattened by splicing each inner tree in
  -- where its leaf was.  `f` is the (process-directed) inversion saying
  -- "this `⊢a` must be `a/skip`".
  graft :
    ∀ {P Pr G} {Γ : Vec Sort γ} {Δ : Vec Behav δ} {Ξ : Vec Behav ξ}
    → (∀ {H} → Γ & Δ ⊢a P ◂ Pr ∶ H
             → (Γ & Δ ⊢blocked_∶_) & [] ⊢skip P ◂ Pr ∶ H)
    → (std : Γ & Δ & Ξ ⊢skip P ◂ Pr ∶ G)
    → LeafAlg std
    → (Γ & Δ ⊢blocked_∶_) & Ξ ⊢skip P ◂ Pr ∶ G
  graft f (skip/main td) leafAlg =
    skip/weaken* _ (f (leafAlg main/here skip/refl))
  graft f (skip/step gr na ktd) leafAlg =
    skip/step gr na (λ gr′ → graft f (ktd gr′) (leafAlg ∘ main/step gr′))
  graft _ (skip/cycle eq inT) _ = skip/cycle eq inT

  -- ══════════════════════════════════════════════════════════════════
  --  PUSH SKIP FORWARD
  -- ══════════════════════════════════════════════════════════════════
  --
  --     skip tree of ⊢a derivations  →  ⊢a derivation
  --
  -- Called AFTER the leaves have been recursively normalised to `⊢a`.

  -- Leaves already `⊢a`; for an action-headed process each is `a/skip` of
  -- a tree, so splice those in.  Structural, and `Ξ`-general.
  agraft :
    ∀ {P Pr G} {Γ : Vec Sort γ} {Δ : Vec Behav δ} {Ξ : Vec Behav ξ}
    → (∀ {H} → Γ & Δ ⊢a P ◂ Pr ∶ H
             → (Γ & Δ ⊢blocked_∶_) & [] ⊢skip P ◂ Pr ∶ H)
    → (Γ & Δ ⊢a_∶_) & Ξ ⊢skip P ◂ Pr ∶ G
    → (Γ & Δ ⊢blocked_∶_) & Ξ ⊢skip P ◂ Pr ∶ G
  agraft f (skip/main d) = skip/weaken* _ (f d)
  agraft f (skip/step gr na ktd) =
    skip/step gr na (λ gr′ → agraft f (ktd gr′))
  agraft _ (skip/cycle eq inT) = skip/cycle eq inT

  -- An `⊢blocked` tree over an `if` process has NO main leaves (`⊢blocked` has no
  -- `if` form), so it is all cycles — reshape it for either branch.
  blocked-if/true :
    ∀ {P E Pr₁ Pr₂ G} {Γ : Vec Sort γ} {Δ : Vec Behav δ} {Ξ : Vec Behav ξ}
    → (Γ & Δ ⊢blocked_∶_) & Ξ ⊢skip P ◂ ifp E then Pr₁ else Pr₂ ∶ G
    → (Γ & Δ ⊢a_∶_) & Ξ ⊢skip P ◂ Pr₁ ∶ G
  blocked-if/true (skip/main ())
  blocked-if/true (skip/step gr na ktd) =
    skip/step gr na (λ gr′ → blocked-if/true (ktd gr′))
  blocked-if/true (skip/cycle eq inT) = skip/cycle eq inT

  blocked-if/false :
    ∀ {P E Pr₁ Pr₂ G} {Γ : Vec Sort γ} {Δ : Vec Behav δ} {Ξ : Vec Behav ξ}
    → (Γ & Δ ⊢blocked_∶_) & Ξ ⊢skip P ◂ ifp E then Pr₁ else Pr₂ ∶ G
    → (Γ & Δ ⊢a_∶_) & Ξ ⊢skip P ◂ Pr₂ ∶ G
  blocked-if/false (skip/main ())
  blocked-if/false (skip/step gr na ktd) =
    skip/step gr na (λ gr′ → blocked-if/false (ktd gr′))
  blocked-if/false (skip/cycle eq inT) = skip/cycle eq inT

  -- Split an `if`-tree into its two branch trees.  Structural.
  aif/true :
    ∀ {P E Pr₁ Pr₂ G} {Γ : Vec Sort γ} {Δ : Vec Behav δ} {Ξ : Vec Behav ξ}
    → (Γ & Δ ⊢a_∶_) & Ξ ⊢skip P ◂ ifp E then Pr₁ else Pr₂ ∶ G
    → (Γ & Δ ⊢a_∶_) & Ξ ⊢skip P ◂ Pr₁ ∶ G
  aif/true (skip/main (a/if _ t _)) = skip/main t
  aif/true (skip/main (a/skip t)) = skip/weaken* _ (blocked-if/true t)
  aif/true (skip/step gr na ktd) = skip/step gr na (λ gr′ → aif/true (ktd gr′))
  aif/true (skip/cycle eq inT) = skip/cycle eq inT

  aif/false :
    ∀ {P E Pr₁ Pr₂ G} {Γ : Vec Sort γ} {Δ : Vec Behav δ} {Ξ : Vec Behav ξ}
    → (Γ & Δ ⊢a_∶_) & Ξ ⊢skip P ◂ ifp E then Pr₁ else Pr₂ ∶ G
    → (Γ & Δ ⊢a_∶_) & Ξ ⊢skip P ◂ Pr₂ ∶ G
  aif/false (skip/main (a/if _ _ f)) = skip/main f
  aif/false (skip/main (a/skip t)) = skip/weaken* _ (blocked-if/false t)
  aif/false (skip/step gr na ktd) = skip/step gr na (λ gr′ → aif/false (ktd gr′))
  aif/false (skip/cycle eq inT) = skip/cycle eq inT

  -- Cycle unfolding at the two leaf families, mirroring
  -- `pskip/unfold-top` for `⊢p`.  `skip/unfold-cycle` is `Leaf`-generic;
  -- the transport it wants is just the family's own bisimilarity lemma.
  askip/unfold-top :
    ∀ {G H P Pr} {Γ : Vec Sort γ} {Δ : Vec Behav δ}
    → (Γ & Δ ⊢a_∶_) & [] ⊢skip P ◂ Pr ∶ G
    → (Γ & Δ ⊢a_∶_) & (G ∷ []) ⊢skip P ◂ Pr ∶ H
    → (Γ & Δ ⊢a_∶_) & [] ⊢skip P ◂ Pr ∶ H
  askip/unfold-top {P = P} {Pr = Pr} =
    skip/unfold-cycle {PPr = P ◂ Pr} {Ξ = []} {Ξ′ = []} (alg/bisim ~ᵛ-refl)

  bskip/unfold-top :
    ∀ {G H P Pr} {Γ : Vec Sort γ} {Δ : Vec Behav δ}
    → (Γ & Δ ⊢blocked_∶_) & [] ⊢skip P ◂ Pr ∶ G
    → (Γ & Δ ⊢blocked_∶_) & (G ∷ []) ⊢skip P ◂ Pr ∶ H
    → (Γ & Δ ⊢blocked_∶_) & [] ⊢skip P ◂ Pr ∶ H
  bskip/unfold-top {P = P} {Pr = Pr} =
    skip/unfold-cycle {PPr = P ◂ Pr} {Ξ = []} {Ξ′ = []} (blocked/bisim ~ᵛ-refl)

  -- Every blocker is an `⊢a` in its own right (`a/skip` of a one-leaf
  -- tree), so a blocker tree is an `⊢a` tree.  Structural, and it keeps
  -- `Ξ` — used to make the `a/skip`-leaf case below descendable.
  blocked→alg :
    ∀ {PPr G} {Γ : Vec Sort γ} {Δ : Vec Behav δ} {Ξ : Vec Behav ξ}
    → (Γ & Δ ⊢blocked_∶_) & Ξ ⊢skip PPr ∶ G
    → (Γ & Δ ⊢a_∶_) & Ξ ⊢skip PPr ∶ G
  blocked→alg (skip/main l) = skip/main (a/skip (skip/main l))
  blocked→alg (skip/step gr na ktd) =
    skip/step gr na (λ gr′ → blocked→alg (ktd gr′))
  blocked→alg (skip/cycle eq inT) = skip/cycle eq inT

  -- The chase: consume the `P ∈T G` witness.  `na` forbids a P-action at
  -- every `skip/step`, so the witness cannot be exhausted inside the
  -- tree — it must reach a main leaf, which is where the `etd` is.
  mutual

    aif/chase :
      ∀ {P E Pr₁ Pr₂ G} {Γ : Vec Sort γ} {Δ : Vec Behav δ}
      → P ∈T G
      → (Γ & Δ ⊢a_∶_) & [] ⊢skip P ◂ ifp E then Pr₁ else Pr₂ ∶ G
      → Γ ⊢e E ∶ s/bool
    aif/chase _ (skip/main (a/if etd _ _)) = etd
    aif/chase inT (skip/main (a/skip t)) = bif/chase inT t
    aif/chase (_ , _ , tr/refl , ()) (skip/step _ _ _)
    aif/chase (_ , _ , tr/step gr₁ _ , here p) (skip/step _ na _) =
      ⊥-elim (∉c→¬∈c (na gr₁) p)
    aif/chase (_ , _ , tr/step gr₁ tr , there mem) std@(skip/step _ _ ktd) =
      aif/chase (_ , _ , tr , mem) (askip/unfold-top std (ktd gr₁))

    bif/chase :
      ∀ {P E Pr₁ Pr₂ G} {Γ : Vec Sort γ} {Δ : Vec Behav δ}
      → P ∈T G
      → (Γ & Δ ⊢blocked_∶_) & [] ⊢skip P ◂ ifp E then Pr₁ else Pr₂ ∶ G
      → Γ ⊢e E ∶ s/bool
    bif/chase _ (skip/main ())
    bif/chase (_ , _ , tr/refl , ()) (skip/step _ _ _)
    bif/chase (_ , _ , tr/step gr₁ _ , here p) (skip/step _ na _) =
      ⊥-elim (∉c→¬∈c (na gr₁) p)
    bif/chase (_ , _ , tr/step gr₁ tr , there mem) std@(skip/step _ _ ktd) =
      bif/chase (_ , _ , tr , mem) (bskip/unfold-top std (ktd gr₁))

  -- The `if`'s expression typing, read off any main leaf.  Same shape as
  -- `a∅/notin`: descend, and when the descent hits a `skip/cycle`, take
  -- the `P ∈T G` evidence it carries and CHASE it with cycle unfolding
  -- until a main leaf turns up.
  --
  -- Two arguments because the two jobs need different measures: the first
  -- is the tree we recurse on structurally (so `Ξ` grows and cycles are
  -- reachable — that is where the evidence comes from), the second is the
  -- same tree kept at `Ξ = []` by unfolding, which is what the chase
  -- needs.  Recursion is on the FIRST, so the second may grow freely.
  mutual

    aif/exp :
      ∀ {P E Pr₁ Pr₂ G} {Γ : Vec Sort γ} {Δ : Vec Behav δ} {Ξ : Vec Behav ξ}
      → (Γ & Δ ⊢a_∶_) & Ξ ⊢skip P ◂ ifp E then Pr₁ else Pr₂ ∶ G
      → (Γ & Δ ⊢a_∶_) & [] ⊢skip P ◂ ifp E then Pr₁ else Pr₂ ∶ G
      → Γ ⊢e E ∶ s/bool
    aif/exp (skip/main (a/if etd _ _)) _ = etd
    aif/exp (skip/main (a/skip t)) u = bif/exp t u
    aif/exp (skip/step _ _ _) (skip/main (a/if etd _ _)) = etd
    -- The twin is `a/skip` of a blocker tree.  It has no main leaf over
    -- an `if`, so re-present it as an `⊢a` tree and descend that instead.
    aif/exp (skip/step _ _ _) (skip/main (a/skip (skip/main ())))
    aif/exp (skip/step _ _ ktdm) (skip/main (a/skip t@(skip/step gr _ ktdt))) =
      aif/exp (ktdm gr) (askip/unfold-top (blocked→alg t) (blocked→alg (ktdt gr)))
    aif/exp (skip/step _ _ ktdm) u@(skip/step gr _ ktdu) =
      aif/exp (ktdm gr) (askip/unfold-top u (ktdu gr))
    aif/exp (skip/cycle _ inT) u = aif/chase inT u

    bif/exp :
      ∀ {P E Pr₁ Pr₂ G} {Γ : Vec Sort γ} {Δ : Vec Behav δ} {Ξ : Vec Behav ξ}
      → (Γ & Δ ⊢blocked_∶_) & Ξ ⊢skip P ◂ ifp E then Pr₁ else Pr₂ ∶ G
      → (Γ & Δ ⊢a_∶_) & [] ⊢skip P ◂ ifp E then Pr₁ else Pr₂ ∶ G
      → Γ ⊢e E ∶ s/bool
    bif/exp (skip/main ()) _
    bif/exp (skip/step _ _ _) (skip/main (a/if etd _ _)) = etd
    bif/exp (skip/step _ _ _) (skip/main (a/skip (skip/main ())))
    bif/exp (skip/step _ _ ktdm) (skip/main (a/skip t@(skip/step gr _ ktdt))) =
      bif/exp (ktdm gr) (askip/unfold-top (blocked→alg t) (blocked→alg (ktdt gr)))
    bif/exp (skip/step _ _ ktdm) u@(skip/step gr _ ktdu) =
      bif/exp (ktdm gr) (askip/unfold-top u (ktdu gr))
    bif/exp (skip/cycle _ inT) u = aif/chase inT u


  -- `∅`: chase the `P ∈T G` witness into the tree.  `na` kills a P-action
  -- at the root, a main leaf's `a/end` kills the rest, and at a
  -- `skip/step` we UNFOLD rather than descend — that keeps `Ξ = []`, so
  -- `skip/cycle` is impossible (its index is `Fin 0`) and no clause for
  -- it is needed.  The recursion is on the WITNESS, which loses one
  -- action per step, so unfolding growing the tree is harmless.
  mutual

    a∅/notin :
      ∀ {P G} {Γ : Vec Sort γ} {Δ : Vec Behav δ}
      → P ∈T G
      → (Γ & Δ ⊢a_∶_) & [] ⊢skip P ◂ ∅ ∶ G
      → ⊥
    a∅/notin inT (skip/main (a/end done)) = done inT
    a∅/notin inT (skip/main (a/skip t)) = b∅/notin inT t
    a∅/notin (_ , _ , tr/refl , ()) (skip/step _ _ _)
    a∅/notin (_ , _ , tr/step gr₁ _ , here p) (skip/step _ na _) =
      ∉c→¬∈c (na gr₁) p
    a∅/notin (_ , _ , tr/step gr₁ tr , there mem) std@(skip/step _ _ ktd) =
      a∅/notin (_ , _ , tr , mem) (askip/unfold-top std (ktd gr₁))

    -- Same chase one family down: `⊢blocked` has no `∅` form, so a main
    -- leaf here is absurd outright.
    b∅/notin :
      ∀ {P G} {Γ : Vec Sort γ} {Δ : Vec Behav δ}
      → P ∈T G
      → (Γ & Δ ⊢blocked_∶_) & [] ⊢skip P ◂ ∅ ∶ G
      → ⊥
    b∅/notin _ (skip/main ())
    b∅/notin (_ , _ , tr/refl , ()) (skip/step _ _ _)
    b∅/notin (_ , _ , tr/step gr₁ _ , here p) (skip/step _ na _) =
      ∉c→¬∈c (na gr₁) p
    b∅/notin (_ , _ , tr/step gr₁ tr , there mem) std@(skip/step _ _ ktd) =
      b∅/notin (_ , _ , tr , mem) (bskip/unfold-top std (ktd gr₁))

  -- Normalise every leaf in place, using the `LeafAlg` the caller
  -- already carries.  Structural.
  amap :
    ∀ {P Pr G} {Γ : Vec Sort γ} {Δ : Vec Behav δ} {Ξ : Vec Behav ξ}
    → (std : Γ & Δ & Ξ ⊢skip P ◂ Pr ∶ G)
    → LeafAlg std
    → (Γ & Δ ⊢a_∶_) & Ξ ⊢skip P ◂ Pr ∶ G
  amap (skip/main td) leafAlg = skip/main (leafAlg main/here skip/refl)
  amap (skip/step gr na ktd) leafAlg =
    skip/step gr na (λ gr′ → amap (ktd gr′) (leafAlg ∘ main/step gr′))
  amap (skip/cycle eq inT) _ = skip/cycle eq inT

  push :
    ∀ {P Pr G} {Γ : Vec Sort γ} {Δ : Vec Behav δ}
    → (Γ & Δ ⊢a_∶_) & [] ⊢skip P ◂ Pr ∶ G
    → Γ & Δ ⊢a P ◂ Pr ∶ G
  -- Blocked-headed: the tree folds into `a/skip`'s own tree.  `rec` is
  -- now one of these — that is the whole point of `blocked/rec`, and it
  -- is why this case no longer needs a common anchor.
  push {Pr = _ ! _ < _ >∙ _}  std = a/skip (agraft (λ { (a/skip t) → t }) std)
  push {Pr = Σ _ ？[ _ ]· _}  std = a/skip (agraft (λ { (a/skip t) → t }) std)
  push {Pr = v _}             std = a/skip (agraft (λ { (a/skip t) → t }) std)
  push {Pr = rec _}           std = a/skip (agraft (λ { (a/skip t) → t }) std)
  push {Pr = ∅}               std = a/end (λ inT → a∅/notin inT std)
  push {Pr = ifp _ then _ else _} std =
    a/if (aif/exp std std) (push (aif/true std)) (push (aif/false std))


  -- Ex-`skip/head`, and the one clause that is *not* a port: `⊢head`
  -- could keep the surviving tree (`h/skip`), `⊢a` cannot — it has to be
  -- folded into the action.  Dispatches on the process.
  a/tree :
    ∀ {P Pr G O} {Γ : Vec Sort γ} {Δ : Vec Behav δ}
    → O -[¬ P ]->* G                      -- the pre-cancellation root
    → (std : Γ & Δ & [] ⊢skip P ◂ Pr ∶ G)
    → LeafAlg std
    → Γ & Δ ⊢a P ◂ Pr ∶ G
  -- Normalise the leaves, then PUSH THE SKIP TREE FORWARD.
  a/tree _ std leafAlg = push (amap std leafAlg)

  -- `leafAlg/unfold`'s own recursion, restructured to stay entirely at
  -- the `remember`/`weaken`-wrapped level throughout: `base` is taken
  -- already `~Leaf`-wrapped, and each `skip/step` level only ever
  -- `weaken`s it further (never re-`remember`s), matching exactly what
  -- `unfold-skip-cycle` itself does internally. This is what lets `leaf`
  -- (the witness handed to us by the caller, sitting at exactly this
  -- wrapped shape) be threaded straight through the recursion, instead of
  -- being transported into a fresh, separately-computed witness — the
  -- latter is what got stuck earlier, since the fresh witness's own state
  -- sits behind an opaque `ktd gr′` application that Agda can't reduce to
  -- a concrete constructor, leaving its `Behav` index unresolved.
  leafAlg/unfold-cycle :
    ∀ {γ ξ ξ′ G H P Pr}
      {Γ : Vec Sort γ} {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → (base : ~Leaf (Γ & Δ ⊢p_∶_) & Ξ′ ++ Ξ ⊢skip P ◂ Pr ∶ G)
    → LeafAlg-remember base
    → (inner : Γ & Δ & Ξ′ ++ G ∷ Ξ ⊢skip P ◂ Pr ∶ H)
    → LeafAlg inner
    → LeafAlg-remember (unfold-skip-cycle {Ξ = Ξ} {Ξ′ = Ξ′} base (skip/remember-leaves inner))
  leafAlg/unfold-cycle base baseHead (skip/main td) innerHead main/here tr =
    innerHead main/here tr
  leafAlg/unfold-cycle {Ξ = Ξ} {Ξ′ = Ξ′}
    base baseHead
    (skip/step {G = H} gr na ktd)
    innerHead
    (main/step gr′ leaf)
    tr =
    let base′ = skip/weaken-visited {H = H} {Ξ = Ξ′ ++ Ξ} {Ξ′ = []} base
        base′Head : LeafAlg-remember base′
        base′Head =
          baseHead
            ∘ mainLeaf/weaken-visited (skip/transport-leaf~ ptd/bisim base)
            ∘ mainLeaf/transport-leaf~/weaken-visited ptd/bisim base
    in
    leafAlg/unfold-cycle
      {Ξ′ = H ∷ Ξ′}
      base′
      base′Head
      (ktd gr′)
      (innerHead ∘ main/step gr′)
      leaf
      tr
  leafAlg/unfold-cycle {Ξ = Ξ} {Ξ′ = Ξ′}
    base baseHead (skip/cycle {X = X} eq inT) innerHead leaf tr
    with lookup/insert {Ξ = Ξ} {Ξ′ = Ξ′} (X , eq)
  ... | inj₁ G~H =
    leafAlg/bisim-remember ~ᵛ-refl G~H base baseHead leaf tr
  ... | inj₂ (_ , eq′) with leaf
  ...   | ()

  leafAlg/unfold :
    ∀ {γ ξ ξ′ G H P Pr}
      {Γ : Vec Sort γ} {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → (base : Γ & Δ & Ξ′ ++ Ξ ⊢skip P ◂ Pr ∶ G)
    → LeafAlg base
    → (inner : Γ & Δ & Ξ′ ++ G ∷ Ξ ⊢skip P ◂ Pr ∶ H)
    → LeafAlg inner
    → LeafAlg (pskip/unfold {Ξ = Ξ} {Ξ′ = Ξ′} base inner)
  leafAlg/unfold {Ξ = Ξ} {Ξ′ = Ξ′} base baseHead inner innerHead =
    leafAlg/unfold-cycle {Ξ = Ξ} {Ξ′ = Ξ′}
      (skip/remember-leaves base)
      (leafAlg/remember base baseHead)
      inner
      innerHead

  leafAlg/unfold-top :
    ∀ {γ δ G H P Pr}
      {Γ : Vec Sort γ} {Δ : Vec Behav δ}
    → (base : Γ & Δ & [] ⊢skip P ◂ Pr ∶ G)
    → LeafAlg base
    → (inner : Γ & Δ & G ∷ [] ⊢skip P ◂ Pr ∶ H)
    → LeafAlg inner
    → LeafAlg (pskip/unfold-top base inner)
  leafAlg/unfold-top base baseHead inner innerHead =
    leafAlg/unfold {Ξ = []} {Ξ′ = []} base baseHead inner innerHead

  -- `-aux` takes the run and exclusion-witness as separate curried
  -- arguments (rather than re-packing them into a fresh tuple at the
  -- recursive call) so the termination checker sees a plain structural
  -- recursion on `_-[_]->_` alone — see `skip/advance`/`no-new-branch/skip`
  -- in `Definitions/Behav.agda` for the same fix.
  cancel/unskip-aux :
    ∀ {γ δ P Pr G G′ O αs}
      {Γ : Vec Sort γ} {Δ : Vec Behav δ}
    → O -[¬ P ]->* G                      -- accumulated: origin ⇝ here
    → G -[ αs ]-> G′
    → All (P ∉α_) αs
    → (std : Γ & Δ & [] ⊢skip P ◂ Pr ∶ G)
    → LeafAlg std
    → Γ & Δ ⊢a P ◂ Pr ∶ G′

  cancel/unskip-aux origin tr/refl [] (skip/main _) leafAlg =
    leafAlg main/here skip/refl
  cancel/unskip-aux origin tr/refl [] std@(skip/step _ _ _) leafAlg =
    a/tree origin std leafAlg
  cancel/unskip-aux origin (tr/step gr tr) allP (skip/main td) leafAlg =
    leafAlg main/here (_ , tr/step gr tr , allP)
  cancel/unskip-aux origin (tr/step gr tr) (P∉β ∷ allP) std@(skip/step _ _ ktd) leafAlg =
    let inner = ktd gr
        std′ = pskip/unfold-top std inner
        leafAlg′ =
          leafAlg/unfold-top std leafAlg
            inner
            (leafAlg ∘ main/step gr)
    in
    cancel/unskip-aux (skip/cat origin (skip/one gr P∉β)) tr allP std′ leafAlg′

  cancel/unskip :
    ∀ {γ δ P Pr G G′}
      {Γ : Vec Sort γ} {Δ : Vec Behav δ}
    → G -[¬ P ]->* G′
    → (std : Γ & Δ & [] ⊢skip P ◂ Pr ∶ G)
    → LeafAlg std
    → Γ & Δ ⊢a P ◂ Pr ∶ G′
  cancel/unskip (_ , tr , allP) =
    cancel/unskip-aux skip/refl tr allP


  mutual

    -- Every main leaf of a tree normalises: recurse to the leaf, then
    -- hand it to `norm` with whatever trace is left.
    mainLeaf/alg :
      ∀ {P Pr G} {Γ : Vec Sort γ} {Δ : Vec Behav δ} {Ξ : Vec Behav ξ}
      → (std : Γ & Δ & Ξ ⊢skip P ◂ Pr ∶ G)
      → LeafAlg std
    mainLeaf/alg (skip/main td) main/here tr = norm td tr
    mainLeaf/alg (skip/step _ _ ktd) (main/step gr′ leaf) =
      mainLeaf/alg (ktd gr′) leaf
    mainLeaf/alg (skip/cycle _ _) ()

    norm :
      ∀ {P Pr G G′} {Γ : Vec Sort γ} {Δ : Vec Behav δ}
      → Γ & Δ ⊢p P ◂ Pr ∶ G
      → G -[¬ P ]->* G′
      → Γ & Δ ⊢a P ◂ Pr ∶ G′

    -- The action survives the trace, and the continuation inherits the
    -- advanced one: a zero-height tree suffices.
    norm (t/send gr etd td) tr =
      let _ , gr′ , tr′ = skip/advance tr gr (∈S refl)
      in a/skip (skip/main (blocked/send gr′ etd (norm td tr′)))

    norm (t/recv gr conts) tr =
      let _ , gr′ , _ = skip/advance tr gr (∈R refl)
      in a/skip (skip/main
           (blocked/recv gr′
             (λ gr″ →
               let _ , gr₀ , tr₀ = branch/before tr gr gr″
               in norm (conts gr₀) tr₀)))

    -- The accumulated unskip *is* the trace parameter — this is why no
    -- separate unskip-pushing pass is needed (TODO.md Step 2).
    norm (t/unskip tr′ td) tr = norm td (skip/cat tr′ tr)

    norm (t/if etd ttd ftd) tr = a/if etd (norm ttd tr) (norm ftd tr)

    -- The trace is parked in the anchor; the body is normalised at its own
    -- state, where it is anchored.
    norm (t/rec guarded td) tr =
      a/skip (skip/main (blocked/rec tr guarded (norm td skip/refl)))

    -- `eq : lu Δ X ~ G` plus `tr : G ⇝ G′` is exactly `skip/bisim-back`'s
    -- input, and its output is exactly `blocked/var`'s premises.
    norm (t/var eq) tr with skip/bisim-back eq tr
    ... | _ , tr′ , H~G′ = a/skip (skip/main (blocked/var tr′ H~G′))

    norm (t/end done) tr = a/end (done ∘ skip/∈T-back tr)

    -- The one hard clause: walk `tr` into the tree (`cancel/unskip`), then
    -- dispatch on what survives.  TODO.md 5a/5b/5c/5e.
    -- Walk the accumulated trace into the tree; whatever survives is
    -- handed to `a/tree`.
    norm (t/skip std) tr = cancel/unskip tr std (mainLeaf/alg std)


  -- DELETED 2026-08-04: `reanchor` / `advance-anchor`.  They existed only
  -- to give `push`'s `rec` case one common anchor.  `blocked/rec` carries
  -- a per-leaf anchor, so no anchor ever has to move, and the whole
  -- family — together with its two open holes — is unnecessary.  It was
  -- also unprovable as stated: see `Stale/PushRecDerivations.agda.stale`
  -- (`Ex6`), which refutes the `W ⇝ L`/`G ⇝ L` span formulation.

  -- ══════════════════════════════════════════════════════════════════
  --  `if` inversion, natively
  -- ══════════════════════════════════════════════════════════════════
  --
  -- The `⊢head` analogue (`head/if/inv` in `Normalise.agda`) needs two
  -- mutual walkers plus a `P ∈T`-driven chase, because `h/skip` can sit
  -- over an `if` and its main leaf may itself be an `h/if`.  Here the
  -- leaves of an `a/skip` tree are `⊢blocked`, which has NO `if` form, so
  -- there is nothing to chase at this level: `blocked→alg` re-presents the
  -- tree with `⊢a` leaves and the three components come straight off the
  -- machinery `push` already uses.
  a/if/inv :
    ∀ {G P E Pr Pr′ Pr″} {Γ : Vec Sort γ} {Δ : Vec Behav δ}
    → Pr ≡ ifp E then Pr′ else Pr″
    → Γ & Δ ⊢a P ◂ Pr ∶ G
    → (Γ ⊢e E ∶ s/bool)
      × (Γ & Δ ⊢a P ◂ Pr′ ∶ G)
      × (Γ & Δ ⊢a P ◂ Pr″ ∶ G)
  a/if/inv refl (a/if etd ttd ftd) = etd , ttd , ftd
  a/if/inv refl (a/skip std) =
    let u = blocked→alg std
    in aif/exp u u , push (aif/true u) , push (aif/false u)

  -- ══════════════════════════════════════════════════════════════════
  --  `rec` guardedness, natively
  -- ══════════════════════════════════════════════════════════════════
  --
  -- `blocked/rec` carries `MessageGuarded Pr` as a field, so a main leaf
  -- hands it over directly.  The only difficulty is a tree that is all
  -- `skip/cycle`; that is what the `P ∈T` chase is for, exactly as in
  -- `bif/chase`/`b∅/notin`.

  -- Descend for a main leaf; if the descent bottoms out in cycles,
  -- surrender the `P ∈T` evidence they carry.
  brec/guarded :
    ∀ {P Pr G} {Γ : Vec Sort γ} {Δ : Vec Behav δ} {Ξ : Vec Behav ξ}
    → (Γ & Δ ⊢blocked_∶_) & Ξ ⊢skip P ◂ rec Pr ∶ G
    → MessageGuarded Pr ⊎ P ∈T G
  brec/guarded (skip/main (blocked/rec _ guarded _)) = inj₁ guarded
  brec/guarded (skip/step gr na ktd) with brec/guarded (ktd gr)
  ... | inj₁ guarded = inj₁ guarded
  ... | inj₂ inT     = inj₂ (in/later gr inT)
  brec/guarded (skip/cycle _ inT) = inj₂ inT

  -- The chase: consume the `P ∈T G` witness, unfolding cycles as we go.
  -- `na` forbids a P-action at every `skip/step`, so the witness cannot be
  -- exhausted inside the tree — it must reach a main leaf.
  brec/chase :
    ∀ {P Pr G} {Γ : Vec Sort γ} {Δ : Vec Behav δ}
    → P ∈T G
    → (Γ & Δ ⊢blocked_∶_) & [] ⊢skip P ◂ rec Pr ∶ G
    → MessageGuarded Pr
  brec/chase _ (skip/main (blocked/rec _ guarded _)) = guarded
  brec/chase (_ , _ , tr/refl , ()) (skip/step _ _ _)
  brec/chase (_ , _ , tr/step gr₁ _ , here p) (skip/step _ na _) =
    ⊥-elim (∉c→¬∈c (na gr₁) p)
  brec/chase (_ , _ , tr/step gr₁ tr , there mem) std@(skip/step _ _ ktd) =
    brec/chase (_ , _ , tr , mem) (bskip/unfold-top std (ktd gr₁))

  a/rec/guarded :
    ∀ {P Pr G} {Γ : Vec Sort γ} {Δ : Vec Behav δ}
    → Γ & Δ ⊢a P ◂ rec Pr ∶ G
    → MessageGuarded Pr
  a/rec/guarded (a/skip std) with brec/guarded std
  ... | inj₁ guarded = guarded
  ... | inj₂ inT     = brec/chase inT std
