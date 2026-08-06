{-# OPTIONS --guardedness #-}

-- Projection for `∥`: typing a participant against a parallel composition
-- reduces to typing it against the side it acts in, so the product state
-- space is never traversed.
--
-- This is the lemma the net-native checker (TODO.md) is built on.  The
-- side condition is `PFree P n₂` — P takes no part in ANY action of `n₂`
-- — which is NOT implied by the receiver-`Disjoint` that `WBNet`'s `∥`
-- already demands, and is checked per participant.
--
-- Both theories appear at once, so both `Algorithmic` instantiations are
-- opened under aliases.  `WBNet (n₁ ∥ n₂)` contains `WBNet n₁`, so a
-- caller always has both witnesses; they are taken as parameters here to
-- keep this module independent of `Check/Network.agda`.

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Vec using (Vec; map; lookup) renaming ([] to v[])
open import Data.Vec.Properties using (lookup-map)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; subst₂)

open import Definitions.Behav using (BTheory; WellBehaved)
import Definitions.Typing as Typing
import Definitions.Typing.Algorithmic as Alg

module Definitions.Graph.NetworkProject (N : ℕ) where

  open import Definitions.Actions N
  open import Definitions.Common N using (Part)
  open import Definitions.Proc N using (Proc; _◂_)
  open import Definitions.Expr using (Sort)
  open import Definitions.Graph.Network N
  open import Definitions.Graph.NetworkWB N
    using (PFree; Disjoint; pfree⇒na; module ParWB)
  open import Definitions.Proc N using (NProc)

  -- ══════════════════════════════════════════════════════════════════
  --  Projecting a product state onto its left component
  -- ══════════════════════════════════════════════════════════════════
  --
  -- Total: when `n₁` has already ended the product state carries only an
  -- `n₂` component, and the projection is `nend`.

  projL : ∀ {n₁ n₂} → NState (n₁ ∥ n₂) → NState n₁
  projL (live (inj₂ (a , _))) = live a
  projL (live (inj₁ _))       = nend
  projL nend                  = nend

  projR : ∀ {n₁ n₂} → NState (n₁ ∥ n₂) → NState n₂
  projR (live (inj₂ (_ , b))) = b
  projR (live (inj₁ b))       = live b
  projR nend                  = nend

  projL-mkPair :
    ∀ {n₁ n₂} (a : NState n₁) (b : NState n₂)
    → projL (mkPair a b) ≡ a
  projL-mkPair (live _) _        = refl
  projL-mkPair nend     (live _) = refl
  projL-mkPair nend     nend     = refl

  projR-mkPair :
    ∀ {n₁ n₂} (a : NState n₁) (b : NState n₂)
    → projR (mkPair a b) ≡ b
  projR-mkPair (live _) _        = refl
  projR-mkPair nend     (live _) = refl
  projR-mkPair nend     nend     = refl

  -- THE BRIDGE.  `mkPair` is surjective on product states, so any `s` can
  -- be rewritten as `mkPair (projL s) (projR s)` — which is what unlocks
  -- the existing machinery in `Network.agda` / `NetworkWB.agda`
  -- (`stepL`, `stepR`, `pstep-inv`, `~-projL`, `~-projR`, `~-pair`), all
  -- of which is stated in `mkPair` form.
  mkPair-proj :
    ∀ {n₁ n₂} (s : NState (n₁ ∥ n₂))
    → mkPair (projL s) (projR s) ≡ s
  mkPair-proj (live (inj₂ (_ , _))) = refl
  mkPair-proj (live (inj₁ _))       = refl
  mkPair-proj nend                  = refl

  -- ══════════════════════════════════════════════════════════════════
  --  Steps, traces and participation across the product
  -- ══════════════════════════════════════════════════════════════════

  module Traces (n₁ n₂ : Net) where

    private
      module T∥ = BTheory (netTheory (n₁ ∥ n₂))
      module T₁ = BTheory (netTheory n₁)

    -- Inversion in PROJECTED form.  `pstep-inv` is stated at a state of
    -- the shape `mkPair a b`; every product state IS of that shape
    -- (`mkPair-proj`), but coercing `s` into it at each use site is
    -- unusable.  Splitting on `s` ONCE here makes the `mkPair` form hold
    -- definitionally, and the result is phrased purely in `projL`/`projR`
    -- — which is what everything downstream consumes.
    pstep-invP :
      ∀ {s α t}
      → NStep (n₁ ∥ n₂) s α t
      → (NStep n₁ (projL s) α (projL t) × projR t ≡ projR s)
      ⊎ (NStep n₂ (projR s) α (projR t) × projL t ≡ projL s)
    pstep-invP {live (inj₂ (a , b))} st
      with pstep-inv n₁ n₂ {a = live a} {b = b} st
    ... | inj₁ (a′ , st₁ , refl)
      rewrite projL-mkPair a′ b | projR-mkPair a′ b = inj₁ (st₁ , refl)
    ... | inj₂ (b′ , st₂ , refl) = inj₂ (st₂ , refl)
    pstep-invP {live (inj₁ b)} st
      with pstep-inv n₁ n₂ {a = nend} {b = live b} st
    ... | inj₁ (_ , () , _)
    ... | inj₂ (b′ , st₂ , refl)
      rewrite projL-mkPair {n₁} {n₂} nend b′ | projR-mkPair {n₁} {n₂} nend b′ =
      inj₂ (st₂ , refl)
    pstep-invP {nend} ()

    -- An `n₁`-step out of the projection is a product step, at `s` itself.
    stepLP :
      ∀ {s α a′}
      → NStep n₁ (projL s) α a′
      → NStep (n₁ ∥ n₂) s α (mkPair a′ (projR s))
    stepLP {s} {α} {a′} st =
      subst (λ z → NStep (n₁ ∥ n₂) z α (mkPair a′ (projR s)))
        (mkPair-proj s) (stepL (projR s) st)

    -- A `¬P` run of the product projects to a `¬P` run of `n₁`: the
    -- `n₁`-steps are kept, the `n₂`-steps do not move the `n₁` component.
    skip-projL-aux :
      ∀ {P : Part} {w t αs}
      → T∥._-[_]->_ w αs t
      → All (P ∉α_) αs
      → T₁._-[¬_]->*_ (projL w) P (projL t)
    skip-projL-aux T∥.tr/refl [] = T₁.skip/refl
    skip-projL-aux {P = P} {t = t} (T∥.tr/step st tr) (P∉α ∷ allP)
      with pstep-invP st
    ... | inj₁ (st₁ , _) = T₁.tr¬/step st₁ P∉α (skip-projL-aux tr allP)
    ... | inj₂ (_ , eq) =
      subst (λ z → T₁._-[¬_]->*_ z P (projL t)) eq (skip-projL-aux tr allP)

    skip-projL :
      ∀ {P : Part} {w t}
      → T∥._-[¬_]->*_ w P t
      → T₁._-[¬_]->*_ (projL w) P (projL t)
    skip-projL (_ , tr , allP) = skip-projL-aux tr allP

    -- Participation lifts along `stepL`, unconditionally.
    private
      liftTr :
        ∀ {a a′ αs} (b : NState n₂)
        → T₁._-[_]->_ a αs a′
        → T∥._-[_]->_ (mkPair a b) αs (mkPair a′ b)
      liftTr b T₁.tr/refl = T∥.tr/refl
      liftTr b (T₁.tr/step st tr) = T∥.tr/step (stepL b st) (liftTr b tr)

    inT-lift :
      ∀ {P : Part} (w : NState (n₁ ∥ n₂))
      → T₁._∈T_ P (projL w)
      → T∥._∈T_ P w
    inT-lift w (αs , a′ , tr , mem) =
      αs , mkPair a′ (projR w) ,
      subst (λ z → T∥._-[_]->_ z αs (mkPair a′ (projR w)))
        (mkPair-proj w) (liftTr (projR w) tr) ,
      mem

    -- …and comes back, provided `P` takes no part in `n₂`: the action
    -- witnessing participation cannot be one of `n₂`'s.
    inT-projL-aux :
      ∀ {P : Part} {w t αs}
      → PFree P n₂
      → T∥._-[_]->_ w αs t
      → Any (P ∈α_) αs
      → T₁._∈T_ P (projL w)
    inT-projL-aux pf (T∥.tr/step st tr) (here px) with pstep-invP st
    ... | inj₁ (st₁ , _) = T₁.in/α st₁ px
    ... | inj₂ (st₂ , _) = ⊥-elim (∉c→¬∈c (pfree⇒na pf st₂) px)
    inT-projL-aux {P = P} pf (T∥.tr/step st tr) (there mem)
      with pstep-invP st
    ... | inj₁ (st₁ , _) = T₁.in/later st₁ (inT-projL-aux pf tr mem)
    ... | inj₂ (_ , eq) =
      subst (λ z → T₁._∈T_ P z) eq (inT-projL-aux pf tr mem)

    inT-projL :
      ∀ {P : Part} {w}
      → PFree P n₂
      → T∥._∈T_ P w
      → T₁._∈T_ P (projL w)
    inT-projL pf (_ , _ , tr , mem) = inT-projL-aux pf tr mem

    -- ── stuckness of the `n₁` component ──

    Stuck : NState n₁ → Set
    Stuck a = ∀ {α a′} → ¬ NStep n₁ a α a′

    nostep : ∀ {a} → nedges n₁ a ≡ [] → Stuck a
    nostep {a} eq {α} {a′} st
      with subst (λ l → (α , a′) ∈ l) eq (nstep⇒listed n₁ st)
    ... | ()

    headStep :
      ∀ {a α a′ rest}
      → nedges n₁ a ≡ (α , a′) ∷ rest
      → NStep n₁ a α a′
    headStep {a} {α} {a′} eq =
      nlisted⇒step n₁ (subst (λ l → (α , a′) ∈ l) (sym eq) (here refl))

    -- Nobody participates in a state with no outgoing edges.
    stuck⇒∉T :
      ∀ {P : Part} {a}
      → Stuck a
      → ¬ T₁._∈T_ P a
    stuck⇒∉T stk (_ , _ , T₁.tr/refl , ())
    stuck⇒∉T stk (_ , _ , T₁.tr/step st _ , _) = ⊥-elim (stk st)

  -- ══════════════════════════════════════════════════════════════════
  --  The statement
  -- ══════════════════════════════════════════════════════════════════

  module Statement
    (n₁ n₂ : Net)
    (dis   : Disjoint n₁ n₂)
    (wb₁   : WellBehaved (netTheory n₁))
    (wb₂   : WellBehaved (netTheory n₂))
    (wb₁₂  : WellBehaved (netTheory (n₁ ∥ n₂)))
    where

    private
      module A₁  = Alg wb₁
      module A₁₂ = Alg wb₁₂
      -- `Alg` does not re-export `MPST`, and `MessageGuarded`/`⊢skip`
      -- live there, so both instances are needed under their own names.
      module M₁  = Typing.MPST wb₁
      module M₁₂ = Typing.MPST wb₁₂
      module PW  = ParWB n₁ n₂ wb₁ wb₂ dis
      module T∥  = BTheory (netTheory (n₁ ∥ n₂))
      module T₁  = BTheory (netTheory n₁)

    open Traces n₁ n₂

    -- Typing `P` at a component state, and at the corresponding product
    -- state, are the same problem.  `Δ = []`: that is what the checker
    -- calls it at, and the general form needs a relation between the two
    -- `Δ`s (see the note below).

    -- `_&_⊢a_∶_` is mixfix, so a qualified use has to be written in
    -- application form.
    At₁ :
      ∀ {γ δ} → Vec Sort γ → Vec (NState n₁) δ
      → NProc γ δ → NState n₁ → Set
    At₁ Γ Δ PPr a = A₁._&_⊢a_∶_ Γ Δ PPr a

    At₁₂ :
      ∀ {γ δ} → Vec Sort γ → Vec (NState (n₁ ∥ n₂)) δ
      → NProc γ δ → NState (n₁ ∥ n₂) → Set
    At₁₂ Γ Δ PPr s = A₁₂._&_⊢a_∶_ Γ Δ PPr s

    Bl₁ :
      ∀ {γ δ} → Vec Sort γ → Vec (NState n₁) δ
      → NProc γ δ → NState n₁ → Set
    Bl₁ Γ Δ PPr a = A₁._&_⊢blocked_∶_ Γ Δ PPr a

    Bl₁₂ :
      ∀ {γ δ} → Vec Sort γ → Vec (NState (n₁ ∥ n₂)) δ
      → NProc γ δ → NState (n₁ ∥ n₂) → Set
    Bl₁₂ Γ Δ PPr s = A₁₂._&_⊢blocked_∶_ Γ Δ PPr s

    Sk₁ :
      ∀ {γ δ ξ} → Vec Sort γ → Vec (NState n₁) δ → Vec (NState n₁) ξ
      → NProc γ δ → NState n₁ → Set
    Sk₁ Γ Δ Ξ PPr a = M₁._&_⊢skip_∶_ (Bl₁ Γ Δ) Ξ PPr a

    Sk₁₂ :
      ∀ {γ δ ξ}
      → Vec Sort γ → Vec (NState (n₁ ∥ n₂)) δ → Vec (NState (n₁ ∥ n₂)) ξ
      → NProc γ δ → NState (n₁ ∥ n₂) → Set
    Sk₁₂ Γ Δ Ξ PPr s = M₁₂._&_⊢skip_∶_ (Bl₁₂ Γ Δ) Ξ PPr s

    private
      -- `~-projL` is stated at `mkPair`s; `mkPair-proj` puts both sides
      -- into that shape.  (It needs only `dis`, not `wb₁`/`wb₂` — those
      -- are `ParWB`'s parameters, not this lemma's.)
      ~-projLP :
        ∀ {u w} → T∥._~_ u w → T₁._~_ (projL u) (projL w)
      ~-projLP {u} {w} pr =
        PW.~-projL
          {a₁ = projL u} {b₁ = projR u} {a₂ = projL w} {b₂ = projR w}
          (subst₂ T∥._~_ (sym (mkPair-proj u)) (sym (mkPair-proj w)) pr)

      -- `MessageGuarded` says nothing about the behaviour, but it is
      -- declared inside `MPST`, so the two instances are distinct types.
      mg-proj :
        ∀ {γ δ} {Pr : Proc γ δ}
        → M₁₂.MessageGuarded Pr → M₁.MessageGuarded Pr
      mg-proj M₁₂.mg/send     = M₁.mg/send
      mg-proj M₁₂.mg/recv     = M₁.mg/recv
      mg-proj (M₁₂.mg/if g h) = M₁.mg/if (mg-proj g) (mg-proj h)

    -- Indexing by `mkPair a b` is the wrong shape: it forces the `n₂`
    -- component to be a fixed `b`, and it is not — `blocked/rec`'s anchor
    -- is reached by a mixed trace and can sit at a DIFFERENT `n₂` state.
    -- The right primitive is the projection, which is total and makes the
    -- `Δ` relation just `map projL`.
    ProjectStmt : Set
    ProjectStmt =
      ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (NState (n₁ ∥ n₂)) δ}
        {P Pr s}
      → PFree P n₂
      → At₁₂ Γ Δ (P ◂ Pr) s
      → At₁ Γ (map projL Δ) (P ◂ Pr) (projL s)

    LiftStmt : Set
    LiftStmt =
      ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (NState (n₁ ∥ n₂)) δ}
        {P Pr s}
      → PFree P n₂
      → At₁ Γ (map projL Δ) (P ◂ Pr) (projL s)
      → At₁₂ Γ Δ (P ◂ Pr) s

    -- ════════════════════════════════════════════════════════════════
    --  Projection
    -- ════════════════════════════════════════════════════════════════
    --
    -- Four mutually recursive functions, all structural on the
    -- derivation.  `stuckWalk` is the extra one: see `projSkip`'s
    -- `skip/step` case.

    mutual

      projA :
        ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (NState (n₁ ∥ n₂)) δ}
          {P : Part} {Pr : Proc γ δ} {s}
        → PFree P n₂
        → At₁₂ Γ Δ (P ◂ Pr) s
        → At₁ Γ (map projL Δ) (P ◂ Pr) (projL s)
      projA pf (A₁₂.a/skip std) = A₁.a/skip (projSkip pf std)
      projA pf (A₁₂.a/if etd ttd ftd) =
        A₁.a/if etd (projA pf ttd) (projA pf ftd)
      projA {s = s} pf (A₁₂.a/end done) =
        A₁.a/end (λ inT → done (inT-lift s inT))

      projSkip :
        ∀ {γ δ ξ} {Γ : Vec Sort γ} {Δ : Vec (NState (n₁ ∥ n₂)) δ}
          {Ξ : Vec (NState (n₁ ∥ n₂)) ξ} {P : Part} {Pr : Proc γ δ} {s}
        → PFree P n₂
        → Sk₁₂ Γ Δ Ξ (P ◂ Pr) s
        → Sk₁ Γ (map projL Δ) (map projL Ξ) (P ◂ Pr) (projL s)
      projSkip pf (M₁₂.skip/main leaf) = M₁.skip/main (projBl pf leaf)

      -- `skip/step` needs an `n₁`-step out of `projL s`, and the
      -- product's step may well be an `n₂` one.  So split on whether
      -- `n₁` has any edge here at all.
      projSkip {Γ = Γ} {Δ = Δ} {P = P} {Pr = Pr} {s = s}
               pf (M₁₂.skip/step gr na ktd)
        with nedges n₁ (projL s) in eq

      -- `n₁` can move: keep the tree, re-index it.  Any `n₁`-step out of
      -- `projL s` lifts to a product step out of `s` (`stepLP`), so the
      -- product's `ktd` covers every branch the projected one needs.
      ... | (α₁ , a₁) ∷ rest =
        M₁.skip/step (headStep eq)
          (λ st₁ → na (stepLP st₁))
          (λ {a″} st₁ →
             subst (λ z → Sk₁ Γ (map projL Δ) _ (P ◂ Pr) z)
               (projL-mkPair a″ (projR s))
               (projSkip pf (ktd (stepLP st₁))))

      -- `n₁` is stuck — and STAYS stuck, since `n₂`-steps leave the `n₁`
      -- component alone.  So the product tree can only be walking `n₂`
      -- edges, and the answer is whatever leaf it reaches, projected.
      ... | [] with pstep-invP gr
      ...   | inj₁ (st₁ , _) = ⊥-elim (nostep eq st₁)
      ...   | inj₂ (_ , eqL) =
        M₁.skip/main
          (subst (λ z → Bl₁ Γ (map projL Δ) (P ◂ Pr) z) eqL
            (stuckWalk pf
              (λ st → nostep eq (subst (λ z → NStep n₁ z _ _) eqL st))
              (ktd gr)))

      projSkip {Ξ = Ξ} {P = P} {s = s} pf (M₁₂.skip/cycle {X = X} bis inT) =
        M₁.skip/cycle
          (subst (λ z → T₁._~_ z (projL s))
            (sym (lookup-map X projL Ξ)) (~-projLP bis))
          (inT-projL pf inT)

      -- Walk down a skip tree whose `n₁` component cannot move, to the
      -- leaf it must end at.  Split out of `projSkip` rather than called
      -- on the whole tree, so the recursion stays structural.
      stuckWalk :
        ∀ {γ δ ξ} {Γ : Vec Sort γ} {Δ : Vec (NState (n₁ ∥ n₂)) δ}
          {Ξ : Vec (NState (n₁ ∥ n₂)) ξ} {P : Part} {Pr : Proc γ δ} {s}
        → PFree P n₂
        → Stuck (projL s)
        → Sk₁₂ Γ Δ Ξ (P ◂ Pr) s
        → Bl₁ Γ (map projL Δ) (P ◂ Pr) (projL s)
      stuckWalk pf stk (M₁₂.skip/main leaf) = projBl pf leaf
      stuckWalk {Γ = Γ} {Δ = Δ} {P = P} {Pr = Pr}
                pf stk (M₁₂.skip/step gr na ktd)
        with pstep-invP gr
      ... | inj₁ (st₁ , _) = ⊥-elim (stk st₁)
      ... | inj₂ (_ , eqL) =
        subst (λ z → Bl₁ Γ (map projL Δ) (P ◂ Pr) z) eqL
          (stuckWalk pf
            (λ st → stk (subst (λ z → NStep n₁ z _ _) eqL st))
            (ktd gr))
      -- `skip/cycle` demands `P ∈T s`, which would project to `P ∈T` a
      -- state with no outgoing edges.
      stuckWalk pf stk (M₁₂.skip/cycle bis inT) =
        ⊥-elim (stuck⇒∉T stk (inT-projL pf inT))

      projBl :
        ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (NState (n₁ ∥ n₂)) δ}
          {P : Part} {Pr : Proc γ δ} {s}
        → PFree P n₂
        → Bl₁₂ Γ Δ (P ◂ Pr) s
        → Bl₁ Γ (map projL Δ) (P ◂ Pr) (projL s)

      -- The action mentions `P`, so it cannot be one of `n₂`'s: the
      -- `inj₂` branch is absurd, and the `inj₁` branch IS the projected
      -- step.  This is exactly what `PFree` buys.
      projBl pf (A₁₂.blocked/send gr etd td) with pstep-invP gr
      ... | inj₁ (st₁ , _) = A₁.blocked/send st₁ etd (projA pf td)
      ... | inj₂ (st₂ , _) =
        ⊥-elim (∉c→¬∈c (pfree⇒na pf st₂) (∈S refl))

      projBl {s = s} pf (A₁₂.blocked/recv gr conts) with pstep-invP gr
      ... | inj₁ (st₁ , _) =
        A₁.blocked/recv st₁
          (λ {_} {_} {a″} st′ →
             subst (λ z → At₁ _ (map projL _) _ z)
               (projL-mkPair a″ (projR s))
               (projA pf (conts (stepLP st′))))
      ... | inj₂ (st₂ , _) =
        ⊥-elim (∉c→¬∈c (pfree⇒na pf st₂) (∈R refl))

      projBl {Δ = Δ} {P = P} pf (A₁₂.blocked/var {H = H} {X = X} tr bis) =
        A₁.blocked/var
          (subst (λ z → T₁._-[¬_]->*_ z P (projL H))
            (sym (lookup-map X projL Δ)) (skip-projL tr))
          (~-projLP bis)

      projBl pf (A₁₂.blocked/rec tr guarded td) =
        A₁.blocked/rec (skip-projL tr) (mg-proj guarded) (projA pf td)

    project : ProjectStmt
    project = projA

  -- ══════════════════════════════════════════════════════════════════
  --  Proving `ProjectStmt` — worked-out case analysis
  -- ══════════════════════════════════════════════════════════════════
  --
  -- Three mutually recursive functions mirroring the judgment:
  --   projA    : ⊢a       at s  →  ⊢a       at projL s
  --   projSkip : ⊢skip    at s  →  ⊢skip    at projL s   (Ξ ↦ map projL Ξ)
  --   projBl   : ⊢blocked at s  →  ⊢blocked at projL s
  --
  -- Every case below is discharged by lemmas that now EXIST; only
  -- `skip/step` needs new work.  `mkPair-proj` rewrites `s` into the
  -- `mkPair` shape the `Network*.agda` lemmas expect.
  --
  --   a/if          congruence.
  --   a/end         `done ∘ inT-lift (projR s)`, modulo `mkPair-proj`.
  --   skip/main     `projBl`.
  --   skip/cycle    `~-projL` for the bisimilarity (both sides put in
  --                 `mkPair` form), `inT-projL` for `P ∈T`.
  --   blocked/send  `pstep-inv`; the `n₂` branch is absurd because the
  --                 action mentions `P` and `pfree⇒na` says it cannot.
  --   blocked/recv  same for the head edge; `conts` is re-indexed by
  --                 lifting each `n₁`-step with `stepL`.
  --   blocked/var   `skip-projL` for the trace, `~-projL` for the `~`,
  --                 plus `lookup∘map` for `lu (map projL Δ) X`.
  --   blocked/rec   `skip-projL` for the anchor trace; the context
  --                 extends definitionally, `map projL (W ∷ Δ)`.
  --
  -- THE ONE HARD CASE — `skip/step`.  Building `skip/step` at `projL s`
  -- needs an `n₁`-step out of `projL s`, and the product's step may be an
  -- `n₂` one.  Split on `nedges n₁ (projL s)`:
  --
  --   * non-empty — take its head as the witness; `na` projects (an
  --     `n₁`-action involving `P` would lift by `stepL` and contradict
  --     the product's `na`), and `ktd₁ gr′ = projSkip (ktd (stepL _ gr′))`
  --     with `Ξ` growing as `map projL (s ∷ Ξ)`, which holds definitionally.
  --
  --   * empty — `n₁` is stuck at `projL s`, and stays stuck, since
  --     `n₂`-steps leave the `n₁` component alone.  Then the product tree
  --     cannot end in `blocked/send`/`blocked/recv` (they need a `P`
  --     action, which would have to be an `n₁` action) nor in
  --     `skip/cycle` (it needs `P ∈T s`, and `inT-projL` would give
  --     `P ∈T projL s`, impossible from a state with no outgoing edges).
  --     So it ends in `blocked/var` or `blocked/rec`, and the answer is
  --     `skip/main` of that leaf projected — the `n₁` component is the
  --     same at the leaf as at `s`.  This needs its own structural walk
  --     over the product tree through the `n₂`-only steps.
