{-# OPTIONS --guardedness #-}

-- TODO.md §7 step 3: the abstract statements of the set-based judgment.
--
-- This file currently carries the CLOSURE OPERATORS and the `~`-closure
-- discipline (§5.2, decided in favour of "closed uniformly").  The seven
-- rules come next.
--
-- Two things worth reading before changing anything here.
--
-- `Guard` is NOT as written in TODO.md §3.1.  That line reads
--
--     Guard P W = { s | P ∈T s ∧ s ∈ Reach∀ P (Guard P W) }
--
-- in which `W` does not occur and `Guard P W` defines itself, so it denotes
-- nothing.  The prose gloss in the same section ("reach a `P ∈T` state from
-- which the same holds again") gives the intended reading, which is what is
-- implemented: `Guard P W = { s | P ∈T s ∧ s ∈ W }`.  Here it is inlined into
-- `Wait`'s leaf family rather than named.
--
-- The μ/ν split is sequenced, not nested: `Reach∀` is an ordinary datatype
-- and `Wait` is a coinductive record whose single field is a `Reach∀`.  That
-- is what keeps the guardedness checker out of the fixpoints.

open import Data.Nat using (ℕ; suc)

open import Data.Fin using (Fin)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_)

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Empty using (⊥)

open import Data.List.Relation.Unary.Any using (Any; here; there)

open import Relation.Nullary using (¬_)

open import Definitions.Typing

module Definitions.Typing.Sets {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  open module M = MPST(wb)
  open M

  open import Definitions.Typing.Properties wb using (skip/bisim)

  -- Sets of states.  `Pred Behav` in TODO.md's notation.
  Pred : Set₁
  Pred = Behav → Set

  -- §5.2: every set in the judgment is closed under bisimilarity.
  Closed : Pred → Set
  Closed 𝒮 = ∀ {G H} → G ~ H → 𝒮 G → 𝒮 H

  -- `Reach∀ P 𝒳`: along EVERY path, within finitely many `P`-inactive steps,
  -- land in `𝒳`.  Universal, not existential — the environment picks the
  -- branch (TODO.md §3.1).  `r/step` carries `skip/step`'s own step witness,
  -- so a `P`-inactive dead end is not skippable.
  data Reach∀ (P : Part)(𝒳 : Pred) : Behav → Set where

    r/leaf :
      ∀ {s}
      → 𝒳 s
      → Reach∀ P 𝒳 s

    r/step :
      ∀ {s α t}
      → (na : P not-active-in s)
      → (gr : s -< α >-> t)
      → (k  : ∀ {β u} → s -< β >-> u → Reach∀ P 𝒳 u)
      → Reach∀ P 𝒳 s

  -- `Reach∀⁺`: `Reach∀` in which a leaf drawn from the guard family `𝒢` is
  -- only available STRICTLY below a step.  An `𝒮`-leaf is still available at
  -- depth 0.
  --
  -- This is not decoration, it is what makes the ν productive.  Without it,
  -- `Wait P ∅` is inhabited at every state where `P` is live, by
  --
  --     force w = r/leaf (inj₂ (pin , w))
  --
  -- taking no step at all — machine-checked, and flatly contradicting D4
  -- (`NoLoop.agda`), which proves the `⊢skip` counterpart `Loop P` is empty.
  -- `skip/cycle` cannot do that: `lu Ξ X ~ G` closes against a STRICT
  -- ancestor and every ancestor edge is a `skip/step`, so at least one step
  -- separates two cycle closures.
  --
  -- Closing against a DISTANT ancestor rather than the immediate one needs no
  -- extra machinery: `t ~ A` and `Wait P 𝒮 A` give `Wait P 𝒮 t` by `wait/~`.
  -- That is a second place where §5.2's uniform `~`-closure pays for itself.
  data Reach∀⁺ (P : Part)(𝒮 𝒢 : Pred) : Behav → Set where

    r/leaf⁺ :
      ∀ {s}
      → 𝒮 s
      → Reach∀⁺ P 𝒮 𝒢 s

    r/step⁺ :
      ∀ {s α t}
      → (na : P not-active-in s)
      → (gr : s -< α >-> t)
      → (k  : ∀ {β u} → s -< β >-> u → Reach∀ P (λ v → 𝒮 v ⊎ 𝒢 v) u)
      → Reach∀⁺ P 𝒮 𝒢 s

  -- `Wait P 𝒮` — was `⊢skip`.
  record Wait (P : Part)(𝒮 : Pred)(s : Behav) : Set where
    coinductive
    field
      force : Reach∀⁺ P 𝒮 (λ t → P ∈T t × Wait P 𝒮 t) s

  open Wait public

  -- `Reach₀` — was `t/unskip`.  Existential, forward along `¬P` runs.
  Reach₀ : Part → Pred → Pred
  Reach₀ P 𝒜 s = ∃[ a ] 𝒜 a × (a -[¬ P ]->* s)

  -- `Reach~` — `Reach₀` closed up to `~`, which is what `blocked/var` used.
  -- On `~`-closed sets the two coincide; see `reach~→reach₀` below.
  Reach~ : Part → Pred → Pred
  Reach~ P 𝒜 s = ∃[ a ] ∃[ H ] 𝒜 a × (a -[¬ P ]->* H) × (H ~ s)

  -- Closure preservation.  This is what §5.2 option 1 rests on: if it failed
  -- for any one operator, "all sets are `~`-closed" would not be stable and
  -- the design would have to be reopened.

  reach∀/~ :
    ∀ {P}{𝒳 : Pred}
    → Closed 𝒳
    → Closed (Reach∀ P 𝒳)

  reach∀/~ c G~H (r/leaf x) =
    r/leaf (c G~H x)

  reach∀/~ c G~H (r/step na gr k) =
    r/step
      (na-bisim G~H na)
      (~L→ G~H gr)
      (λ gr′ → reach∀/~ c (~R→~ G~H gr′) (k (~R→ G~H gr′)))

  -- `Wait` needs the map over `Reach∀` to be mutual with the corecursion:
  -- the corecursive call sits inside the leaf family, under `inj₂`/`_,_`,
  -- which is what makes it guarded.
  mutual

    wait/~ :
      ∀ {P}{𝒮 : Pred}
      → Closed 𝒮
      → Closed (Wait P 𝒮)

    force (wait/~ c G~H w) =
      waitB/~ c G~H (force w)

    waitB/~ :
      ∀ {P}{𝒮 : Pred}
      → Closed 𝒮
      → Closed (Reach∀⁺ P 𝒮 (λ t → P ∈T t × Wait P 𝒮 t))

    waitB/~ c G~H (r/leaf⁺ x) =
      r/leaf⁺ (c G~H x)

    waitB/~ c G~H (r/step⁺ na gr k) =
      r/step⁺
        (na-bisim G~H na)
        (~L→ G~H gr)
        (λ gr′ → waitR/~ c (~R→~ G~H gr′) (k (~R→ G~H gr′)))

    waitR/~ :
      ∀ {P}{𝒮 : Pred}
      → Closed 𝒮
      → Closed (Reach∀ P (λ t → 𝒮 t ⊎ (P ∈T t × Wait P 𝒮 t)))

    waitR/~ c G~H (r/leaf (inj₁ x)) =
      r/leaf (inj₁ (c G~H x))

    waitR/~ c G~H (r/leaf (inj₂ (i , w))) =
      r/leaf (inj₂ (∈~ G~H i , wait/~ c G~H w))

    waitR/~ c G~H (r/step na gr k) =
      r/step
        (na-bisim G~H na)
        (~L→ G~H gr)
        (λ gr′ → waitR/~ c (~R→~ G~H gr′) (k (~R→ G~H gr′)))

  reach₀/~ :
    ∀ {P}{𝒜 : Pred}
    → Closed 𝒜
    → Closed (Reach₀ P 𝒜)

  reach₀/~ c G~H (a , a∈ , tr) =
    let H₀ , a~H₀ , tr′ = skip/bisim G~H tr
    in H₀ , c a~H₀ a∈ , tr′

  -- The payoff of §5.2 option 1: on `~`-closed sets `Reach₀` and `Reach~`
  -- are the same operator, so the `blocked/rec` / `blocked/var` asymmetry
  -- disappears rather than propagating into every lemma.

  reach₀→reach~ :
    ∀ {P}{𝒜 : Pred}{s}
    → Reach₀ P 𝒜 s
    → Reach~ P 𝒜 s

  reach₀→reach~ (a , a∈ , tr) =
    a , _ , a∈ , tr , ~refl

  reach~→reach₀ :
    ∀ {P}{𝒜 : Pred}
    → Closed 𝒜
    → ∀ {s}
    → Reach~ P 𝒜 s
    → Reach₀ P 𝒜 s

  reach~→reach₀ c (a , H , a∈ , tr , H~s) =
    reach₀/~ c H~s (a , a∈ , tr)

  -- D4 for the set formulation: `Wait P ∅` is EMPTY, matching `Loop P = ∅`
  -- (`NoLoop.agda`).  This is the check that `Reach∀⁺`'s progress condition is
  -- the RIGHT repair and not merely *a* repair — without it this statement is
  -- false, by the one-line witness quoted at `Reach∀⁺`.
  --
  -- Unlike `NoLoop.agda` there is no ancestor context to carry: a `Guard` leaf
  -- already packages the `Wait` it closes against.  The recursion is again on
  -- the `Any (P ∈α_) αs` witness — `waitR/∅` hands it on unchanged at a guard
  -- leaf, but every cycle back through `waitR/∅` strictly decreases it.

  private
    Grd : Part → Pred
    Grd P t = P ∈T t × Wait P (λ _ → ⊥) t

  mutual

    wait/∅-key :
      ∀ {P s H αs}
      → Wait P (λ _ → ⊥) s
      → s -[ αs ]-> H
      → Any (P ∈α_) αs
      → ⊥

    wait/∅-key w tr mem =
      waitB/∅ (force w) tr mem

    waitB/∅ :
      ∀ {P s H αs}
      → Reach∀⁺ P (λ _ → ⊥) (Grd P) s
      → s -[ αs ]-> H
      → Any (P ∈α_) αs
      → ⊥

    waitB/∅ (r/leaf⁺ ()) _ _

    waitB/∅ (r/step⁺ _ _ _) tr/refl ()

    waitB/∅ (r/step⁺ na _ _) (tr/step gr _) (here px) =
      ∉c→¬∈c (na gr) px

    waitB/∅ (r/step⁺ _ _ k) (tr/step gr tr) (there mem) =
      waitR/∅ (k gr) tr mem

    waitR/∅ :
      ∀ {P s H αs}
      → Reach∀ P (λ v → ⊥ ⊎ Grd P v) s
      → s -[ αs ]-> H
      → Any (P ∈α_) αs
      → ⊥

    waitR/∅ (r/leaf (inj₁ ())) _ _

    waitR/∅ (r/leaf (inj₂ (_ , w))) tr mem =
      wait/∅-key w tr mem

    waitR/∅ (r/step _ _ _) tr/refl ()

    waitR/∅ (r/step na _ _) (tr/step gr _) (here px) =
      ∉c→¬∈c (na gr) px

    waitR/∅ (r/step _ _ k) (tr/step gr tr) (there mem) =
      waitR/∅ (k gr) tr mem

  -- Descend to a guard leaf, which the `Reach∀` tree must reach, and hand its
  -- own `P ∈T` run to the key lemma.
  wait/∅-find :
    ∀ {P s}
    → Reach∀ P (λ v → ⊥ ⊎ Grd P v) s
    → ⊥

  wait/∅-find (r/leaf (inj₁ ()))

  wait/∅-find (r/leaf (inj₂ ((_ , _ , tr , mem) , w))) =
    wait/∅-key w tr mem

  wait/∅-find (r/step _ gr k) =
    wait/∅-find (k gr)

  wait/∅ : ∀ {P s} → ¬ Wait P (λ _ → ⊥) s
  wait/∅ w with force w
  ... | r/leaf⁺ ()
  ... | r/step⁺ _ gr k = wait/∅-find (k gr)

  -- Anchors (D1: `rec` anchors are singletons).  Under §5.2 option 1 the
  -- singleton is taken `~`-closed — `{s | W ~ s}` rather than `{W}` — which
  -- is what lets `s/var` and `s/rec` both use `Reach₀` and never `Reach~`.
  ⌈_⌉ : Behav → Pred
  ⌈ W ⌉ s = W ~ s

  ⌈⌉/closed : ∀ {W} → Closed ⌈ W ⌉
  ⌈⌉/closed G~H W~G = ~trans W~G G~H

  private
    variable
      γ δ : ℕ

  -- The judgment.  One rule per process form; `𝒮` occurs only in
  -- `⊆`-premises, so it stays downward closed and every `Pr` has a largest
  -- `𝒮`, with `∅` satisfying every rule.
  --
  -- `Closed` is deliberately NOT a premise of any rule.  It does not need to
  -- be: the operators preserve closure (proved above), so every set the rules
  -- construct is closed already, and adding the premise would break the
  -- downward closure of `𝒮` that the whole design rests on.  `Closed` is a
  -- hypothesis of the lemmas that need it instead.

  infix 4 _&_⊢_∶_

  data _&_⊢_∶_
    (Γ : Vec Sort γ)
    (Δ : Vec Behav δ)
    : NProc γ δ → Pred → Set₁
    where

    s/send :
      ∀ {P Q I}
        {i  : Fin (suc I)}
        {S  : Sort}
        {E  : Exp γ}
        {Pr : Proc γ δ}
        {𝒮 𝒯 : Pred}
      → (etd : Γ ⊢e E ∶ S)
      → (td  : Γ & Δ ⊢ P ◂ Pr ∶ 𝒯)
      → (sub : ∀ {s}
             → 𝒮 s
             → Wait P (λ u → ∃[ u′ ] (u -< P ⟶ Q # i < S > >-> u′) × 𝒯 u′) s)
      → Γ & Δ ⊢ P ◂ Q ! i < E >∙ Pr ∶ 𝒮

    -- Send is `∃`, receive is `∀`+`∃`: internal versus external choice.  The
    -- process picks the send label, so that exact edge must exist; the
    -- environment picks the branch, so the process must cover every offered
    -- branch and may cover more.  `𝒯` is indexed by `(j , U)`, never by `j`
    -- alone — see TODO.md §6 and `Tests/LabelSorts.agda`.
    s/recv :
      ∀ {P Q I}
        {Br : Vec (Proc (suc γ) δ) (suc I)}
        {𝒮 : Pred}
        {𝒯 : Fin (suc I) → Sort → Pred}
      → (conts : ∀ {j U} → (U ∷ Γ) & Δ ⊢ Q ◂ lu Br j ∶ 𝒯 j U)
      → (sub : ∀ {s}
             → 𝒮 s
             → Wait Q
                 (λ u → (Σ[ j ∈ Fin (suc I) ] ∃[ U ] ∃[ t ]
                           (u -< P ⟶ Q # j < U > >-> t))
                      × (∀ {j U t} → u -< P ⟶ Q # j < U > >-> t → 𝒯 j U t))
                 s)
      → Γ & Δ ⊢ Q ◂ Σ P ？· Br ∶ 𝒮

    s/if :
      ∀ {P E}
        {A B : Proc γ δ}
        {𝒮 : Pred}
      → (etd : Γ ⊢e E ∶ s/bool)
      → (ttd : Γ & Δ ⊢ P ◂ A ∶ 𝒮)
      → (ftd : Γ & Δ ⊢ P ◂ B ∶ 𝒮)
      → Γ & Δ ⊢ P ◂ ifp E then A else B ∶ 𝒮

    -- No `Wait` on `s/if`/`s/end`: `a/if`/`a/end` are top level in `⊢a` and
    -- no `⊢blocked` constructor covers `ifp`/`∅`.  This is sound WITHOUT the
    -- `∪ Loop P` wart because `Loop P = Wait P ∅` is empty — D4, proved in
    -- `Definitions/Typing/NoLoop.agda`.
    s/end :
      ∀ {P}{𝒮 : Pred}
      → (done : ∀ {s} → 𝒮 s → ¬ P ∈T s)
      → Γ & Δ ⊢ P ◂ ∅ ∶ 𝒮

    s/var :
      ∀ {P}{X : Fin δ}{𝒮 : Pred}
      → (sub : ∀ {s} → 𝒮 s → Wait P (Reach₀ P ⌈ lu Δ X ⌉) s)
      → Γ & Δ ⊢ P ◂ v X ∶ 𝒮

    s/rec :
      ∀ {P}
        {Pr : Proc γ (suc δ)}
        {𝒮 𝒜 : Pred}
      → (mg  : MessageGuarded Pr)
      → (td  : ∀ {W} → 𝒜 W → Γ & (W ∷ Δ) ⊢ P ◂ Pr ∶ ⌈ W ⌉)
      → (sub : ∀ {s} → 𝒮 s → Wait P (Reach₀ P 𝒜) s)
      → Γ & Δ ⊢ P ◂ rec Pr ∶ 𝒮

  -- `⊢s M ∶ G` becomes "`G` is in every participant's set" (TODO.md §3.2).
  -- Primed only to coexist with `Declarative`'s `⊢s_∶_`, which is still in
  -- scope; it loses the prime when D2 deletes the old judgment.
  ⊢s′_∶_ : Session → Behav → Set₁
  ⊢s′ M ∶ G =
    ∀ P → ∃[ 𝒮 ] (([] & [] ⊢ P ◂ (M [ P ]s) ∶ 𝒮) × 𝒮 G)
