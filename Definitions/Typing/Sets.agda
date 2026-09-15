{-# OPTIONS --guardedness #-}

-- TODO.md §7 step 3: the abstract statements of the set-based judgment.
--
-- This file currently carries the CLOSURE OPERATORS and the `~`-closure
-- discipline (§5.2, decided in favour of "closed uniformly").  The seven
-- rules come next.
--
-- `Wait` was a ν over `Pred Behav` (TODO.md §3.1's `Reach∀`/`Reach∀⁺`/`Guard`).
-- That is refuted — see the comment at `WaitV` — and it is now the μ over a
-- visited SET of TODO.md §7 step 4b.  The seven typing rules below are
-- unchanged by that: they still speak only of sets of states, and `Wait` is a
-- side condition in a `⊆`-premise, never part of a derivation's shape.

open import Data.Nat using (ℕ; suc)

open import Data.Fin using (Fin)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_)

open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)

open import Data.Empty using (⊥; ⊥-elim)

open import Data.List using (List; []; _∷_)
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

  -- §5.2: every set in the judgment is closed under bisimilarity.  Level
  -- polymorphic because `WaitV` lands in `Set₁`.
  Closed : ∀ {ℓ} → (Behav → Set ℓ) → Set ℓ
  Closed 𝒮 = ∀ {G H} → G ~ H → 𝒮 G → 𝒮 H

  -- `Wait P 𝒮` — was `⊢skip`.  A FINITE tree indexed by a VISITED SET.
  --
  -- The previous definition was a ν over `Pred Behav` (`Reach∀`/`Reach∀⁺` plus
  -- a coinductive record).  It is REFUTED: `Tests/WaitNotSkip.agda` is a
  -- well-behaved theory with a state at which `Wait` holds and no `⊢skip`
  -- derivation exists, so `⊢ ⟺ ⊢set` was unprovable.  A `⊢skip` derivation is
  -- a finite tree whose leaves close against ANCESTORS, and a greatest
  -- fixpoint over states admits infinite unfoldings; the two agree only when
  -- there are finitely many `~`-classes, which `WellBehaved` does not give.
  --
  -- So the ancestors come back — as a SET, which is what keeps the typing
  -- rules set-valued and what bounds the search in the finite realisation
  -- (`V ∪ ⌈s⌉` is idempotent; a vector of ancestors would grow forever).
  -- TODO.md §7 step 4b.
  --
  -- `wv/step` is the only constructor that grows `V`, and `V` is empty at the
  -- root, so a cycle can never close at depth 0.  That is exactly what
  -- `Reach∀⁺`'s progress condition used to have to say by hand.
  data WaitV (P : Part)(𝒮 : Pred) : Pred → Behav → Set₁ where

    wv/leaf :
      ∀ {V s}
      → 𝒮 s
      → WaitV P 𝒮 V s

    wv/cycle :
      ∀ {V s}
      → (anc : ∃[ a ] V a × (a ~ s))
      → (inT : P ∈T s)
      → WaitV P 𝒮 V s

    wv/step :
      ∀ {V s α t}
      → (na : P not-active-in s)
      → (gr : s -< α >-> t)
      → (k  : ∀ {β u} → s -< β >-> u → WaitV P 𝒮 (λ v → V v ⊎ (s ~ v)) u)
      → WaitV P 𝒮 V s

  Wait : Part → Pred → Behav → Set₁
  Wait P 𝒮 = WaitV P 𝒮 (λ _ → ⊥)

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

  -- Weakening in the visited set.  `wv/step` changes the index, so the two
  -- sides of any transport disagree on it and this is needed everywhere.
  waitV/mono :
    ∀ {P}{𝒮 V V′ : Pred}
    → (∀ {s} → V s → V′ s)
    → ∀ {s}
    → WaitV P 𝒮 V s
    → WaitV P 𝒮 V′ s

  waitV/mono f (wv/leaf x) =
    wv/leaf x

  waitV/mono f (wv/cycle (a , a∈ , a~s) inT) =
    wv/cycle (a , f a∈ , a~s) inT

  waitV/mono f (wv/step na gr k) =
    wv/step na gr
      (λ gr′ →
        waitV/mono
          (λ { (inj₁ x)   → inj₁ (f x)
             ; (inj₂ s~v) → inj₂ s~v })
          (k gr′))

  -- `~`-closure.  `V` need not be closed: `wv/cycle` already asks for its
  -- ancestor only up to `~`.
  wait/~ :
    ∀ {P}{𝒮 : Pred}
    → Closed 𝒮
    → ∀ {V : Pred}
    → Closed (WaitV P 𝒮 V)

  wait/~ c G~H (wv/leaf x) =
    wv/leaf (c G~H x)

  wait/~ c G~H (wv/cycle (a , a∈ , a~G) inT) =
    wv/cycle (a , a∈ , ~trans a~G G~H) (∈~ G~H inT)

  wait/~ c G~H (wv/step na gr k) =
    wv/step
      (na-bisim G~H na)
      (~L→ G~H gr)
      (λ gr′ →
        waitV/mono
          (λ { (inj₁ x)   → inj₁ x
             ; (inj₂ G~v) → inj₂ (~trans (~sym G~H) G~v) })
          (wait/~ c (~R→~ G~H gr′) (k (~R→ G~H gr′))))

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

  -- If every leaf of a `Wait` makes `P` active, so does its root: a step node
  -- contributes `in/later`, and a cycle node carries `P ∈T` as its own premise.
  -- Over `⊢skip` this needed two companions (one for the tree, one for the leaf
  -- family); here the leaf family is a plain `Pred`, so it is one lemma.
  waitActive :
    ∀ {P}{𝒮 V : Pred}{s}
    → (∀ {u} → 𝒮 u → P ∈T u)
    → WaitV P 𝒮 V s
    → P ∈T s

  waitActive f (wv/leaf x)        = f x
  waitActive f (wv/cycle _ inT)   = inT
  waitActive f (wv/step _ gr k)   = in/later gr (waitActive f (k gr))

  -- `P ∈T s` is an existential over a RUN containing a `P`-action, so the run
  -- cannot be empty and `s` therefore steps.
  inT→step :
    ∀ {P s} → P ∈T s → ∃[ α ] ∃[ t ] (s -< α >-> t)

  inT→step ([]    , _ , _           , ())
  inT→step (_ ∷ _ , _ , tr/step gr _ , _) = _ , _ , gr

  -- A `Wait` whose leaves all step makes its root step: a step node carries
  -- one, and a cycle node's `P ∈T` yields one by `inT→step`.
  waitStep :
    ∀ {P}{𝒮 V : Pred}{s}
    → (∀ {u} → 𝒮 u → ∃[ α ] ∃[ t ] (u -< α >-> t))
    → WaitV P 𝒮 V s
    → ∃[ α ] ∃[ t ] (s -< α >-> t)

  waitStep f (wv/leaf x)      = f x
  waitStep f (wv/cycle _ inT) = inT→step inT
  waitStep f (wv/step _ gr _) = _ , _ , gr

  -- If `P` is ACTIVE at `s` then a `Wait P 𝒮` at the root can only be a leaf:
  -- `wv/step` demands `P` be inactive, and `wv/cycle` demands a visited
  -- ancestor, which the root has none of.  This is the lemma that replaces
  -- every "walk the skip tree, contradict at `skip/step`" argument in
  -- `Safety/`; over `⊢skip` each of those needed its own companion function.
  waitLeaf :
    ∀ {P}{𝒮 : Pred}{s α t}
    → s -< α >-> t
    → P ∈α α
    → WaitV P 𝒮 (λ _ → ⊥) s
    → 𝒮 s

  waitLeaf _  _  (wv/leaf x)             = x
  waitLeaf _  _  (wv/cycle (_ , () , _) _)
  waitLeaf gr px (wv/step na _ _)        = ⊥-elim (∉c→¬∈c (na gr) px)

  -- Re-rooting.  A subtree whose visited set still mentions the top state `G`
  -- becomes a subtree without it, by replacing every cycle back to `G` with a
  -- copy of `G`'s own tree, transported along `~`.  This is the `WaitV`
  -- analogue of `Properties.agda`'s `skip/unfold-cycle`, and like it needs the
  -- leaf family to transport — which is what `s/recv`'s `tclosed` is for.
  --
  -- The inclusion `W ⊆ V ∪ ⌈ G ⌉` is carried as a FUNCTION rather than applying
  -- `waitV/mono` to the recursive argument: repacking the argument would stop
  -- the recursion being structural (CLAUDE.md).
  waitV/unfold-top :
    ∀ {P}{𝒮 : Pred}
    → Closed 𝒮
    → ∀ {G}
    → WaitV P 𝒮 (λ _ → ⊥) G
    → ∀ {V W : Pred}
    → (∀ {v} → W v → V v ⊎ (G ~ v))
    → ∀ {u}
    → WaitV P 𝒮 W u
    → WaitV P 𝒮 V u

  waitV/unfold-top c top f (wv/leaf x) =
    wv/leaf x

  waitV/unfold-top c top f (wv/cycle (a , wa , a~u) inT)
    with f wa
  ... | inj₁ va  = wv/cycle (a , va , a~u) inT
  ... | inj₂ G~a = waitV/mono (λ ()) (wait/~ c (~trans G~a a~u) top)

  waitV/unfold-top c top f (wv/step na gr k) =
    wv/step na gr
      (λ gr′ →
        waitV/unfold-top c top
          (λ { (inj₁ w)   → [ (λ v → inj₁ (inj₁ v)) , inj₂ ]′ (f w)
             ; (inj₂ u~v) → inj₁ (inj₂ u~v) })
          (k gr′))

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
      -- As for `s/recv`'s `tclosed`: the continuation set is `~`-closed.
      -- `Preservation`'s readiness argument re-roots BOTH sides' `Wait`s, and
      -- re-rooting needs the leaf family to transport along `~`.
      → (tclosed : Closed 𝒯)
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
      -- Conditional on `𝒯 j U` being INHABITED.  `blocked/recv` requires a
      -- continuation only for labels the behaviour actually offers, so
      -- demanding `conts` unconditionally makes the set rules strictly
      -- stronger than `⊢a` and completeness false: a branch the graph never
      -- offers may be arbitrary — even carrying an ill-typed expression, which
      -- has no `Γ ⊢e E ∶ S` to give `s/send` — and `⊢a` still accepts it.
      -- Soundness is unaffected: `set⇒alg` reaches `conts` only from an actual
      -- edge, which supplies the witness.
      → (conts : ∀ {j U t} → 𝒯 j U t → (U ∷ Γ) & Δ ⊢ Q ◂ lu Br j ∶ 𝒯 j U)
      -- The continuation sets are `~`-closed.  This is NOT the thing §5.2
      -- ruled out: that was `Closed 𝒮`, whose premise would break the
      -- downward closure of `𝒮` the design rests on.  `𝒯` is the CONTINUATION
      -- set and is not downward closed by anything, so constraining it costs
      -- nothing.  It is needed because `Safety/Preservation.agda`'s two-sided
      -- readiness argument re-roots the receiver's `Wait` at every step
      -- (`waitV/unfold-top`), and re-rooting replaces a cycle leaf by its
      -- ancestor's tree transported along `~` — which needs the leaf family to
      -- transport, i.e. exactly this.  The `⊢a` proof got the same fact for
      -- free from `blocked/bisim`; here it has to be said.  `alg⇒set` supplies
      -- it as `alg/~`, so completeness is unaffected.
      → (tclosed : ∀ {j U} → Closed (𝒯 j U))
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
