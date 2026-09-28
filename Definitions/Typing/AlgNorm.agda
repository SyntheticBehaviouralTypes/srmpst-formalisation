{-# OPTIONS --guardedness #-}

-- `⊢p → ⊢a` DIRECTLY.  With `AlgDeclarative.agda`'s converse this is the
-- whole equivalence between the two rule sets, and the old, deleted two-tier
-- `⊢a`/`⊢blocked` system is no longer needed by anything — which is the
-- point: there are TWO systems, the declarative one and this one, and
-- nothing in between.
--
-- This replaced `Definitions/Typing/Norm.agda` (830 lines), which is now
-- deleted along with the old `⊢a` itself.  `norm`'s bulk was its `t/skip`
-- case, which had to walk an accumulated `¬P` trace INTO a skip tree
-- (`cancel/unskip`, `MainLeaf`, `LeafAlg`, `leafAlg/unfold-cycle`, …),
-- re-rooting as it went.  Here that re-rooting is `waitV/unfold-top`
-- (`Typing/Alg.agda`), so the trace is handled once and generically, by
-- `waitFollow`, and the trace parameter disappears from the recursion
-- entirely: `t/unskip` just follows.
--
-- The other simplification is coverage.  `norm` is one function over all of
-- `⊢p`; here the recursion is on the PROCESS, so at each leaf family only the
-- three constructors that can conclude that process form are in scope
-- (`t/send`/`t/skip`/`t/unskip` for a send, and so on).  Agda discharges the
-- rest by coverage.
--
-- What each leaf family has to supply is the same two facts in each case:
-- it is `~`-closed, and it ADVANCES along a `¬P` step (`skip/advance` for the
-- communication families, `skip/cat` for the two reachability ones).
--
-- THE ONE IDEA THAT MAKES THIS WORK, and the thing to not undo: `⊢p`'s
-- `t/skip` is SELF-REFERENTIAL — its leaf family is `⊢p` — so digging a fact
-- out of one directly is not structurally recursive past a `skip/cycle`, and
-- no arrangement of a chase fixes that (it was tried twice).  Eliminating the
-- self-reference is what the old `⊢a`'s two-layer `a/skip`/`⊢blocked` split
-- bought, and `WaitV` buys it too, for free: its leaf family is a plain
-- `Pred`, so CONVERT FIRST (structurally, cycles going to `wv/cycle`
-- one-for-one), then read the fact off the result with `waitFind`.  Each
-- family below carries exactly the state-free facts its rule needs, for
-- exactly that reason.

open import Data.Nat using (ℕ; suc)

open import Data.Fin using (Fin; zero; suc)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Empty using (⊥; ⊥-elim)

open import Data.Unit using (⊤; tt)

open import Data.List.Relation.Unary.Any using (Any; here; there)

open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality using (refl)

open import Relation.Unary using (_∈_; _⊆_)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)

open import Definitions.Typing

module Definitions.Typing.AlgNorm
  {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where

  open module M = MPST(wb)
  open M

  open import Definitions.Typing.Alg wb
  open import Definitions.Typing.Properties wb
    using (td/bisim; skip/bisim; skip/bisim-back; skip/unfold-cycle)
  open import Definitions.Typing.MainLeaf wb
  open import Definitions.Typing.AlgEquiv wb using (wait⇒skip)

  -- ══════════════════════════════════════════════════════════════════
  --  Every `Wait` has a reachable leaf
  -- ══════════════════════════════════════════════════════════════════
  --
  -- This is the whole reason the construction below goes THROUGH `Wait`
  -- rather than digging in the `⊢p` derivation directly.  `⊢p`'s `t/skip`
  -- is self-referential — its leaf family is `⊢p` again — so a leaf found
  -- past a `skip/cycle` may need unwrapping once more, and that second
  -- unwrap is not a subterm of anything the termination checker can see.
  -- `WaitV`'s leaf family is a plain `Pred`, chosen here to carry exactly
  -- the non-recursive facts each rule needs, so the leaf found IS the
  -- answer and nothing further has to be chased.  Cycles cost nothing on
  -- the way in: `wv/cycle` mirrors `skip/cycle` one-for-one.
  --
  -- Both halves are already proved: `wait⇒skip` (`AlgEquiv.agda`) and
  -- `findMain` (`MainLeaf.agda`, generic in the leaf family, and the only
  -- thing that knows how to see past a cycle).
  -- The process is explicit: it does not occur in the result, so nothing
  -- would solve it.
  waitFind :
    ∀ {γ δ}{P}(Pr : Proc γ δ){𝒮 : Behavs}{G}
    → WaitV P 𝒮 (λ _ → ⊥) G
    → ∃[ H ] 𝒮 H

  waitFind {P = P} Pr {𝒮 = 𝒮} w =
    findMain P Pr (λ _ H → 𝒮 H) (wait⇒skip P Pr 𝒮 w)

  private
    variable
      γ δ ξ : ℕ

  -- ══════════════════════════════════════════════════════════════════
  --  The canonical set: `⊢p`-typeability
  -- ══════════════════════════════════════════════════════════════════
  --
  -- The set judgment is proved at the LARGEST set, and the rules' downward
  -- closure recovers every smaller one.

  Typ : Vec Sort γ → Vec Behav δ → NProc γ δ → Behavs
  Typ Γ Δ PPr G = Γ & Δ ⊢p PPr ∶ G

  typ/closed :
    ∀ {Γ : Vec Sort γ}{Δ : Vec Behav δ}{P}{Pr : Proc γ δ}
    → Closed (Typ Γ Δ (P ◂ Pr))
  typ/closed = td/bisim ~ᵛ-refl

  -- ══════════════════════════════════════════════════════════════════
  --  Following a `¬P` run with a `Wait`
  -- ══════════════════════════════════════════════════════════════════
  --
  -- This is what `norm` needed `cancel/unskip` and the whole `MainLeaf`
  -- apparatus for.  A `wv/step` node re-roots by `waitV/unfold-top`; a leaf
  -- advances by the family's own `adv`; a cycle cannot occur, because the root
  -- has an empty visited set.

  Advances : Part → Behavs → Set
  Advances P 𝒮 = ∀ {u α v} → 𝒮 u → u -< α >-> v → P ∉α α → 𝒮 v

  waitStep1 :
    ∀ {P}{𝒮 : Behavs}
    → Closed 𝒮
    → Advances P 𝒮
    → ∀ {u α v}
    → WaitV P 𝒮 (λ _ → ⊥) u
    → u -< α >-> v
    → P ∉α α
    → WaitV P 𝒮 (λ _ → ⊥) v

  waitStep1 c adv (wv/leaf x) gr P∉α =
    wv/leaf (adv x gr P∉α)

  waitStep1 c adv (wv/cycle (_ , () , _) _) _ _

  waitStep1 c adv top@(wv/step _ _ k) gr _ =
    waitV/unfold-top c top (λ w → w) (k gr)

  waitFollow :
    ∀ {P}{𝒮 : Behavs}
    → Closed 𝒮
    → Advances P 𝒮
    → ∀ {G s}
    → WaitV P 𝒮 (λ _ → ⊥) G
    → G -[¬ P ]->* s
    → WaitV P 𝒮 (λ _ → ⊥) s

  waitFollow c adv w ([] , tr/refl , []) = w
  waitFollow c adv w (_ ∷ αs , tr/step gr tr , P∉α ∷ allP) =
    waitFollow c adv (waitStep1 c adv w gr P∉α) (αs , tr , allP)

  -- One `¬P` step as a run, for the `adv`s below.
  one : ∀ {P u α v} → u -< α >-> v → P ∉α α → u -[¬ P ]->* v
  one gr P∉α = tr¬/step gr P∉α skip/refl

  -- An idle walk is a `¬P` run.
  idle⇒unskip : ∀ {P s t} → Star (_⇝[ P ]_) s t → s -[¬ P ]->* t
  idle⇒unskip ε                   = skip/refl
  idle⇒unskip ((na , _ , gr) ◅ run) = tr¬/step gr (na gr) (idle⇒unskip run)

  -- `Unskip` at fixed anchors: the leaf family of `a/var`/`a/rec`.
  After : Part → Behavs → Behavs
  After P 𝒜 s = ∃[ a ] 𝒜 a × a -[¬ P ]->* s

  after/~ : ∀ {P}{𝒜 : Behavs} → Closed 𝒜 → Closed (After P 𝒜)
  after/~ c G~H (a , a∈ , tr) =
    let H₀ , a~H₀ , tr′ = skip/bisim G~H tr
    in H₀ , c a~H₀ a∈ , tr′

  -- ══════════════════════════════════════════════════════════════════
  --  Visited vectors as sets (`Vof`, `Typing/Alg.agda`)
  -- ══════════════════════════════════════════════════════════════════

  vof/cons :
    ∀ {ξ}{Ξ : Vec Behav ξ}{A s} → Vof (A ∷ Ξ) s → Vof Ξ s ⊎ (A ~ s)
  vof/cons (zero  , eq) = inj₂ eq
  vof/cons (suc X , eq) = inj₁ (X , eq)

  vof/nil : ∀ {s} → Vof [] s → ⊥
  vof/nil (() , _)

  -- `∅`'s leaf family: P never becomes active.  It mentions neither `Γ`
  -- nor `Δ`, so it lives here rather than in the block below — otherwise
  -- both are phantom parameters of every use and nothing can solve them.
  -- `P ∈T` is backward closed (`in/later`), so `¬ P ∈T` advances along any
  -- step, `¬P` or not.
  EndL : Part → Behavs
  EndL P u = ¬ P ∈T u

  endL/closed : ∀ {P} → Closed (EndL P)
  endL/closed G~H x inT = x (∈~ (~sym G~H) inT)

  endL/adv : ∀ {P} → Advances P (EndL P)
  endL/adv x gr _ inT = x (in/later gr inT)

  ---------------------------------------------------------------------
  -- `∅`: `a/end`'s `done` must hold at EVERY state of the set, not just
  -- at one, so `waitFind` is no use here — it lands on some other state.
  -- Instead assume `P ∈T` at the state in question and chase its run
  -- into the tree, exactly as `Norm.agda`'s `a∅/notin` does: `na` kills
  -- the run's first action at each step, and unfolding keeps the visited
  -- set empty, so `skip/cycle` never arises (its index would be `Fin 0`)
  -- and the run runs out.  The leaf family here is `¬ P ∈T`, a plain
  -- predicate, so a leaf ends it outright.
  ---------------------------------------------------------------------

  -- Generic in the process: the chase reads only the leaf family, never
  -- the process, and pinning it to `∅` would leave `γ`/`δ` unsolvable.
  endUnfold :
    ∀ {γ δ}{P}{Pr : Proc γ δ}{G H}
    → ((λ _ K → EndL P K) & [] ⊢skip P ◂ Pr ∶ G)
    → ((λ _ K → EndL P K) & (G ∷ []) ⊢skip P ◂ Pr ∶ H)
    → ((λ _ K → EndL P K) & [] ⊢skip P ◂ Pr ∶ H)

  endUnfold {P = P}{Pr = Pr} =
    skip/unfold-cycle {PPr = P ◂ Pr} {Ξ = []} {Ξ′ = []}
      (λ G~G′ x inT → x (∈~ (~sym G~G′) inT))

  endChase :
    ∀ {γ δ}{P}{Pr : Proc γ δ}{G}
    → P ∈T G
    → ((λ _ K → EndL P K) & [] ⊢skip P ◂ Pr ∶ G)
    → ⊥

  endChase inT (skip/main x) = x inT
  endChase (_ , _ , tr/refl , ()) (skip/step _ _ _)
  endChase {P = P} (_ , _ , tr/step {α = α} gr₁ _ , here p)
           (skip/step _ na _) =
    ∉α→¬∈α {P} {α} (na gr₁) p
  endChase (_ , _ , tr/step gr₁ tr , there mem) std@(skip/step _ _ ktd) =
    endChase (_ , _ , tr , mem) (endUnfold std (ktd gr₁))

  -- ══════════════════════════════════════════════════════════════════
  --  The leaf families
  -- ══════════════════════════════════════════════════════════════════
  --
  -- A family that does not mention `Γ` or `Δ` is stated outside the block
  -- that has them as parameters (like `EndL` above); otherwise they would be
  -- phantom parameters of every use, and nothing could solve them.

  -- var and rec: both `After`, so both advance by `skip/cat`.
  after/adv : ∀ {P}{𝒜 : Behavs} → Advances P (After P 𝒜)
  after/adv (a , a∈ , tr) grα P∉α =
    a , a∈ , skip/cat tr (one grα P∉α)

  -- `rec`'s guardedness, as its own constant family — the same trick as
  -- `IfE`.  `a/rec` needs it as a single state-free fact, and keeping it
  -- OUT of `RecA` is what lets `RecA` stay the plain anchor set.
  RecG : ∀ {γ δ} → Proc γ (suc δ) → Behavs
  RecG Pr _ = MessageGuarded Pr

  recG/closed : ∀ {γ δ}{Pr : Proc γ (suc δ)} → Closed (RecG Pr)
  recG/closed _ guarded = guarded

  recG/adv : ∀ {γ δ}{P}{Pr : Proc γ (suc δ)} → Advances P (RecG Pr)
  recG/adv guarded _ _ = guarded

  -- `if`: the guard's typing, constant in the state.
  module _ {γ}{Γ : Vec Sort γ} where

    IfE : Exp γ → Behavs
    IfE E _ = Γ ⊢e E ∶ s/bool

    ifE/closed : ∀ {E} → Closed (IfE E)
    ifE/closed _ etd = etd

    ifE/adv : ∀ {P}{E} → Advances P (IfE E)
    ifE/adv etd _ _ = etd

  module _ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ} where

    ---------------------------------------------------------------------
    -- send
    ---------------------------------------------------------------------

    SendL :
      ∀ {I} → Part → PartSet → Fin (suc I) → Sort → Proc γ δ → Behavs
    SendL P Qs i S Pr u =
      ∃[ u′ ] (u -<[ P ↦ (! Qs) # i < S > ]>-> u′) × Typ Γ Δ (P ◂ Pr) u′

    sendL/closed :
      ∀ {I P Qs}{i : Fin (suc I)}{S}{Pr} → Closed (SendL P Qs i S Pr)
    sendL/closed G~H (_ , (α , eq , gr) , td) =
      _ , (α , eq , ~L→ G~H gr) , typ/closed (~L→~ G~H gr) td

    sendL/adv :
      ∀ {I P Qs}{i : Fin (suc I)}{S}{Pr} → Advances P (SendL P Qs i S Pr)
    sendL/adv {P = P} (_ , (α , eq , gr) , td) grα P∉α
      with skip/advance {P = P} (one {P = P} grα P∉α) gr (_ , eq)
    ... | _ , gr′ , tr = _ , (α , eq , gr′) , t/unskip tr td

    ---------------------------------------------------------------------
    -- recv
    ---------------------------------------------------------------------

    RecvL :
      ∀ {I} → Part → Part → Vec (Proc (suc γ) δ) (suc I) → Behavs
    RecvL {I} P Q Br u =
      (Σ[ j ∈ Fin (suc I) ] ∃[ U ] ∃[ t ] (u -<[ Q ↦ (？ P) # j < U > ]>-> t))
      × (∀ {j U t} → u -<[ Q ↦ (？ P) # j < U > ]>-> t
                   → Typ (U ∷ Γ) Δ (Q ◂ lu Br j) t)

    recvL/closed :
      ∀ {I P Q}{Br : Vec (Proc (suc γ) δ) (suc I)} → Closed (RecvL P Q Br)
    recvL/closed G~H ((j , U , _ , (α , eq , gr)) , k) =
      (j , U , _ , (α , eq , ~L→ G~H gr)) ,
      λ { (α′ , eq′ , gr′) →
          typ/closed (~R→~ G~H gr′) (k (α′ , eq′ , ~R→ G~H gr′)) }

    -- A branch offered after the `¬Q` step was offered before it
    -- (`recv/same-comm`, `branch/before`), so `k` covers it.
    recvL/adv :
      ∀ {I P Q}{Br : Vec (Proc (suc γ) δ) (suc I)} → Advances Q (RecvL P Q Br)
    recvL/adv {Q = Q} ((j , U , _ , (α , eq , gr)) , k) grα Q∉α
      with skip/advance {P = Q} (one {P = Q} grα Q∉α) gr (_ , eq)
    ... | _ , gr′ , _ =
      (j , U , _ , (α , eq , gr′)) ,
      λ { (α″ , eq″ , gr″) →
          let tr  = one {P = Q} grα Q∉α
              ceq = recv/same-comm tr gr (_ , _ , eq) gr″ (_ , _ , eq″)
              _ , gr₀ , tr₀ = branch/before tr (_ , _ , eq) gr gr″ ceq
          in t/unskip tr₀ (k (α″ , eq″ , gr₀)) }

    ---------------------------------------------------------------------
    -- rec
    ---------------------------------------------------------------------

    -- The `rec` anchor family: the body typed at its own anchor.  This is
    -- exactly `a/rec`'s `𝒜`, and `Check/Alg.agda` decides membership in
    -- it directly, so it stays free of anything else.
    RecA : ∀ {P} → Proc γ (suc δ) → Behavs
    RecA {P = P} Pr W = Typ Γ (W ∷ Δ) (P ◂ Pr) W

    recA/closed :
      ∀ {P}{Pr : Proc γ (suc δ)} → Closed (RecA {P = P} Pr)
    recA/closed W~W′ td =
      td/bisim (~ᵛ/∷ W~W′ ~ᵛ-refl) W~W′ td

    ---------------------------------------------------------------------
    -- The "one state-free fact" families (`SendE` here, `RecG` and `IfE`
    -- above).  Each is a plain `Pred`, so `waitFind` on it lands on the
    -- fact itself with nothing left to unwrap — which is the whole point
    -- (see `waitFind`).
    ---------------------------------------------------------------------

    -- Sort-agnostic send: `a/send` needs ONE sort, fixed outside the set,
    -- but `sendWait` already needs that sort to build its family.  So the
    -- sort is existential here, extracted once, and `sendWait` is then run
    -- at the sort found.  `⊢e-unique` is what makes "the sort found" and
    -- "every leaf's sort" the same thing.
    SendE :
      ∀ {I} → Part → PartSet → Fin (suc I) → Exp γ → Proc γ δ → Behavs
    SendE P Qs i E Pr u =
      Σ[ S ∈ Sort ]
        ∃[ u′ ] (Γ ⊢e E ∶ S) × (u -<[ P ↦ (! Qs) # i < S > ]>-> u′)
              × Typ Γ Δ (P ◂ Pr) u′

    sendE/closed :
      ∀ {I P Qs}{i : Fin (suc I)}{E}{Pr} → Closed (SendE P Qs i E Pr)
    sendE/closed G~H (S , _ , etd , (α , eq , gr) , td) =
      S , _ , etd , (α , eq , ~L→ G~H gr) , typ/closed (~L→~ G~H gr) td

    sendE/adv :
      ∀ {I P Qs}{i : Fin (suc I)}{E}{Pr} → Advances P (SendE P Qs i E Pr)
    sendE/adv {P = P} (S , _ , etd , (α , eq , gr) , td) grα P∉α
      with skip/advance {P = P} (one {P = P} grα P∉α) gr (_ , eq)
    ... | _ , gr′ , tr = S , _ , etd , (α , eq , gr′) , t/unskip tr td

  -- ══════════════════════════════════════════════════════════════════
  --  `⊢p` derivation ⟶ `Wait`, for every leaf family at once
  -- ══════════════════════════════════════════════════════════════════
  --
  -- A derivation of `P ◂ Pr` ends in `t/unskip` (follow the run with the
  -- family's `adv`), in `t/skip` (mirror the tree onto `WaitV` exactly as
  -- `AlgEquiv.agda`'s `skip⇒waitV` does, calling back at every
  -- `skip/main`), or in a rule for `Pr` itself: a `Base` derivation, where
  -- the family's `base` reads its fact off.  Only `base` differs between
  -- families.  It is a module PARAMETER, not a mutually recursive function,
  -- so the recursion below stays structural.

  Base : ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{PPr G} → Γ & Δ ⊢p PPr ∶ G → Set
  Base (t/skip _)     = ⊥
  Base (t/unskip _ _) = ⊥
  Base _              = ⊤

  module Walk
    {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{P}{Pr : Proc γ δ}
    (L : Behavs)(c : Closed L)(adv : Advances P L)
    (base : ∀ {G}(td : Γ & Δ ⊢p P ◂ Pr ∶ G) → Base td → L G)
    where

    mutual

      walk : ∀ {G} → Γ & Δ ⊢p P ◂ Pr ∶ G → WaitV P L (λ _ → ⊥) G
      walk (t/unskip tr td)    = waitFollow c adv (walk td) tr
      walk (t/skip std)        = waitV/mono vof/nil (tree std)
      walk td@(t/send _ _ _)   = wv/leaf (base td tt)
      walk td@(t/recv _ _)     = wv/leaf (base td tt)
      walk td@(t/if _ _ _)     = wv/leaf (base td tt)
      walk td@(t/rec _ _)      = wv/leaf (base td tt)
      walk td@(t/var _)        = wv/leaf (base td tt)
      walk td@(t/end _)        = wv/leaf (base td tt)

      tree :
        ∀ {ξ}{Ξ : Vec Behav ξ}{G}
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ Pr ∶ G
        → WaitV P L (Vof Ξ) G
      tree (skip/main td)              = waitV/mono (λ ()) (walk td)
      tree (skip/step gr na ktd)       =
        wv/step na gr (λ gr′ → waitV/mono vof/cons (tree (ktd gr′)))
      tree (skip/cycle {X = X} eq inT) = wv/cycle (_ , (X , ~refl) , eq) inT

  -- One instance per family.
  module _ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ} where

    sendWait :
      ∀ {I P Qs}{i : Fin (suc I)}{S E}{Pr : Proc γ δ}{G}
      → Γ ⊢e E ∶ S
      → Γ & Δ ⊢p P ◂ Qs ! i < E >∙ Pr ∶ G
      → WaitV P (SendL {Γ = Γ} {Δ = Δ} P Qs i S Pr) (λ _ → ⊥) G
    sendWait etd = Walk.walk _ sendL/closed sendL/adv base
      where
        base : ∀ {G}(td : Γ & Δ ⊢p _ ◂ _ ∶ G) → Base td → SendL _ _ _ _ _ G
        base (t/send gr etd′ td) _ with ⊢e-unique etd′ etd
        ... | refl = _ , gr , td

    recvWait :
      ∀ {I P Q}{Br : Vec (Proc (suc γ) δ) (suc I)}{G}
      → Γ & Δ ⊢p Q ◂ Σ P ？· Br ∶ G
      → WaitV Q (RecvL {Γ = Γ} {Δ = Δ} P Q Br) (λ _ → ⊥) G
    recvWait {Br = Br} =
      Walk.walk _ (recvL/closed {Br = Br}) (recvL/adv {Br = Br})
        λ { (t/recv gr conts) _ → (_ , _ , _ , gr) , conts }

    varWait :
      ∀ {P}{X : Fin δ}{G}
      → Γ & Δ ⊢p P ◂ v X ∶ G
      → WaitV P (After P (lu Δ X ~_)) (λ _ → ⊥) G
    varWait =
      Walk.walk _ (after/~ (λ G~H W~G → ~trans W~G G~H)) after/adv
        λ { (t/var eq) _ → _ , eq , skip/refl }

    recWait :
      ∀ {P}{Pr : Proc γ (suc δ)}{G}
      → Γ & Δ ⊢p P ◂ rec Pr ∶ G
      → WaitV P (After P (RecA {Γ = Γ} {Δ = Δ} {P = P} Pr)) (λ _ → ⊥) G
    recWait {P = P} {Pr = Pr} =
      Walk.walk _ (after/~ (recA/closed {Γ = Γ} {Δ = Δ} {P = P} {Pr = Pr}))
        after/adv
        λ { (t/rec _ td) _ → _ , td , skip/refl }

    sendEWait :
      ∀ {I P Qs}{i : Fin (suc I)}{E}{Pr : Proc γ δ}{G}
      → Γ & Δ ⊢p P ◂ Qs ! i < E >∙ Pr ∶ G
      → WaitV P (SendE {Γ = Γ} {Δ = Δ} P Qs i E Pr) (λ _ → ⊥) G
    sendEWait =
      Walk.walk _ sendE/closed sendE/adv
        λ { (t/send gr etd td) _ → _ , _ , etd , gr , td }

    recGWait :
      ∀ {P}{Pr : Proc γ (suc δ)}{G}
      → Γ & Δ ⊢p P ◂ rec Pr ∶ G
      → WaitV P (RecG Pr) (λ _ → ⊥) G
    recGWait = Walk.walk _ recG/closed recG/adv λ { (t/rec guarded _) _ → guarded }

    ifEWait :
      ∀ {P E}{A B : Proc γ δ}{G}
      → Γ & Δ ⊢p P ◂ ifp E then A else B ∶ G
      → WaitV P (IfE {Γ = Γ} E) (λ _ → ⊥) G
    ifEWait = Walk.walk _ ifE/closed ifE/adv λ { (t/if etd _ _) _ → etd }

    endWait :
      ∀ {P}{G}
      → Γ & Δ ⊢p P ◂ ∅ ∶ G
      → WaitV P (EndL P) (λ _ → ⊥) G
    endWait = Walk.walk _ endL/closed endL/adv λ { (t/end done) _ → done }

    ---------------------------------------------------------------------
    -- `if`: splitting a derivation into its two branches, AT THE SAME
    -- STATE.  Unlike everything above this needs no `Wait` and no leaf
    -- hunting at all: the result is a TREE of the same shape, so a
    -- `skip/cycle` is copied across verbatim — it carries no branch data
    -- to split.  `a/if` takes no `Wait` premise (D4), which is exactly why
    -- this is the whole of it.
    ---------------------------------------------------------------------

    mutual

      ifTrue :
        ∀ {P E}{A B : Proc γ δ}{G}
        → Γ & Δ ⊢p P ◂ ifp E then A else B ∶ G
        → Γ & Δ ⊢p P ◂ A ∶ G

      ifTrue (t/if _ ttd _)    = ttd
      ifTrue (t/unskip tr td)  = t/unskip tr (ifTrue td)
      ifTrue (t/skip std)      = t/skip (ifTrueTree std)

      ifTrueTree :
        ∀ {ξ}{Ξ : Vec Behav ξ}{P E}{A B : Proc γ δ}{G}
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ ifp E then A else B ∶ G
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ A ∶ G

      ifTrueTree (skip/main td) = skip/main (ifTrue td)
      ifTrueTree (skip/step gr na ktd) =
        skip/step gr na (λ gr′ → ifTrueTree (ktd gr′))
      ifTrueTree (skip/cycle eq inT) = skip/cycle eq inT

    mutual

      ifFalse :
        ∀ {P E}{A B : Proc γ δ}{G}
        → Γ & Δ ⊢p P ◂ ifp E then A else B ∶ G
        → Γ & Δ ⊢p P ◂ B ∶ G

      ifFalse (t/if _ _ ftd)   = ftd
      ifFalse (t/unskip tr td) = t/unskip tr (ifFalse td)
      ifFalse (t/skip std)     = t/skip (ifFalseTree std)

      ifFalseTree :
        ∀ {ξ}{Ξ : Vec Behav ξ}{P E}{A B : Proc γ δ}{G}
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ ifp E then A else B ∶ G
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ B ∶ G

      ifFalseTree (skip/main td) = skip/main (ifFalse td)
      ifFalseTree (skip/step gr na ktd) =
        skip/step gr na (λ gr′ → ifFalseTree (ktd gr′))
      ifFalseTree (skip/cycle eq inT) = skip/cycle eq inT


    endNotin :
      ∀ {P}{G}
      → Γ & Δ ⊢p P ◂ ∅ ∶ G
      → ¬ P ∈T G

    endNotin {P = P} td inT =
      endChase inT (wait⇒skip {γ = γ} {δ = δ} P ∅ (EndL P) (endWait td))

  -- ══════════════════════════════════════════════════════════════════
  --  `⊢p` ⟶ `⊢a`, at the largest set
  -- ══════════════════════════════════════════════════════════════════
  --
  -- Stated at the LARGEST set, `Typed`: `⊢p`-typeability, with the anchors
  -- of a state as `Δ`.  `alg/mono` recovers every smaller set.
  --
  -- The continuation sets of `a/send`/`a/recv` are `Post α (Front P 𝒮)`.
  -- Each state in one is `α` out of a state `u` idle-reachable from some
  -- `G ∈ 𝒮` where `P` acts; following the idle run with the `Wait` at `G`
  -- (`waitFollow`) and reading the leaf at `u` (`waitLeaf`, since `P` acts
  -- at `u`) gives the continuation's `⊢p` derivation.
  --
  -- The recursion is on the PROCESS, not the derivation: the derivation
  -- each case needs comes out of `waitFind` and is not a subterm of the
  -- one it came from.  `typBr` makes `lu Br j` structural.

  Typed : ∀ {γ δ} → Vec Sort γ → NProc γ δ → States δ
  Typed Γ PPr (ws , G) = Γ & ws ⊢p PPr ∶ G

  -- `a/rec`'s entry set: the body typed at its own anchor.
  Entry : ∀ {γ δ} → Vec Sort γ → Part → Proc γ (suc δ) → States δ
  Entry Γ P Pr (ws , W) = Γ & (W ∷ ws) ⊢p P ◂ Pr ∶ W

  recvAt :
    ∀ {γ δ}{Γ : Vec Sort γ}{I P Q}{Br : Vec (Proc (suc γ) δ) (suc I)}{j U}
    → Post Q ((？ P) # j < U >) (Front Q (Typed Γ (Q ◂ Σ P ？· Br)))
      ⊆ Typed (U ∷ Γ) (Q ◂ lu Br j)

  recvAt {Q = Q}{Br = Br}{j}{U}{ws , t}
         (_ , ((_ , td , run) , _) , (α , eq , gr))
    with waitLeaf {Q} gr (_ , eq)
           (waitFollow (recvL/closed {Br = Br}) (recvL/adv {Br = Br})
              (recvWait td) (idle⇒unskip run))
  ... | _ , k = k (α , eq , gr)

  -- The send case needs the SYNCHRONOUS instance: `a/send` types the
  -- continuation after EVERY step with `P`'s event, `t/send` after one, and
  -- only `balanced` (via `send-det`) makes those the same step.
  module _ (sync : Synchronous B) where
    open Synchronous sync using (send-det)

    sendAt :
      ∀ {γ δ}{Γ : Vec Sort γ}{I P Qs}{i : Fin (suc I)}{S E}{Pr : Proc γ δ}
      → Γ ⊢e E ∶ S
      → Post P ((! Qs) # i < S >) (Front P (Typed Γ (P ◂ Qs ! i < E >∙ Pr)))
        ⊆ Typed Γ (P ◂ Pr)

    sendAt {P = P} etd {ws , t} (_ , ((_ , td , run) , _) , (α , eq , gr))
      with waitLeaf {P} gr (_ , eq)
             (waitFollow sendL/closed sendL/adv (sendWait etd td)
               (idle⇒unskip run))
    ... | _ , (α′ , eq′ , gr′) , td′
      with send-det gr gr′ eq eq′
    ...   | refl rewrite step-deterministic gr gr′ = td′

    mutual

      typing⇒alg :
        ∀ {γ δ}{Γ : Vec Sort γ}{P}(Pr : Proc γ δ){ws G}
        → Γ & ws ⊢p P ◂ Pr ∶ G
        → Γ ⊢a P ◂ Pr ∶ Typed Γ (P ◂ Pr)

      typing⇒alg (Qs ! i < E >∙ Pr) td
        with waitFind (Qs ! i < E >∙ Pr) (sendEWait td)
      ... | _ , _ , _ , etd , _ , cont =
        a/send etd
          (λ td′ → waitV/leaf-mono (λ { (_ , gr , _) → _ , gr })
                     (sendWait etd td′))
          (alg/mono (sendAt etd) (typing⇒alg Pr cont))

      typing⇒alg (Σ Q ？· Br) td =
        a/recv
          (λ td′ → waitV/leaf-mono proj₁ (recvWait td′))
          (λ { {j} (_ , x∈) →
               alg/mono (recvAt {Br = Br})
                 (typBr Br j (recvAt {Br = Br} x∈)) })

      typing⇒alg (ifp E then A else B) td
        with waitFind (ifp E then A else B) (ifEWait td)
      ... | _ , etd =
        a/if etd
          (alg/mono ifTrue  (typing⇒alg A (ifTrue td)))
          (alg/mono ifFalse (typing⇒alg B (ifFalse td)))

      typing⇒alg ∅ td = a/end endNotin

      typing⇒alg (v X) td = a/var varWait

      typing⇒alg {Γ = Γ}{P} (rec Pr) td
        with waitFind (rec Pr) (recGWait td) | waitFind (rec Pr) (recWait td)
      ... | _ , guarded | _ , _ , aW , _ =
        a/rec {𝒜 = Entry Γ P Pr} guarded
          (alg/mono (λ { {_ ∷ _ , _} (aW′ , W~s) → typ/closed W~s aW′ })
                    (typing⇒alg Pr aW))
          recWait

      typBr :
        ∀ {γ δ n}{Γ : Vec Sort γ}{Q}
          (Br : Vec (Proc (suc γ) δ) n)(j : Fin n){U ws t}
        → (U ∷ Γ) & ws ⊢p Q ◂ lu Br j ∶ t
        → (U ∷ Γ) ⊢a Q ◂ lu Br j ∶ Typed (U ∷ Γ) (Q ◂ lu Br j)

      typBr (B ∷ Bs) zero    w = typing⇒alg B w
      typBr (B ∷ Bs) (suc j) w = typBr Bs j w

    -- ════════════════════════════════════════════════════════════════
    --  The boundary `Safety/` uses
    -- ════════════════════════════════════════════════════════════════

    td⇒at :
      ∀ {γ δ}{Γ : Vec Sort γ}{P}{Pr : Proc γ δ}{ws G}
      → Γ & ws ⊢p P ◂ Pr ∶ G
      → Γ ⊢at P ◂ Pr ∶ (ws , G)

    td⇒at {Pr = Pr} td = _ , typing⇒alg Pr td , td
