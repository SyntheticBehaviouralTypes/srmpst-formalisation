{-# OPTIONS --guardedness #-}

-- `⊢p → ⊢set` DIRECTLY.  With `SetsDeclarative.agda`'s converse this is the
-- whole equivalence between the two rule sets, and `⊢a` is no longer needed by
-- anything — which is the point: there are TWO systems, the declarative one and
-- the set-based one, and nothing in between.
--
-- This replaced `Definitions/Typing/Norm.agda` (830 lines), which is now
-- deleted along with `⊢a` itself.  `norm`'s bulk was its `t/skip` case, which
-- had to walk an accumulated `¬P` trace INTO a skip tree (`cancel/unskip`,
-- `MainLeaf`, `LeafAlg`, `leafAlg/unfold-cycle`, …), re-rooting as it went.
-- Here that re-rooting is `waitV/unfold-top` (`Typing/Sets.agda`), so the
-- trace is handled once and generically, by `waitFollow`, and the trace
-- parameter disappears from the recursion entirely: `t/unskip` just follows.
--
-- The other simplification is coverage.  `norm` is one function over all of
-- `⊢p`; here the recursion is on the PROCESS, so at each leaf family only the
-- three constructors that can conclude that process form are in scope
-- (`t/send`/`t/skip`/`t/unskip` for a send, and so on).  Agda discharges the
-- rest by coverage.
--
-- What each leaf family has to supply is the same two facts in each case:
-- it is `~`-closed, and it ADVANCES along a `¬P` step (`skip/advance` for the
-- communication families, `skip/cat` for the two `Reach₀` ones).
--
-- THE ONE IDEA THAT MAKES THIS WORK, and the thing to not undo: `⊢p`'s
-- `t/skip` is SELF-REFERENTIAL — its leaf family is `⊢p` — so digging a fact
-- out of one directly is not structurally recursive past a `skip/cycle`, and
-- no arrangement of a chase fixes that (it was tried twice).  Eliminating the
-- self-reference is what `⊢a`'s two-layer `a/skip`/`⊢blocked` split bought,
-- and `WaitV` buys it too, for free: its leaf family is a plain `Pred`, so
-- CONVERT FIRST (structurally, cycles going to `wv/cycle` one-for-one), then
-- read the fact off the result with `waitFind`.  Each family below carries
-- exactly the state-free facts its rule needs, for exactly that reason.

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

open import Data.List.Relation.Unary.Any using (Any; here; there)

open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality using (refl)

open import Definitions.Typing

module Definitions.Typing.SetsNorm
  {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where

  open module M = MPST(wb)
  open M

  open import Definitions.Typing.Sets wb
  open import Definitions.Typing.Properties wb
    using (td/bisim; skip/bisim-back; skip/unfold-cycle)
  open import Definitions.Typing.MainLeaf wb
  open import Definitions.Typing.SetsEquiv wb using (wait⇒skip)

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
  -- Both halves are already proved: `wait⇒skip` (`SetsEquiv.agda`) and
  -- `findMain` (`MainLeaf.agda`, generic in the leaf family, and the only
  -- thing that knows how to see past a cycle).
  -- The process is explicit: it does not occur in the result, so nothing
  -- would solve it.
  waitFind :
    ∀ {γ δ}{P}(Pr : Proc γ δ){𝒮 : Pred}{G}
    → Wait P 𝒮 G
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
  -- As in `SetsAlg.agda`, the set judgment is proved at the LARGEST set, and
  -- the rules' downward closure recovers every smaller one.

  Typ : Vec Sort γ → Vec Behav δ → NProc γ δ → Pred
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

  Advances : Part → Pred → Set
  Advances P 𝒮 = ∀ {u α v} → 𝒮 u → u -< α >-> v → P ∉α α → 𝒮 v

  waitStep1 :
    ∀ {P}{𝒮 : Pred}
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
    ∀ {P}{𝒮 : Pred}
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

  -- ══════════════════════════════════════════════════════════════════
  --  Visited vectors as sets, as in `SetsEquiv.agda`
  -- ══════════════════════════════════════════════════════════════════

  Vof : ∀ {ξ} → Vec Behav ξ → Pred
  Vof Ξ s = ∃[ X ] (lu Ξ X ~ s)

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
  EndL : Part → Pred
  EndL P u = ¬ P ∈T u

  endL/closed : ∀ {P} → Closed (EndL P)
  endL/closed G~H x inT = x (∈~ (~sym G~H) inT)

  endL/adv : ∀ {P} → Advances P (EndL P)
  endL/adv x gr _ inT = x (in/later gr inT)

  ---------------------------------------------------------------------
  -- `∅`: `s/end`'s `done` must hold at EVERY state of the set, not just
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
  endChase (_ , _ , tr/step gr₁ _ , here p) (skip/step _ na _) =
    ∉c→¬∈c (na gr₁) p
  endChase (_ , _ , tr/step gr₁ tr , there mem) std@(skip/step _ _ ktd) =
    endChase (_ , _ , tr , mem) (endUnfold std (ktd gr₁))

  -- ══════════════════════════════════════════════════════════════════
  --  The four leaf families
  -- ══════════════════════════════════════════════════════════════════

  module _ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ} where

    ---------------------------------------------------------------------
    -- send
    ---------------------------------------------------------------------

    SendL :
      ∀ {I} → Part → Part → Fin (suc I) → Sort → Proc γ δ → Pred
    SendL P Q i S Pr u =
      ∃[ u′ ] (u -< P ⟶ Q # i < S > >-> u′) × Typ Γ Δ (P ◂ Pr) u′

    sendL/closed :
      ∀ {I P Q}{i : Fin (suc I)}{S}{Pr} → Closed (SendL P Q i S Pr)
    sendL/closed G~H (_ , gr , td) =
      _ , ~L→ G~H gr , typ/closed (~L→~ G~H gr) td

    sendL/adv :
      ∀ {I P Q}{i : Fin (suc I)}{S}{Pr} → Advances P (SendL P Q i S Pr)
    sendL/adv (_ , gr , td) grα P∉α
      with skip/advance (one grα P∉α) gr (∈S refl)
    ... | _ , gr′ , tr = _ , gr′ , t/unskip tr td

    ---------------------------------------------------------------------
    -- recv
    ---------------------------------------------------------------------

    RecvL :
      ∀ {I} → Part → Part → Vec (Proc (suc γ) δ) (suc I) → Pred
    RecvL {I} P Q Br u =
      (Σ[ j ∈ Fin (suc I) ] ∃[ U ] ∃[ t ] (u -< P ⟶ Q # j < U > >-> t))
      × (∀ {j U t} → u -< P ⟶ Q # j < U > >-> t
                   → Typ (U ∷ Γ) Δ (Q ◂ lu Br j) t)

    recvL/closed :
      ∀ {I P Q}{Br : Vec (Proc (suc γ) δ) (suc I)} → Closed (RecvL P Q Br)
    recvL/closed G~H ((j , U , _ , gr) , k) =
      (j , U , _ , ~L→ G~H gr) ,
      λ gr′ → typ/closed (~R→~ G~H gr′) (k (~R→ G~H gr′))

    recvL/adv :
      ∀ {I P Q}{Br : Vec (Proc (suc γ) δ) (suc I)} → Advances Q (RecvL P Q Br)
    recvL/adv ((j , U , _ , gr) , k) grα Q∉α
      with skip/advance (one grα Q∉α) gr (∈R refl)
    ... | _ , gr′ , _ =
      (j , U , _ , gr′) ,
      λ gr″ →
        let _ , gr₀ , tr₀ = branch/before (one grα Q∉α) gr gr″
        in t/unskip tr₀ (k gr₀)

    ---------------------------------------------------------------------
    -- var and rec: both `Reach₀`, so both advance by `skip/cat`
    ---------------------------------------------------------------------

    reach₀/adv :
      ∀ {P}{𝒜 : Pred} → Advances P (Reach₀ P 𝒜)
    reach₀/adv (a , a∈ , tr) grα P∉α =
      a , a∈ , skip/cat tr (one grα P∉α)

    -- The `rec` anchor family: the body typed at its own anchor.  This is
    -- exactly `s/rec`'s `𝒜`, and `Check/Sets.agda` decides membership in
    -- it directly, so it stays free of anything else.
    RecA : ∀ {P} → Proc γ (suc δ) → Pred
    RecA {P = P} Pr W = Typ Γ (W ∷ Δ) (P ◂ Pr) W

    recA/closed :
      ∀ {P}{Pr : Proc γ (suc δ)} → Closed (RecA {P = P} Pr)
    recA/closed W~W′ td =
      td/bisim (~ᵛ/∷ W~W′ ~ᵛ-refl) W~W′ td

    -- `rec`'s guardedness, as its own constant family — the same trick as
    -- `IfE`.  `s/rec` needs it as a single state-free fact, and keeping it
    -- OUT of `RecA` is what lets `RecA` stay the plain anchor set.
    RecG : Proc γ (suc δ) → Pred
    RecG Pr _ = MessageGuarded Pr

    recG/closed : ∀ {Pr : Proc γ (suc δ)} → Closed (RecG Pr)
    recG/closed _ guarded = guarded

    recG/adv : ∀ {P}{Pr : Proc γ (suc δ)} → Advances P (RecG Pr)
    recG/adv guarded _ _ = guarded

    ---------------------------------------------------------------------
    -- The three "one state-free fact" families.  Each is a plain `Pred`,
    -- so `waitFind` on it lands on the fact itself with nothing left to
    -- unwrap — which is the whole point (see `waitFind`).
    ---------------------------------------------------------------------

    -- Sort-agnostic send: `s/send` needs ONE sort, fixed outside the set,
    -- but `sendWait` already needs that sort to build its family.  So the
    -- sort is existential here, extracted once, and `sendWait` is then run
    -- at the sort found.  `⊢e-unique` is what makes "the sort found" and
    -- "every leaf's sort" the same thing.
    SendE :
      ∀ {I} → Part → Part → Fin (suc I) → Exp γ → Proc γ δ → Pred
    SendE P Q i E Pr u =
      Σ[ S ∈ Sort ]
        ∃[ u′ ] (Γ ⊢e E ∶ S) × (u -< P ⟶ Q # i < S > >-> u′)
              × Typ Γ Δ (P ◂ Pr) u′

    sendE/closed :
      ∀ {I P Q}{i : Fin (suc I)}{E}{Pr} → Closed (SendE P Q i E Pr)
    sendE/closed G~H (S , _ , etd , gr , td) =
      S , _ , etd , ~L→ G~H gr , typ/closed (~L→~ G~H gr) td

    sendE/adv :
      ∀ {I P Q}{i : Fin (suc I)}{E}{Pr} → Advances P (SendE P Q i E Pr)
    sendE/adv (S , _ , etd , gr , td) grα P∉α
      with skip/advance (one grα P∉α) gr (∈S refl)
    ... | _ , gr′ , tr = S , _ , etd , gr′ , t/unskip tr td

    -- `if`: the guard's typing, constant in the state.
    IfE : Exp γ → Pred
    IfE E _ = Γ ⊢e E ∶ s/bool

    ifE/closed : ∀ {E} → Closed (IfE E)
    ifE/closed _ etd = etd

    ifE/adv : ∀ {P}{E} → Advances P (IfE E)
    ifE/adv etd _ _ = etd

    -- (`EndL`, the `∅` family, is above — it mentions neither `Γ` nor `Δ`,
    -- and leaving it in this block would make those phantom parameters of
    -- every use, which nothing can then solve.)

  -- ══════════════════════════════════════════════════════════════════
  --  `⊢p` derivation ⟶ `Wait`, one family at a time
  -- ══════════════════════════════════════════════════════════════════
  --
  -- Each pair is mutual: the derivation walker handles `t/send`-style leaves,
  -- `t/unskip` (follow the run) and `t/skip` (hand off to the tree walker); the
  -- tree walker mirrors `⊢skip` onto `WaitV` exactly as `SetsEquiv.agda`'s
  -- `skip⇒waitV` does, and calls back at every `skip/main`.

  module _ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ} where

    mutual

      sendWait :
        ∀ {I P Q}{i : Fin (suc I)}{S E}{Pr : Proc γ δ}{G}
        → Γ ⊢e E ∶ S
        → Γ & Δ ⊢p P ◂ Q ! i < E >∙ Pr ∶ G
        → WaitV P (SendL {Γ = Γ} {Δ = Δ} P Q i S Pr) (λ _ → ⊥) G

      sendWait etd (t/send gr etd′ td)
        rewrite ⊢e-unique etd′ etd = wv/leaf (_ , gr , td)

      sendWait etd (t/unskip tr td) =
        waitFollow sendL/closed sendL/adv (sendWait etd td) tr

      sendWait etd (t/skip std) =
        waitV/mono (λ v → ⊥-elim′ (vof/nil v)) (sendTree etd std)
        where
          ⊥-elim′ : ∀ {A : Set} → ⊥ → A
          ⊥-elim′ ()

      sendTree :
        ∀ {ξ}{Ξ : Vec Behav ξ}{I P Q}{i : Fin (suc I)}{S E}{Pr : Proc γ δ}{G}
        → Γ ⊢e E ∶ S
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ Q ! i < E >∙ Pr ∶ G
        → WaitV P (SendL {Γ = Γ} {Δ = Δ} P Q i S Pr) (Vof Ξ) G

      sendTree etd (skip/main td) =
        waitV/mono (λ ()) (sendWait etd td)

      sendTree etd (skip/step gr na ktd) =
        wv/step na gr (λ gr′ → waitV/mono vof/cons (sendTree etd (ktd gr′)))

      sendTree etd (skip/cycle {X = X} eq inT) =
        wv/cycle (_ , (X , ~refl) , eq) inT

    ---------------------------------------------------------------------
    -- recv
    ---------------------------------------------------------------------

    mutual

      recvWait :
        ∀ {I P Q}{Br : Vec (Proc (suc γ) δ) (suc I)}{G}
        → Γ & Δ ⊢p Q ◂ Σ P ？· Br ∶ G
        → WaitV Q (RecvL {Γ = Γ} {Δ = Δ} P Q Br) (λ _ → ⊥) G

      recvWait (t/recv gr conts) =
        wv/leaf ((_ , _ , _ , gr) , conts)

      recvWait {Br = Br} (t/unskip tr td) =
        waitFollow (recvL/closed {Br = Br}) (recvL/adv {Br = Br}) (recvWait td) tr

      recvWait (t/skip std) =
        waitV/mono (λ v → ⊥-elim′ (vof/nil v)) (recvTree std)
        where
          ⊥-elim′ : ∀ {A : Set} → ⊥ → A
          ⊥-elim′ ()

      recvTree :
        ∀ {ξ}{Ξ : Vec Behav ξ}{I P Q}{Br : Vec (Proc (suc γ) δ) (suc I)}{G}
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip Q ◂ Σ P ？· Br ∶ G
        → WaitV Q (RecvL {Γ = Γ} {Δ = Δ} P Q Br) (Vof Ξ) G

      recvTree (skip/main td) =
        waitV/mono (λ ()) (recvWait td)

      recvTree (skip/step gr na ktd) =
        wv/step na gr (λ gr′ → waitV/mono vof/cons (recvTree (ktd gr′)))

      recvTree (skip/cycle {X = X} eq inT) =
        wv/cycle (_ , (X , ~refl) , eq) inT

    ---------------------------------------------------------------------
    -- var
    ---------------------------------------------------------------------

    mutual

      varWait :
        ∀ {P}{X : Fin δ}{G}
        → Γ & Δ ⊢p P ◂ v X ∶ G
        → WaitV P (Reach₀ P ⌈ lu Δ X ⌉) (λ _ → ⊥) G

      varWait (t/var eq) =
        wv/leaf (_ , eq , skip/refl)

      varWait {P = P} {X = X} (t/unskip tr td) =
        waitFollow {P = P} {𝒮 = Reach₀ P ⌈ lu Δ X ⌉}
          (reach₀/~ (⌈⌉/closed {W = lu Δ X}))
          (reach₀/adv {γ = γ} {δ = δ} {Γ = Γ} {Δ = Δ} {P = P} {𝒜 = ⌈ lu Δ X ⌉})
          (varWait td) tr

      varWait (t/skip std) =
        waitV/mono (λ v → ⊥-elim′ (vof/nil v)) (varTree std)
        where
          ⊥-elim′ : ∀ {A : Set} → ⊥ → A
          ⊥-elim′ ()

      varTree :
        ∀ {ξ}{Ξ : Vec Behav ξ}{P}{X : Fin δ}{G}
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ v X ∶ G
        → WaitV P (Reach₀ P ⌈ lu Δ X ⌉) (Vof Ξ) G

      varTree (skip/main td) =
        waitV/mono (λ ()) (varWait td)

      varTree (skip/step gr na ktd) =
        wv/step na gr (λ gr′ → waitV/mono vof/cons (varTree (ktd gr′)))

      varTree (skip/cycle {X = X} eq inT) =
        wv/cycle (_ , (X , ~refl) , eq) inT

    ---------------------------------------------------------------------
    -- rec
    ---------------------------------------------------------------------

    mutual

      recWait :
        ∀ {P}{Pr : Proc γ (suc δ)}{G}
        → Γ & Δ ⊢p P ◂ rec Pr ∶ G
        → WaitV P (Reach₀ P (RecA {P = P} Pr)) (λ _ → ⊥) G

      recWait (t/rec guarded td) =
        wv/leaf (_ , td , skip/refl)

      recWait {P = P} {Pr = Pr} (t/unskip tr td) =
        waitFollow {P = P} {𝒮 = Reach₀ P (RecA {P = P} Pr)}
          (reach₀/~ (recA/closed {P = P} {Pr = Pr}))
          (reach₀/adv {γ = γ} {δ = δ} {Γ = Γ} {Δ = Δ} {P = P} {𝒜 = RecA {P = P} Pr})
          (recWait td) tr

      recWait (t/skip std) =
        waitV/mono (λ v → ⊥-elim′ (vof/nil v)) (recTree std)
        where
          ⊥-elim′ : ∀ {A : Set} → ⊥ → A
          ⊥-elim′ ()

      recTree :
        ∀ {ξ}{Ξ : Vec Behav ξ}{P}{Pr : Proc γ (suc δ)}{G}
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ rec Pr ∶ G
        → WaitV P (Reach₀ P (RecA {P = P} Pr)) (Vof Ξ) G

      recTree (skip/main td) =
        waitV/mono (λ ()) (recWait td)

      recTree (skip/step gr na ktd) =
        wv/step na gr (λ gr′ → waitV/mono vof/cons (recTree (ktd gr′)))

      recTree (skip/cycle {X = X} eq inT) =
        wv/cycle (_ , (X , ~refl) , eq) inT

    ---------------------------------------------------------------------
    -- The same walk again, at the three "one state-free fact" families.
    -- Identical in shape to `sendWait`/`sendTree`: a `t/skip` hands off to
    -- the tree walker, `t/unskip` follows the run, and a `skip/cycle`
    -- becomes a `wv/cycle` verbatim.  `waitFind` is what reads the fact
    -- back out afterwards.
    ---------------------------------------------------------------------

    mutual

      sendEWait :
        ∀ {I P Q}{i : Fin (suc I)}{E}{Pr : Proc γ δ}{G}
        → Γ & Δ ⊢p P ◂ Q ! i < E >∙ Pr ∶ G
        → WaitV P (SendE {Γ = Γ} {Δ = Δ} P Q i E Pr) (λ _ → ⊥) G

      sendEWait (t/send gr etd td) =
        wv/leaf (_ , _ , etd , gr , td)

      sendEWait {E = E} {Pr = Pr} (t/unskip tr td) =
        waitFollow sendE/closed sendE/adv (sendEWait td) tr

      sendEWait (t/skip std) =
        waitV/mono (λ v → ⊥-elim′ (vof/nil v)) (sendETree std)
        where
          ⊥-elim′ : ∀ {A : Set} → ⊥ → A
          ⊥-elim′ ()

      sendETree :
        ∀ {ξ}{Ξ : Vec Behav ξ}{I P Q}{i : Fin (suc I)}{E}{Pr : Proc γ δ}{G}
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ Q ! i < E >∙ Pr ∶ G
        → WaitV P (SendE {Γ = Γ} {Δ = Δ} P Q i E Pr) (Vof Ξ) G

      sendETree (skip/main td) =
        waitV/mono (λ ()) (sendEWait td)

      sendETree (skip/step gr na ktd) =
        wv/step na gr (λ gr′ → waitV/mono vof/cons (sendETree (ktd gr′)))

      sendETree (skip/cycle {X = X} eq inT) =
        wv/cycle (_ , (X , ~refl) , eq) inT

    mutual

      recGWait :
        ∀ {P}{Pr : Proc γ (suc δ)}{G}
        → Γ & Δ ⊢p P ◂ rec Pr ∶ G
        → WaitV P (RecG {Γ = Γ} {Δ = Δ} Pr) (λ _ → ⊥) G

      recGWait (t/rec guarded _) = wv/leaf guarded

      recGWait {P = P} {Pr = Pr} (t/unskip tr td) =
        waitFollow {P = P} {𝒮 = RecG {Γ = Γ} {Δ = Δ} Pr}
          (recG/closed {γ = γ} {δ = δ} {Γ = Γ} {Δ = Δ} {Pr = Pr})
          (recG/adv {γ = γ} {δ = δ} {Γ = Γ} {Δ = Δ} {P = P} {Pr = Pr})
          (recGWait td) tr

      recGWait (t/skip std) =
        waitV/mono (λ v → ⊥-elim′ (vof/nil v)) (recGTree std)
        where
          ⊥-elim′ : ∀ {A : Set} → ⊥ → A
          ⊥-elim′ ()

      recGTree :
        ∀ {ξ}{Ξ : Vec Behav ξ}{P}{Pr : Proc γ (suc δ)}{G}
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ rec Pr ∶ G
        → WaitV P (RecG {Γ = Γ} {Δ = Δ} Pr) (Vof Ξ) G

      recGTree (skip/main td) =
        waitV/mono (λ ()) (recGWait td)

      recGTree (skip/step gr na ktd) =
        wv/step na gr (λ gr′ → waitV/mono vof/cons (recGTree (ktd gr′)))

      recGTree (skip/cycle {X = X} eq inT) =
        wv/cycle (_ , (X , ~refl) , eq) inT

    mutual

      ifEWait :
        ∀ {P E}{A B : Proc γ δ}{G}
        → Γ & Δ ⊢p P ◂ ifp E then A else B ∶ G
        → WaitV P (IfE {Γ = Γ} {Δ = Δ} E) (λ _ → ⊥) G

      ifEWait (t/if etd _ _) = wv/leaf etd

      ifEWait {P = P} {E = E} (t/unskip tr td) =
        waitFollow {P = P} {𝒮 = IfE {Γ = Γ} {Δ = Δ} E}
          (ifE/closed {γ = γ} {δ = δ} {Γ = Γ} {Δ = Δ} {E = E})
          (ifE/adv {γ = γ} {δ = δ} {Γ = Γ} {Δ = Δ} {P = P} {E = E})
          (ifEWait td) tr

      ifEWait (t/skip std) =
        waitV/mono (λ v → ⊥-elim′ (vof/nil v)) (ifETree std)
        where
          ⊥-elim′ : ∀ {A : Set} → ⊥ → A
          ⊥-elim′ ()

      ifETree :
        ∀ {ξ}{Ξ : Vec Behav ξ}{P E}{A B : Proc γ δ}{G}
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ ifp E then A else B ∶ G
        → WaitV P (IfE {Γ = Γ} {Δ = Δ} E) (Vof Ξ) G

      ifETree (skip/main td) =
        waitV/mono (λ ()) (ifEWait td)

      ifETree (skip/step gr na ktd) =
        wv/step na gr (λ gr′ → waitV/mono vof/cons (ifETree (ktd gr′)))

      ifETree (skip/cycle {X = X} eq inT) =
        wv/cycle (_ , (X , ~refl) , eq) inT

    mutual

      endWait :
        ∀ {P}{G}
        → Γ & Δ ⊢p P ◂ ∅ ∶ G
        → WaitV P (EndL P) (λ _ → ⊥) G

      endWait (t/end done) = wv/leaf done

      endWait {P = P} (t/unskip tr td) =
        waitFollow {P = P} {𝒮 = EndL P} endL/closed endL/adv (endWait td) tr

      endWait (t/skip std) =
        waitV/mono (λ v → ⊥-elim′ (vof/nil v)) (endTree std)
        where
          ⊥-elim′ : ∀ {A : Set} → ⊥ → A
          ⊥-elim′ ()

      endTree :
        ∀ {ξ}{Ξ : Vec Behav ξ}{P}{G}
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ ∅ ∶ G
        → WaitV P (EndL P) (Vof Ξ) G

      endTree (skip/main td) =
        waitV/mono (λ ()) (endWait td)

      endTree (skip/step gr na ktd) =
        wv/step na gr (λ gr′ → waitV/mono vof/cons (endTree (ktd gr′)))

      endTree (skip/cycle {X = X} eq inT) =
        wv/cycle (_ , (X , ~refl) , eq) inT

    ---------------------------------------------------------------------
    -- `if`: splitting a derivation into its two branches, AT THE SAME
    -- STATE.  Unlike everything above this needs no `Wait` and no leaf
    -- hunting at all: the result is a TREE of the same shape, so a
    -- `skip/cycle` is copied across verbatim — it carries no branch data
    -- to split.  `s/if` takes no `Wait` premise (D4), which is exactly why
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
  --  `⊢p` ⟶ `⊢set`, at the largest set
  -- ══════════════════════════════════════════════════════════════════
  --
  -- Stated at `Typ` for the same reason `alg⇒set` is stated at `Alg`:
  -- `s/send`'s continuation set has to cover the continuation state of
  -- EVERY leaf at once, which no singleton does.  `set/mono` recovers the
  -- smaller sets, `⌈ G ⌉` included.
  --
  -- The recursion is on the PROCESS, not the derivation: the derivation
  -- each case needs comes out of `waitFind` and is not a subterm of the
  -- one it came from.  `typBr` is the companion that makes `lu Br j`
  -- structural.
  --
  -- Only `send` and `rec` consult the given derivation at all, and only
  -- for the one state-free fact their rule carries (the sort, the
  -- guardedness).  Everything else — the whole graph walk — is the `sub`
  -- field, and that is `sendWait`/`recvWait`/`varWait`/`recWait`, which
  -- take the derivation at each state as it comes.

  mutual

    typing⇒set :
      ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{P}(Pr : Proc γ δ){G}
      → Γ & Δ ⊢p P ◂ Pr ∶ G
      → Γ & Δ ⊢ P ◂ Pr ∶ Typ Γ Δ (P ◂ Pr)

    typing⇒set {P = P} (Q ! i < E >∙ Pr) td
      with waitFind (Q ! i < E >∙ Pr) (sendEWait td)
    ... | _ , _ , _ , etd , _ , cont =
      s/send etd (typing⇒set Pr cont) typ/closed (sendWait etd)

    typing⇒set (Σ Q ？· Br) td =
      s/recv (λ {j} w → typBr Br j w) typ/closed recvWait

    typing⇒set {P = P} (ifp E then A else B) td
      with waitFind (ifp E then A else B) (ifEWait td)
    ... | _ , etd =
      s/if etd
        (set/mono ifTrue  (typing⇒set A (ifTrue td)))
        (set/mono ifFalse (typing⇒set B (ifFalse td)))

    typing⇒set ∅ td = s/end endNotin

    typing⇒set (v X) td = s/var varWait

    typing⇒set {P = P} (rec Pr) td
      with waitFind (rec Pr) (recGWait td)
    ... | _ , guarded =
      s/rec guarded
        (λ aW → set/mono (λ W~s → typ/closed W~s aW) (typing⇒set Pr aW))
        recWait

    -- Makes `lu Br j` structural: `Br` shrinks going in, the branch shrinks
    -- coming out.
    typBr :
      ∀ {γ δ n}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{Q}
        (Br : Vec (Proc (suc γ) δ) n)(j : Fin n){U t}
      → (U ∷ Γ) & Δ ⊢p Q ◂ lu Br j ∶ t
      → (U ∷ Γ) & Δ ⊢ Q ◂ lu Br j ∶ Typ (U ∷ Γ) Δ (Q ◂ lu Br j)

    typBr (B ∷ Bs) zero    w = typing⇒set B w
    typBr (B ∷ Bs) (suc j) w = typBr Bs j w

  -- ══════════════════════════════════════════════════════════════════
  --  The boundary `Safety/` uses
  -- ══════════════════════════════════════════════════════════════════
  --
  -- `⊢s` is stated over `⊢p`, so coming IN needs `⊢p → ⊢set`; this is it,
  -- and it no longer goes anywhere near `⊢a`.  Going OUT is
  -- `SetsDeclarative.agda`'s `⊨⇒typing`.

  td⇒⊨ :
    ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{P}{Pr : Proc γ δ}{G}
    → Γ & Δ ⊢p P ◂ Pr ∶ G
    → Γ & Δ ⊨ P ◂ Pr ∶ G

  td⇒⊨ {Pr = Pr} td = _ , typing⇒set Pr td , td
