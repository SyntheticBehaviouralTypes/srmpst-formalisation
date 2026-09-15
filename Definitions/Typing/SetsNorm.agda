{-# OPTIONS --guardedness #-}

-- `⊢p → ⊢set` DIRECTLY.  With `SetsDeclarative.agda`'s converse this is the
-- whole equivalence between the two rule sets, and `⊢a` is no longer needed by
-- anything — which is the point: there are TWO systems, the declarative one and
-- the set-based one, and nothing in between.
--
-- This replaces `Definitions/Typing/Norm.agda` (830 lines).  It is shorter for
-- one structural reason: `norm`'s bulk is its `t/skip` case, which has to walk
-- an accumulated `¬P` trace INTO a skip tree (`cancel/unskip`, `MainLeaf`,
-- `LeafAlg`, `leafAlg/unfold-cycle`, …), re-rooting the tree as it goes.  Here
-- that re-rooting is `waitV/unfold-top` (`Typing/Sets.agda`), so the trace is
-- handled once and generically, by `waitFollow`, and the trace parameter
-- disappears from the recursion entirely: `t/unskip` just follows.
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

open import Data.Nat using (ℕ; suc)

open import Data.Fin using (Fin; zero; suc)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_)

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Empty using (⊥)

open import Relation.Binary.PropositionalEquality using (refl)

open import Definitions.Typing

module Definitions.Typing.SetsNorm
  {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where

  open module M = MPST(wb)
  open M

  open import Definitions.Typing.Sets wb
  open import Definitions.Typing.Properties wb
    using (td/bisim; skip/bisim-back)

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

    RecA : ∀ {P} → Proc γ (suc δ) → Pred
    RecA {P} Pr W = Typ Γ (W ∷ Δ) (P ◂ Pr) W

    recA/closed :
      ∀ {P}{Pr : Proc γ (suc δ)} → Closed (RecA {P} Pr)
    recA/closed W~W′ td =
      td/bisim (~ᵛ/∷ W~W′ ~ᵛ-refl) W~W′ td

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
