{-# OPTIONS --guardedness #-}

-- Which multi-role processes does the checker accept?  `orig G` decides
-- `wellBehaved?`/`synchronous?` of `G`; `view G Ps` decides `wellBehaved?`
-- of `Ps`'s view graph; `TC` type-checks code for `Ps` against it.
-- Graphs are copied from `Examples/` and `Tests/`; every verdict is forced
-- by `refl`.

module Tests.Quotient where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Vec using ([]; _∷_)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (⌊_⌋; does; True)

open import Definitions.Expr using (s/bool; s/nat; s/unit; val; v/bool; v/nat; v/unit)

data Verdict : Set where
  notWB notSync ok : Verdict

module Judge (N : ℕ) where
  open import Data.Bool using (T)
  open import Definitions.Common N using (PartSet)
  open import Definitions.Proc N using (Proc)
  open import Definitions.Graph.Algebra N using (OpenGraph; compile; underlying)
  open import Definitions.Graph.Decision N using (wellBehaved?; synchronous?)
  open import Definitions.Graph.View N using (viewGraph)
  open import Check using (buildG; typecheck)

  -- The theory itself must be well behaved and synchronous.
  orig : OpenGraph 0 → Verdict
  orig g =
    if ⌊ wellBehaved? (underlying (compile g)) ⌋
    then (if ⌊ synchronous? (underlying (compile g)) ⌋ then ok else notSync)
    else notWB

  view : OpenGraph 0 → PartSet → Verdict
  view g Ps = if ⌊ wellBehaved? (viewGraph (underlying (compile g)) Ps) ⌋ then ok else notWB

  -- Code for block `Ps`, at the initial state of its view (`typecheck`
  -- decides the view too).
  TC : (g : OpenGraph 0)
       {p : True (wellBehaved? (underlying (compile g)))}
       {q : True (synchronous? (underlying (compile g)))}
     → PartSet → Proc 0 0 → Bool
  TC g {p} {q} Ps Pr = does (typecheck (buildG g {p} {q}) Ps Pr)

-- ══════════════════════════════════════════════════════════════════════
--  Three roles
-- ══════════════════════════════════════════════════════════════════════

module Three where
  open import Definitions.Graph.Algebra 3
  open import Data.Fin.Subset using (⁅_⁆; _∪_)
  open import Definitions.Actions 3 renaming (_<_> to mkChoice)
  open import Definitions.Proc 3
  open Judge 3

  A B C : Fin 3
  A = 0F
  B = 1F
  C = 2F

  here : Fin 1
  here = 0F

  lbl0 lbl1 : Fin 2
  lbl0 = 0F
  lbl1 = 1F

  AB AC BC : _
  AB = ⁅ A ⁆ ∪ ⁅ B ⁆
  AC = ⁅ A ⁆ ∪ ⁅ C ⁆
  BC = ⁅ B ⁆ ∪ ⁅ C ⁆

  -- Examples/RoundRobin.agda, NonRecursive: A → B → C → A.
  module RoundRobin where
    round : OpenGraph 0
    round =
      (A ⟶ ⁅ B ⁆ # mkChoice here s/bool) ∙
      ((B ⟶ ⁅ C ⁆ # mkChoice here s/bool) ∙
       ((C ⟶ ⁅ A ⁆ # mkChoice here s/bool) ∙ end))

    _ : orig round ≡ ok
    _ = refl
    _ : view round AB ≡ ok
    _ = refl
    _ : view round AC ≡ ok
    _ = refl
    _ : view round BC ≡ ok
    _ = refl

  -- Examples/OAuth2.agda (S, C, A renamed A, B, C): S→C, C→A, A→S.
  module OAuth2 where
    S′ C′ A′ : Fin 3
    S′ = A
    C′ = B
    A′ = C

    oauth : OpenGraph 0
    oauth = openGraph 4 (node 0F)
      ( ( ((S′ ⟶ ⁅ C′ ⁆ # mkChoice lbl0 s/nat) , node 1F)
        ∷ ((S′ ⟶ ⁅ C′ ⁆ # mkChoice lbl1 s/nat) , node 3F)
        ∷ [] )
      v∷ ( ((C′ ⟶ ⁅ A′ ⁆ # mkChoice lbl0 s/nat) , node 2F) ∷ [] )
      v∷ ( ((A′ ⟶ ⁅ S′ ⁆ # mkChoice here s/bool) , ended) ∷ [] )
      v∷ ( ((C′ ⟶ ⁅ A′ ⁆ # mkChoice lbl1 s/bool) , ended) ∷ [] )
      v∷ v[]
      )

    _ : orig oauth ≡ ok
    _ = refl
    _ : view oauth AB ≡ ok
    _ = refl
    _ : view oauth AC ≡ ok
    _ = refl
    _ : view oauth BC ≡ ok
    _ = refl

  -- Examples/Rec2Buy.agda (A, B, S): `B` and `S` never talk to each other.
  module Rec2Buy where
    S : Fin 3
    S = C

    rec2buy : OpenGraph 0
    rec2buy = openGraph 6 (node 0F)
      (  ( ((A ⟶ ⁅ S ⁆ # mkChoice here s/nat) , node 1F) ∷ [] )
      v∷ ( ((S ⟶ ⁅ A ⁆ # mkChoice here s/nat) , node 2F) ∷ [] )
      v∷ ( ((A ⟶ ⁅ B ⁆ # mkChoice lbl0 s/nat) , node 4F)
         ∷ ((A ⟶ ⁅ B ⁆ # mkChoice lbl1 s/unit) , node 3F)
         ∷ [] )
      v∷ ( ((A ⟶ ⁅ S ⁆ # mkChoice lbl1 s/unit) , ended) ∷ [] )
      v∷ ( ((B ⟶ ⁅ A ⁆ # mkChoice lbl0 s/nat) , node 5F)
         ∷ ((B ⟶ ⁅ A ⁆ # mkChoice lbl1 s/unit) , node 2F)
         ∷ [] )
      v∷ ( ((A ⟶ ⁅ S ⁆ # mkChoice lbl0 s/unit) , ended) ∷ [] )
      v∷ v[]
      )

    -- {A,B}: the `A⟶B`, `B⟶A` loop is an internal τ-cycle; its exits are
    -- `A⟶S` buy / no.
    _ : orig rec2buy ≡ ok
    _ = refl
    _ : view rec2buy AB ≡ ok
    _ = refl
    _ : view rec2buy AC ≡ ok
    _ = refl
    _ : view rec2buy BC ≡ ok
    _ = refl

  -- Examples/NoSynGT.agda: A messages B and C, in either order.
  module NoSynGT where
    nosyn : OpenGraph 0
    nosyn =
      choice
        ((A ⟶ ⁅ B ⁆ # mkChoice here s/unit) ⇒
          ((A ⟶ ⁅ C ⁆ # mkChoice here s/unit) ∙ end))
        ( ((A ⟶ ⁅ C ⁆ # mkChoice here s/unit) ⇒
            ((A ⟶ ⁅ B ⁆ # mkChoice here s/unit) ∙ end))
        ∷ [])

    -- {A,B}: `A→B` is internal; `A` sends to `C`, before or after it.
    ab : Proc 0 0
    ab = A ⇒ ⁅ C ⁆ ! here < val v/unit >∙ ∅

    -- {B,C}: two receives from `A` at different own roles; `A` decides the
    -- order, the code has to commit to one.
    bc₁ bc₂ : Proc 0 0
    bc₁ = B ⇐ A ？· ((C ⇐ A ？· (∅ ∷ [])) ∷ [])
    bc₂ = C ⇐ A ？· ((B ⇐ A ？· (∅ ∷ [])) ∷ [])

    _ : orig nosyn ≡ ok
    _ = refl
    _ : view nosyn AB ≡ ok
    _ = refl
    _ : view nosyn AC ≡ ok
    _ = refl
    -- The {B,C} view is fine; the race is seen at typing (`Focus`).
    _ : view nosyn BC ≡ ok
    _ = refl

    _ : TC nosyn AB ab ≡ true
    _ = refl
    _ : TC nosyn BC bc₁ ≡ false
    _ = refl
    _ : TC nosyn BC bc₂ ≡ false
    _ = refl

  -- Examples/CounterExamples.agda: A → B (choice), B → C (forward).
  module Forward where
    round : OpenGraph 0
    round = openGraph 3 (node 0F)
      ( ( ((A ⟶ ⁅ B ⁆ # mkChoice lbl0 s/bool) , node 1F)
        ∷ ((A ⟶ ⁅ B ⁆ # mkChoice lbl1 s/bool) , node 2F)
        ∷ [] )
      v∷ ( ((B ⟶ ⁅ C ⁆ # mkChoice lbl0 s/bool) , ended) ∷ [] )
      v∷ ( ((B ⟶ ⁅ C ⁆ # mkChoice lbl1 s/bool) , ended) ∷ [] )
      v∷ v[]
      )

    -- {A,C}: one label of the choice (a sender may send fewer), then the
    -- forward from `B`, at both.
    ac : Proc 0 0
    ac = A ⇒ ⁅ B ⁆ ! lbl0 < val (v/bool true) >∙ (C ⇐ B ？· (∅ ∷ ∅ ∷ []))

    _ : orig round ≡ ok
    _ = refl
    _ : view round AB ≡ ok
    _ = refl
    _ : view round AC ≡ ok
    _ = refl
    _ : view round BC ≡ ok
    _ = refl

    _ : TC round AC ac ≡ true
    _ = refl

  -- Tests/Multicast.agda, Once: A ⟶ {B, C}.
  module Multicast where
    g : OpenGraph 0
    g = (A ⟶ (⁅ B ⁆ ∪ ⁅ C ⁆) # mkChoice here s/bool) ∙ end

    _ : orig g ≡ ok
    _ = refl
    _ : view g AB ≡ ok
    _ = refl
    _ : view g AC ≡ ok
    _ = refl
    _ : view g BC ≡ ok
    _ = refl

  -- Tests/LabelSorts.agda: A chooses to C, then sends B a nat or a bool.
  module LabelSorts where
    g : OpenGraph 0
    g =
      choice
        ((A ⟶ ⁅ C ⁆ # mkChoice lbl0 s/unit) ⇒
          ((A ⟶ ⁅ B ⁆ # mkChoice here s/nat) ∙ end))
        ( ((A ⟶ ⁅ C ⁆ # mkChoice lbl1 s/unit) ⇒
            ((A ⟶ ⁅ B ⁆ # mkChoice here s/bool) ∙ end))
        ∷ [])

    _ : orig g ≡ ok
    _ = refl
    _ : view g AB ≡ ok
    _ = refl
    -- `A⟶C` is internal, so {A,C}'s view sends `A⟶B` with label `here` at
    -- sort nat and at sort bool: non-deterministic, and no order helps.
    _ : view g AC ≡ notWB
    _ = refl
    _ : view g BC ≡ ok
    _ = refl

-- ══════════════════════════════════════════════════════════════════════
--  Four roles
-- ══════════════════════════════════════════════════════════════════════

module Four where
  open import Definitions.Graph.Algebra 4 renaming (var to gvar)
  open import Data.Fin.Subset using (⁅_⁆; _∪_)
  open import Definitions.Actions 4 renaming (_<_> to mkChoice)
  open import Definitions.Proc 4
  open Judge 4

  here : Fin 1
  here = 0F

  lbl0 lbl1 : Fin 2
  lbl0 = 0F
  lbl1 = 1F

  -- Examples/RecMW.agda.
  module RecMW where
    M R W1 W2 : Fin 4
    M  = 0F
    R  = 1F
    W1 = 2F
    W2 = 3F

    recmw : OpenGraph 0
    recmw =
      μ ( (M ⟶ ⁅ W1 ⁆ # mkChoice lbl0 s/nat) ∙
          (   ((M ⟶ ⁅ W2 ⁆ # mkChoice lbl0 s/nat) ∙ end)
            ∥ ((W1 ⟶ ⁅ R ⁆ # mkChoice here s/nat) ∙ end)
          ⨾ (W2 ⟶ ⁅ R ⁆ # mkChoice here s/nat) ∙
            choice ((R ⟶ ⁅ M ⁆ # mkChoice lbl0 s/nat) ⇒ gvar 0F)
                   ( ((R ⟶ ⁅ M ⁆ # mkChoice lbl1 s/bool) ⇒
                       ((M ⟶ ⁅ W1 ⁆ # mkChoice lbl1 s/bool) ∙
                        (M ⟶ ⁅ W2 ⁆ # mkChoice lbl1 s/bool) ∙ end))
                   ∷ []) ) )

    MW1 MW2 MR W1W2 W1R W2R : _
    MW1  = ⁅ M ⁆ ∪ ⁅ W1 ⁆
    MW2  = ⁅ M ⁆ ∪ ⁅ W2 ⁆
    MR   = ⁅ M ⁆ ∪ ⁅ R ⁆
    W1W2 = ⁅ W1 ⁆ ∪ ⁅ W2 ⁆
    W1R  = ⁅ W1 ⁆ ∪ ⁅ R ⁆
    W2R  = ⁅ W2 ⁆ ∪ ⁅ R ⁆

    -- {M,W1}: `M→W1` is internal; then `M→W2` and `W1→R` are two sends by
    -- different own roles, in either order.
    mw1₁ mw1₂ : Proc 0 0
    mw1₁ =
      rec (M ⇒ ⁅ W2 ⁆ ! lbl0 < val (v/nat 0) >∙
           (W1 ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙
            (M ⇐ R ？· (v 0F
                       ∷ (M ⇒ ⁅ W2 ⁆ ! lbl1 < val (v/bool true) >∙ ∅)
                       ∷ []))))
    mw1₂ =
      rec (W1 ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙
           (M ⇒ ⁅ W2 ⁆ ! lbl0 < val (v/nat 0) >∙
            (M ⇐ R ？· (v 0F
                       ∷ (M ⇒ ⁅ W2 ⁆ ! lbl1 < val (v/bool true) >∙ ∅)
                       ∷ []))))

    -- Controls without a race: {M,W2} and {W1,R}.
    mw2 w1r : Proc 0 0
    mw2 =
      rec (M ⇒ ⁅ W1 ⁆ ! lbl0 < val (v/nat 0) >∙
           (W2 ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙
            (M ⇐ R ？· (v 0F
                       ∷ (M ⇒ ⁅ W1 ⁆ ! lbl1 < val (v/bool true) >∙ ∅)
                       ∷ []))))
    w1r =
      rec (W1 ⇐ M ？·
            ( (R ⇐ W2 ？· ((R ⇒ ⁅ M ⁆ ! lbl0 < val (v/nat 0) >∙ v 0F) ∷ []))
            ∷ ∅
            ∷ []))

    -- {W1,W2}: after `M→W1`, `M→W2` (received by `W2`) races `W1→R` (sent
    -- by `W1`): a mixed choice, in either order.
    w12₁ w12₂ : Proc 0 0
    w12₁ =
      rec (W1 ⇐ M ？·
            ( (W1 ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙
               (W2 ⇐ M ？· ( (W2 ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙ v 0F)
                           ∷ ∅ ∷ [])))
            ∷ (W2 ⇐ M ？· (∅ ∷ ∅ ∷ []))
            ∷ []))
    w12₂ =
      rec (W1 ⇐ M ？·
            ( (W2 ⇐ M ？· ( (W1 ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙
                             (W2 ⇒ ⁅ R ⁆ ! here < val (v/nat 0) >∙ v 0F))
                           ∷ ∅ ∷ []))
            ∷ (W2 ⇐ M ？· (∅ ∷ ∅ ∷ []))
            ∷ []))

    _ : orig recmw ≡ ok
    _ = refl
    _ : view recmw MW1 ≡ ok
    _ = refl
    _ : view recmw MW2 ≡ ok
    _ = refl
    -- {M,R} is rejected at typing: `M→W2` races `W1→R`.
    _ : view recmw MR ≡ ok
    _ = refl
    _ : view recmw W1W2 ≡ ok
    _ = refl
    _ : view recmw W1R ≡ ok
    _ = refl
    _ : view recmw W2R ≡ ok
    _ = refl

    _ : TC recmw MW1 mw1₁ ≡ false
    _ = refl
    _ : TC recmw MW1 mw1₂ ≡ false
    _ = refl
    _ : TC recmw MW2 mw2 ≡ true
    _ = refl
    _ : TC recmw W1R w1r ≡ true
    _ = refl
    _ : TC recmw W1W2 w12₁ ≡ false
    _ = refl
    _ : TC recmw W1W2 w12₂ ≡ false
    _ = refl

  -- A relay: `A → B . B → C . C → D` under {B,C}.  `B` receives, `B→C`
  -- is internal, `C` sends.  The view is not synchronous (`C→D` appears
  -- after `A→B`, which involves neither `C` nor `D`), and is accepted.
  module Relay where
    open import Definitions.Graph.Decision 4 using (synchronous?)
    open import Definitions.Graph.View 4 using (viewGraph)

    A B C D : Fin 4
    A = 0F
    B = 1F
    C = 2F
    D = 3F

    g : OpenGraph 0
    g = (A ⟶ ⁅ B ⁆ # mkChoice here s/unit) ∙
        (B ⟶ ⁅ C ⁆ # mkChoice here s/unit) ∙
        (C ⟶ ⁅ D ⁆ # mkChoice here s/unit) ∙ end

    BC : _
    BC = ⁅ B ⁆ ∪ ⁅ C ⁆

    bc : Proc 0 0
    bc = B ⇐ A ？· ((C ⇒ ⁅ D ⁆ ! here < val v/unit >∙ ∅) ∷ [])

    _ : orig g ≡ ok
    _ = refl
    _ : view g BC ≡ ok
    _ = refl
    _ : ⌊ synchronous? (viewGraph (underlying (compile g)) BC) ⌋ ≡ false
    _ = refl
    _ : TC g BC bc ≡ true
    _ = refl

  -- An internal choice, told to `R` by one message.
  module InternalChoice where
    P Q R S : Fin 4
    P = 0F
    Q = 1F
    R = 2F
    S = 3F

    told : OpenGraph 0
    told =
      choice
        ((P ⟶ ⁅ Q ⁆ # mkChoice lbl0 s/unit) ⇒
          ((Q ⟶ ⁅ R ⁆ # mkChoice lbl0 s/unit) ∙ end))
        ( ((P ⟶ ⁅ Q ⁆ # mkChoice lbl1 s/unit) ⇒
            ((Q ⟶ ⁅ R ⁆ # mkChoice lbl1 s/unit) ∙ end))
        ∷ [])

    PQ : _
    PQ = ⁅ P ⁆ ∪ ⁅ Q ⁆

    -- {P,Q}: the internal choice is made by the send that tells `R`.
    pq : Proc 0 0
    pq = Q ⇒ ⁅ R ⁆ ! lbl1 < val v/unit >∙ ∅

    _ : orig told ≡ ok
    _ = refl
    _ : view told PQ ≡ ok
    _ = refl
    _ : TC told PQ pq ≡ true
    _ = refl

  -- `P → Q . R → S`, as role-level synchronisation demands: both orders.
  module Square where
    P Q R S : Fin 4
    P = 0F
    Q = 1F
    R = 2F
    S = 3F

    square : OpenGraph 0
    square = openGraph 3 (node 0F)
      ( ( ((P ⟶ ⁅ Q ⁆ # mkChoice here s/unit) , node 1F)
        ∷ ((R ⟶ ⁅ S ⁆ # mkChoice here s/unit) , node 2F)
        ∷ [] )
      v∷ ( ((R ⟶ ⁅ S ⁆ # mkChoice here s/unit) , ended) ∷ [] )
      v∷ ( ((P ⟶ ⁅ Q ⁆ # mkChoice here s/unit) , ended) ∷ [] )
      v∷ v[]
      )

    PS QR : _
    PS = ⁅ P ⁆ ∪ ⁅ S ⁆
    QR = ⁅ Q ⁆ ∪ ⁅ R ⁆

    -- A mixed choice at state 0 for both blocks, in either order.
    ps₁ ps₂ qr₁ qr₂ : Proc 0 0
    ps₁ = P ⇒ ⁅ Q ⁆ ! here < val v/unit >∙ (S ⇐ R ？· (∅ ∷ []))
    ps₂ = S ⇐ R ？· ((P ⇒ ⁅ Q ⁆ ! here < val v/unit >∙ ∅) ∷ [])
    qr₁ = Q ⇐ P ？· ((R ⇒ ⁅ S ⁆ ! here < val v/unit >∙ ∅) ∷ [])
    qr₂ = R ⇒ ⁅ S ⁆ ! here < val v/unit >∙ (Q ⇐ P ？· (∅ ∷ []))

    _ : orig square ≡ ok
    _ = refl
    _ : view square PS ≡ ok
    _ = refl
    _ : view square QR ≡ ok
    _ = refl

    _ : TC square PS ps₁ ≡ false
    _ = refl
    _ : TC square PS ps₂ ≡ false
    _ = refl
    _ : TC square QR qr₁ ≡ false
    _ = refl
    _ : TC square QR qr₂ ≡ false
    _ = refl

-- ══════════════════════════════════════════════════════════════════════
--  Five roles
-- ══════════════════════════════════════════════════════════════════════

module Five where
  open import Definitions.Graph.Algebra 5
  open import Data.Fin.Subset using (⁅_⁆; _∪_)
  open import Definitions.Actions 5 renaming (_<_> to mkChoice)
  open import Definitions.Proc 5
  open Judge 5

  here : Fin 1
  here = 0F

  lbl0 lbl1 : Fin 2
  lbl0 = 0F
  lbl1 = 1F

  -- `(P → Q) ∥ (R → T . R → S)` under {P,S}.  `P→Q` and `R→S` are
  -- a mixed choice at state 2, which the idle `R→T` reaches from 0.
  module Race where
    P Q R S T : Fin 5
    P = 0F
    Q = 1F
    R = 2F
    S = 3F
    T = 4F

    g : OpenGraph 0
    g = openGraph 5 (node 0F)
      ( ( ((P ⟶ ⁅ Q ⁆ # mkChoice here s/unit) , node 1F)
        ∷ ((R ⟶ ⁅ T ⁆ # mkChoice here s/unit) , node 2F)
        ∷ [] )
      v∷ ( ((R ⟶ ⁅ T ⁆ # mkChoice here s/unit) , node 3F) ∷ [] )
      v∷ ( ((P ⟶ ⁅ Q ⁆ # mkChoice here s/unit) , node 3F)
         ∷ ((R ⟶ ⁅ S ⁆ # mkChoice here s/unit) , node 4F)
         ∷ [] )
      v∷ ( ((R ⟶ ⁅ S ⁆ # mkChoice here s/unit) , ended) ∷ [] )
      v∷ ( ((P ⟶ ⁅ Q ⁆ # mkChoice here s/unit) , ended) ∷ [] )
      v∷ v[]
      )

    PS : _
    PS = ⁅ P ⁆ ∪ ⁅ S ⁆

    -- Both orders are rejected by `Focus` at state 0.
    ps₁ ps₂ : Proc 0 0
    ps₁ = P ⇒ ⁅ Q ⁆ ! here < val v/unit >∙ (S ⇐ R ？· (∅ ∷ []))
    ps₂ = S ⇐ R ？· ((P ⇒ ⁅ Q ⁆ ! here < val v/unit >∙ ∅) ∷ [])

    _ : orig g ≡ ok
    _ = refl
    _ : view g PS ≡ ok
    _ = refl
    _ : TC g PS ps₁ ≡ false
    _ = refl
    _ : TC g PS ps₂ ≡ false
    _ = refl

  -- An internal choice next to an outsider's step.
  --   (P → S # 0 . S → R # 0  +  P → S # 1 . S → R # 1)  ∥  T → U
  module InternalThenIdle where
    P S R T U : Fin 5
    P = 0F
    S = 1F
    R = 2F
    T = 3F
    U = 4F

    g : OpenGraph 0
    g =
      ( choice
          ((P ⟶ ⁅ S ⁆ # mkChoice lbl0 s/unit) ⇒
            ((S ⟶ ⁅ R ⁆ # mkChoice lbl0 s/unit) ∙ end))
          ( ((P ⟶ ⁅ S ⁆ # mkChoice lbl1 s/unit) ⇒
              ((S ⟶ ⁅ R ⁆ # mkChoice lbl1 s/unit) ∙ end))
          ∷ []) )
      ∥ ((T ⟶ ⁅ U ⁆ # mkChoice here s/unit) ∙ end)

    PS : _
    PS = ⁅ P ⁆ ∪ ⁅ S ⁆

    -- {P,S}: the internal choice is made by the send that tells `R`;
    -- `T→U` is an outsider's step.
    ps : Proc 0 0
    ps = S ⇒ ⁅ R ⁆ ! lbl0 < val v/unit >∙ ∅

    _ : orig g ≡ ok
    _ = refl
    _ : view g PS ≡ ok
    _ = refl
    _ : TC g PS ps ≡ true
    _ = refl
