{-# OPTIONS --guardedness #-}

-- Which multi-role processes does the checker accept?  `orig G` decides
-- `wellBehaved?`/`synchronous?` of `G`; `view G Ps` decides `wellBehaved?`
-- of `Ps`'s view graph; `TC` type-checks code for `Ps` against it.
-- Graphs are copied from `Examples/` and `Tests/`; every verdict is forced
-- by `refl`.

module Tests.Quotient where

open import Definitions.Expr.Syntax
import Data.Bool as Bool
open import Data.Bool using (Bool; if_then_else_)
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
  open import Definitions.Actions 3
  open import Definitions.Proc 3 hiding (rec; _⇐_？·_)
  open import Definitions.Proc.Syntax 3
  open import Utils.Branch using (⟪_⟫; _↦_; _∣_)
  open Judge 3

  A B C : Fin 3
  A = 0F
  B = 1F
  C = 2F

  -- labels of the protocols below, by their example
  token auth item price notify announce value : Fin 1
  token    = 0F
  auth     = 0F
  item     = 0F
  price    = 0F
  notify   = 0F
  announce = 0F
  value    = 0F

  login passwd split yes buy accept asNat cancel quit no reject asBool : Fin 2
  login  = 0F
  passwd = 0F
  split  = 0F
  yes    = 0F
  buy    = 0F
  accept = 0F
  asNat  = 0F
  cancel = 1F
  quit   = 1F
  no     = 1F
  reject = 1F
  asBool = 1F

  AB AC BC : _
  AB = ⁅ A ⁆ ∪ ⁅ B ⁆
  AC = ⁅ A ⁆ ∪ ⁅ C ⁆
  BC = ⁅ B ⁆ ∪ ⁅ C ⁆

  -- Examples/RoundRobin.agda, NonRecursive: A → B → C → A.
  module RoundRobin where
    round : OpenGraph 0
    round =
      A ⟶ ⁅ B ⁆ # token < s/bool > ∙
      B ⟶ ⁅ C ⁆ # token < s/bool > ∙
      C ⟶ ⁅ A ⁆ # token < s/bool > ∙ end

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
    oauth =
      ⟪ S′ ⟶ ⁅ C′ ⁆ # login < s/nat >  ∙ C′ ⟶ ⁅ A′ ⁆ # passwd < s/nat > ∙
                                         A′ ⟶ ⁅ S′ ⁆ # auth < s/bool > ∙ end
      ∣ S′ ⟶ ⁅ C′ ⁆ # cancel < s/nat > ∙ C′ ⟶ ⁅ A′ ⁆ # quit < s/bool > ∙ end
      ⟫

    _ : orig oauth ≡ ok
    _ = refl
    _ : view oauth AB ≡ ok
    _ = refl
    _ : view oauth AC ≡ ok
    _ = refl
    _ : view oauth BC ≡ ok
    _ = refl

  -- Examples/Rec2Buy.agda (A, B, S): `S` quotes both buyers.
  module Rec2Buy where
    S : Fin 3
    S = C

    rec2buy : OpenGraph 0
    rec2buy =
      A ⟶ ⁅ S ⁆ # item < s/nat > ∙
      S ⟶ AB # price < s/nat > ∙
      μ X ·
        ⟪ A ⟶ ⁅ B ⁆ # split < s/nat >   ∙
            ⟪ B ⟶ ⁅ A ⁆ # yes < s/nat > ∙ A ⟶ ⁅ S ⁆ # buy < s/unit > ∙ end
            ∣ B ⟶ ⁅ A ⁆ # no < s/unit > ∙ X
            ⟫
        ∣ A ⟶ ⁅ B ⁆ # cancel < s/unit > ∙ A ⟶ ⁅ S ⁆ # quit < s/unit > ∙ end
        ⟫

    -- {A,B}: the `A⟶B`, `B⟶A` loop is an internal τ-cycle; its exits are
    -- `A⟶S` buy / quit.
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
      ⟪ A ⟶ ⁅ B ⁆ # notify < s/unit > ∙ A ⟶ ⁅ C ⁆ # notify < s/unit > ∙ end
      ∣ A ⟶ ⁅ C ⁆ # notify < s/unit > ∙ A ⟶ ⁅ B ⁆ # notify < s/unit > ∙ end
      ⟫

    -- {A,B}: `A→B` is internal; `A` sends to `C`, before or after it.
    ab : Proc 0 0
    ab = A ⇒ ⁅ C ⁆ ! notify < unit >∙ ∅

    -- {B,C}: two receives from `A` at different own roles; `A` decides the
    -- order, the code has to commit to one.
    bc₁ bc₂ : Proc 0 0
    bc₁ = B ⇐ A ？· ⟪ notify ↦ C ⇐ A ？· ⟪ notify ↦ ∅ ⟫ ⟫
    bc₂ = C ⇐ A ？· ⟪ notify ↦ B ⇐ A ？· ⟪ notify ↦ ∅ ⟫ ⟫

    _ : orig nosyn ≡ ok
    _ = refl
    _ : view nosyn AB ≡ ok
    _ = refl
    _ : view nosyn AC ≡ ok
    _ = refl
    -- The {B,C} view is fine; the race is seen at typing (`Focus`).
    _ : view nosyn BC ≡ ok
    _ = refl

    _ : TC nosyn AB ab ≡ Bool.true
    _ = refl
    _ : TC nosyn BC bc₁ ≡ Bool.false
    _ = refl
    _ : TC nosyn BC bc₂ ≡ Bool.false
    _ = refl

  -- Examples/CounterExamples.agda: A → B (choice), B → C (forward).
  module Forward where
    round : OpenGraph 0
    round =
      ⟪ A ⟶ ⁅ B ⁆ # accept < s/bool > ∙ B ⟶ ⁅ C ⁆ # accept < s/bool > ∙ end
      ∣ A ⟶ ⁅ B ⁆ # reject < s/bool > ∙ B ⟶ ⁅ C ⁆ # reject < s/bool > ∙ end
      ⟫

    -- {A,C}: one label of the choice (a sender may send fewer), then the
    -- forward from `B`, at both.
    ac : Proc 0 0
    ac = A ⇒ ⁅ B ⁆ ! accept < true >∙
         C ⇐ B ？· ⟪ accept ↦ ∅ ∣ reject ↦ ∅ ⟫

    _ : orig round ≡ ok
    _ = refl
    _ : view round AB ≡ ok
    _ = refl
    _ : view round AC ≡ ok
    _ = refl
    _ : view round BC ≡ ok
    _ = refl

    _ : TC round AC ac ≡ Bool.true
    _ = refl

  -- Tests/Multicast.agda, Once: A ⟶ {B, C}.
  module Multicast where
    g : OpenGraph 0
    g = A ⟶ ⁅ B ⁆ ∪ ⁅ C ⁆ # announce < s/bool > ∙ end

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
      ⟪ A ⟶ ⁅ C ⁆ # asNat < s/unit >  ∙ A ⟶ ⁅ B ⁆ # value < s/nat > ∙ end
      ∣ A ⟶ ⁅ C ⁆ # asBool < s/unit > ∙ A ⟶ ⁅ B ⁆ # value < s/bool > ∙ end
      ⟫

    _ : orig g ≡ ok
    _ = refl
    _ : view g AB ≡ ok
    _ = refl
    -- `A⟶C` is internal, so {A,C}'s view sends `A⟶B` with label `value` at
    -- sort nat and at sort bool: non-deterministic, and no order helps.
    _ : view g AC ≡ notWB
    _ = refl
    _ : view g BC ≡ ok
    _ = refl

-- ══════════════════════════════════════════════════════════════════════
--  Four roles
-- ══════════════════════════════════════════════════════════════════════

module Four where
  open import Definitions.Graph.Algebra 4
  open import Data.Fin.Subset using (⁅_⁆; _∪_)
  open import Definitions.Actions 4
  open import Definitions.Proc 4 hiding (rec; _⇐_？·_)
  open import Definitions.Proc.Syntax 4
  open import Utils.Branch using (⟪_⟫; _↦_; _∣_)
  open Judge 4

  report relay ping pong : Fin 1
  report = 0F
  relay  = 0F
  ping   = 0F
  pong   = 0F

  datum continue left stop right : Fin 2
  datum    = 0F
  continue = 0F
  left     = 0F
  stop     = 1F
  right    = 1F

  -- Examples/RecMW.agda.
  module RecMW where
    M R W1 W2 : Fin 4
    M  = 0F
    R  = 1F
    W1 = 2F
    W2 = 3F

    recmw : OpenGraph 0
    recmw =
      μ X ·
        M ⟶ ⁅ W1 ⁆ # datum < s/nat > ∙
        M ⟶ ⁅ W2 ⁆ # datum < s/nat > ∙
        W1 ⟶ ⁅ R ⁆ # report < s/nat > ∙
        W2 ⟶ ⁅ R ⁆ # report < s/nat > ∙
        ⟪ R ⟶ ⁅ M ⁆ # continue < s/nat > ∙ X
        ∣ R ⟶ ⁅ M ⁆ # stop < s/bool >    ∙ M ⟶ ⁅ W1 ⁆ # stop < s/bool > ∙
                                           M ⟶ ⁅ W2 ⁆ # stop < s/bool > ∙ end
        ⟫

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
      rec X ·
        M ⇒ ⁅ W2 ⁆ ! datum < 0 >∙
        W1 ⇒ ⁅ R ⁆ ! report < 0 >∙
        M ⇐ R ？· ⟪ continue ↦ X
                  ∣ stop     ↦ M ⇒ ⁅ W2 ⁆ ! stop < true >∙ ∅
                  ⟫
    mw1₂ =
      rec X ·
        W1 ⇒ ⁅ R ⁆ ! report < 0 >∙
        M ⇒ ⁅ W2 ⁆ ! datum < 0 >∙
        M ⇐ R ？· ⟪ continue ↦ X
                  ∣ stop     ↦ M ⇒ ⁅ W2 ⁆ ! stop < true >∙ ∅
                  ⟫

    -- Controls without a race: {M,W2} and {W1,R}.
    mw2 w1r : Proc 0 0
    mw2 =
      rec X ·
        M ⇒ ⁅ W1 ⁆ ! datum < 0 >∙
        W2 ⇒ ⁅ R ⁆ ! report < 0 >∙
        M ⇐ R ？· ⟪ continue ↦ X
                  ∣ stop     ↦ M ⇒ ⁅ W1 ⁆ ! stop < true >∙ ∅
                  ⟫
    w1r =
      rec X ·
        W1 ⇐ M ？·
          ⟪ datum ↦ R ⇐ W2 ？·
                      ⟪ report ↦ R ⇒ ⁅ M ⁆ ! continue < 0 >∙ X ⟫
          ∣ stop  ↦ ∅
          ⟫

    -- {W1,W2}: after `M→W1`, `M→W2` (received by `W2`) races `W1→R` (sent
    -- by `W1`): a mixed choice, in either order.
    w12₁ w12₂ : Proc 0 0
    w12₁ =
      rec X ·
        W1 ⇐ M ？·
          ⟪ datum ↦ W1 ⇒ ⁅ R ⁆ ! report < 0 >∙
                    W2 ⇐ M ？·
                      ⟪ datum ↦ W2 ⇒ ⁅ R ⁆ ! report < 0 >∙ X
                      ∣ stop  ↦ ∅
                      ⟫
          ∣ stop  ↦ W2 ⇐ M ？· ⟪ datum ↦ ∅ ∣ stop ↦ ∅ ⟫
          ⟫
    w12₂ =
      rec X ·
        W1 ⇐ M ？·
          ⟪ datum ↦ W2 ⇐ M ？·
                      ⟪ datum ↦ W1 ⇒ ⁅ R ⁆ ! report < 0 >∙
                                W2 ⇒ ⁅ R ⁆ ! report < 0 >∙ X
                      ∣ stop  ↦ ∅
                      ⟫
          ∣ stop  ↦ W2 ⇐ M ？· ⟪ datum ↦ ∅ ∣ stop ↦ ∅ ⟫
          ⟫

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

    _ : TC recmw MW1 mw1₁ ≡ Bool.false
    _ = refl
    _ : TC recmw MW1 mw1₂ ≡ Bool.false
    _ = refl
    _ : TC recmw MW2 mw2 ≡ Bool.true
    _ = refl
    _ : TC recmw W1R w1r ≡ Bool.true
    _ = refl
    _ : TC recmw W1W2 w12₁ ≡ Bool.false
    _ = refl
    _ : TC recmw W1W2 w12₂ ≡ Bool.false
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
    g = A ⟶ ⁅ B ⁆ # relay < s/unit > ∙
        B ⟶ ⁅ C ⁆ # relay < s/unit > ∙
        C ⟶ ⁅ D ⁆ # relay < s/unit > ∙ end

    BC : _
    BC = ⁅ B ⁆ ∪ ⁅ C ⁆

    bc : Proc 0 0
    bc = B ⇐ A ？· ⟪ relay ↦ C ⇒ ⁅ D ⁆ ! relay < unit >∙ ∅ ⟫

    _ : orig g ≡ ok
    _ = refl
    _ : view g BC ≡ ok
    _ = refl
    _ : ⌊ synchronous? (viewGraph (underlying (compile g)) BC) ⌋ ≡ Bool.false
    _ = refl
    _ : TC g BC bc ≡ Bool.true
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
      ⟪ P ⟶ ⁅ Q ⁆ # left < s/unit >  ∙ Q ⟶ ⁅ R ⁆ # left < s/unit > ∙ end
      ∣ P ⟶ ⁅ Q ⁆ # right < s/unit > ∙ Q ⟶ ⁅ R ⁆ # right < s/unit > ∙ end
      ⟫

    PQ : _
    PQ = ⁅ P ⁆ ∪ ⁅ Q ⁆

    -- {P,Q}: the internal choice is made by the send that tells `R`.
    pq : Proc 0 0
    pq = Q ⇒ ⁅ R ⁆ ! right < unit >∙ ∅

    _ : orig told ≡ ok
    _ = refl
    _ : view told PQ ≡ ok
    _ = refl
    _ : TC told PQ pq ≡ Bool.true
    _ = refl

  -- `P → Q . R → S`, as role-level synchronisation demands: both orders.
  module Square where
    P Q R S : Fin 4
    P = 0F
    Q = 1F
    R = 2F
    S = 3F

    square : OpenGraph 0
    square = P ⟶ ⁅ Q ⁆ # ping < s/unit > ∙ R ⟶ ⁅ S ⁆ # pong < s/unit > ∙ end

    PS QR : _
    PS = ⁅ P ⁆ ∪ ⁅ S ⁆
    QR = ⁅ Q ⁆ ∪ ⁅ R ⁆

    -- A mixed choice at state 0 for both blocks, in either order.
    ps₁ ps₂ qr₁ qr₂ : Proc 0 0
    ps₁ = P ⇒ ⁅ Q ⁆ ! ping < unit >∙ S ⇐ R ？· ⟪ pong ↦ ∅ ⟫
    ps₂ = S ⇐ R ？· ⟪ pong ↦ P ⇒ ⁅ Q ⁆ ! ping < unit >∙ ∅ ⟫
    qr₁ = Q ⇐ P ？· ⟪ ping ↦ R ⇒ ⁅ S ⁆ ! pong < unit >∙ ∅ ⟫
    qr₂ = R ⇒ ⁅ S ⁆ ! pong < unit >∙ Q ⇐ P ？· ⟪ ping ↦ ∅ ⟫

    _ : orig square ≡ ok
    _ = refl
    _ : view square PS ≡ ok
    _ = refl
    _ : view square QR ≡ ok
    _ = refl

    _ : TC square PS ps₁ ≡ Bool.false
    _ = refl
    _ : TC square PS ps₂ ≡ Bool.false
    _ = refl
    _ : TC square QR qr₁ ≡ Bool.false
    _ = refl
    _ : TC square QR qr₂ ≡ Bool.false
    _ = refl

-- ══════════════════════════════════════════════════════════════════════
--  Five roles
-- ══════════════════════════════════════════════════════════════════════

module Five where
  open import Definitions.Graph.Algebra 5
  open import Data.Fin.Subset using (⁅_⁆; _∪_)
  open import Definitions.Actions 5
  open import Definitions.Proc 5 hiding (rec; _⇐_？·_)
  open import Definitions.Proc.Syntax 5
  open import Utils.Branch using (⟪_⟫; _↦_; _∣_)
  open Judge 5

  ping warm pong idle : Fin 1
  ping = 0F
  warm = 0F
  pong = 0F
  idle = 0F

  left right : Fin 2
  left  = 0F
  right = 1F

  -- `(P → Q) ∥ (R → T . R → S)` under {P,S}.  `P→Q` and `R→S` are
  -- a mixed choice at state 1, which the idle `R→T` reaches from 0.
  module Race where
    P Q R S T : Fin 5
    P = 0F
    Q = 1F
    R = 2F
    S = 3F
    T = 4F

    g : OpenGraph 0
    g =
        P ⟶ ⁅ Q ⁆ # ping < s/unit > ∙ end
      ∥ R ⟶ ⁅ T ⁆ # warm < s/unit > ∙
        R ⟶ ⁅ S ⁆ # pong < s/unit > ∙ end

    PS : _
    PS = ⁅ P ⁆ ∪ ⁅ S ⁆

    -- Both orders are rejected by `Focus` at state 0.
    ps₁ ps₂ : Proc 0 0
    ps₁ = P ⇒ ⁅ Q ⁆ ! ping < unit >∙ S ⇐ R ？· ⟪ pong ↦ ∅ ⟫
    ps₂ = S ⇐ R ？· ⟪ pong ↦ P ⇒ ⁅ Q ⁆ ! ping < unit >∙ ∅ ⟫

    _ : orig g ≡ ok
    _ = refl
    _ : view g PS ≡ ok
    _ = refl
    _ : TC g PS ps₁ ≡ Bool.false
    _ = refl
    _ : TC g PS ps₂ ≡ Bool.false
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
        ⟪ P ⟶ ⁅ S ⁆ # left < s/unit >  ∙ S ⟶ ⁅ R ⁆ # left < s/unit > ∙ end
        ∣ P ⟶ ⁅ S ⁆ # right < s/unit > ∙ S ⟶ ⁅ R ⁆ # right < s/unit > ∙ end
        ⟫
      ∥ T ⟶ ⁅ U ⁆ # idle < s/unit > ∙ end

    PS : _
    PS = ⁅ P ⁆ ∪ ⁅ S ⁆

    -- {P,S}: the internal choice is made by the send that tells `R`;
    -- `T→U` is an outsider's step.
    ps : Proc 0 0
    ps = S ⇒ ⁅ R ⁆ ! left < unit >∙ ∅

    _ : orig g ≡ ok
    _ = refl
    _ : view g PS ≡ ok
    _ = refl
    _ : TC g PS ps ≡ Bool.true
    _ = refl
