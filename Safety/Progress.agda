{-# OPTIONS --guardedness #-}

-- Progress, for processes typed against their local views.
--
-- 1. A block that is not `done` acts somewhere in its view; the first step
--    on that trace not internal to its sender's block is `Active`.
-- 2. The sender's block of an `Active` step is at a send, or has a τ step.
-- 3. Each receiving block is at a matching receive (`recv-head`), or has a
--    τ step.

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Fin using (Fin; zero) renaming (_≟_ to _≟f_; suc to fsuc)
open import Data.Fin.Subset using (_∈_; _∉_)
open import Data.List.Relation.Unary.All
  using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
import Data.List.Relation.Unary.All as All
open import Data.List using (List)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂; [_,_]′)
open import Data.Vec using (Vec; []; replicate; _[_]=_) renaming (lookup to lu)
open import Data.Vec.Properties using (lookup⇒[]=)
open import Function using (_∘_; id)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_; _◅◅_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_; yes; no)

open import Definitions.Expr
open import Definitions.Behav using (BTheory; WellBehaved; Balanced; Synchronous)
open import Definitions.Typing.Declarative using (module MPST)
import Definitions.Proc as A
import Safety.Preservation as Views

module Safety.Progress
  {N : ℕ} {B : BTheory N} (wb : WellBehaved B) (sync : Synchronous B)
  {K : ℕ} (Ρ : A.Assignment N K)
  (wbL   : ∀ j → WellBehaved (Views.Local wb sync Ρ j))
  where

  open import Definitions.Common N
  open import Definitions.Actions N
  open import Definitions.Proc N
  open import Definitions.View B
  open import Definitions.View.Lemmas B wb sync
  open BTheory B
  open A.Assignment Ρ
  open A.Over N Ρ
  open Views wb sync Ρ using (module Typed; balL)
  open Typed wbL

  Progress : Session → Set
  Progress M = ∃[ α ] ∃[ M′ ] M [ α ]⇒ M′

  private
    -- Over a finite index: either every `x` has `A x`, or some `x` gives
    -- a way out `B`.
    fin-collect :
      ∀ {n} {A : Fin n → Set} {B : Set}
      → (∀ x → A x ⊎ B) → (∀ x → A x) ⊎ B
    fin-collect {0} f = inj₁ λ ()
    fin-collect {suc n} {A} f
      with f zero | fin-collect {n} {A ∘ fsuc} (f ∘ fsuc)
    ... | inj₂ b | _       = inj₂ b
    ... | inj₁ _ | inj₂ b  = inj₂ b
    ... | inj₁ a | inj₁ as = inj₁ λ { zero → a ; (fsuc x) → as x }

    -- An action internal to the blocks of two different roles is
    -- internal to neither, unless the roles share a block.
    same-block :
      ∀ {X j l β} → X ∈ lu roles j → X ∈α β
      → Internal (lu roles l) β → l ≡ j
    same-block X∈ X∈β int = trans (sym (∈/owner (int _ X∈β))) (∈/owner X∈)

  -- ══════════════════════════════════════════════════════════════════
  --  Progress
  -- ══════════════════════════════════════════════════════════════════

  module Prog {M : Session} {G : Behav} (ts : ⊢ᴸ M ∶ G) where

    -- ════════════════════════════════════════════════════════════════
    --  Runs of internal steps
    -- ════════════════════════════════════════════════════════════════

    InBlock : Action → Set
    InBlock γ = ∃[ b ] Internal (lu roles b) γ

    Walk : Behav → Behav → Set
    Walk s s′ = ∃[ γ ] s -< γ >-> s′ × InBlock γ

    -- To block `k`, a walk is `Mixed`: another block's internal step is
    -- an outsiders' step.
    walk/mixed :
      ∀ k {u v} → Star Walk u v → Star (Mixed/ {lu roles k} InBlock) u v
    walk/mixed k ε = ε
    walk/mixed k ((γ , gr , ib@(b , int)) ◅ walk) with b ≟f k
    ... | yes refl = (γ , gr , ib , inj₁ int) ◅ walk/mixed k walk
    ... | no b≢k =
      ( γ , gr , ib
      , inj₂ λ Z Z∈ → ¬∈α→∉α {Z} {γ} λ Z∈γ →
          b≢k (same-block {β = γ} Z∈ Z∈γ int) )
      ◅ walk/mixed k walk

    run/walk :
      ∀ {Ps u v bs}
      → u -[ bs ]-> v → All (λ b → InBlock b × Ps ∉αˢ b) bs → Star Walk u v
    run/walk tr/refl []ᴬ = ε
    run/walk (tr/step gr tr) ((ib , _) ∷ᴬ qs) =
      (_ , gr , ib) ◅ run/walk tr qs

    τs/walk : ∀ {k u v} → Star (_-τ->_ (lu roles k)) u v → Star Walk u v
    τs/walk {k} = Star.map λ (γ , gr , int) → γ , gr , k , int

    -- A step at the end of a walk that its sender's block takes part in
    -- externally.
    record Active : Set where
      field
        {u t} : Behav
        {β}   : Action
        walk  : Star Walk G u
        gr    : u -< β >-> t
        l     : Fin K
        {S}   : Part
        S∈    : S ∈ lu roles l
        snd   : Send β S
        ¬int  : ¬ Internal (lu roles l) β

    -- A step at the end of a walk: internal to its sender's block (the
    -- walk goes on), or `Active`.
    classify :
      ∀ {u β t}
      → Star Walk G u → u -< β >-> t
      → (Star Walk G t × InBlock β) ⊎ Active
    classify walk gr with Synchronous.balanced sync gr
    ... | S , Qs , c , _ , _ , refl
      with internal? (lu roles (owner S)) (S ⟶ Qs # c)
    ...   | yes int =
      inj₁ (walk ◅◅ ((_ , gr , owner S , int) ◅ ε) , owner S , int)
    ...   | no ¬int =
      inj₂ (record
        { walk = walk ; gr = gr ; l = owner S ; S∈ = owner/∈ S
        ; snd = _ , _ , ev-sender {S} {Qs} {c} ; ¬int = ¬int })

    if/progress :
      ∀ k {E Pr Pr′}
      → [] ⊢e E ∶ s/bool → M [ k ]= ifp E then Pr else Pr′ → Progress M
    if/progress k etd lu≡ with eval-bool etd
    ... | inj₁ e⇓t = nothing , _ , s/if/true k lu≡ e⇓t
    ... | inj₂ e⇓f = nothing , _ , s/if/false k lu≡ e⇓f

    -- A receiving block, ready for `P`'s multicast.
    Ready : Fin K → Part → PartSet → ℕ → Fin K → Set
    Ready l P Qs I k =
      Receives l Qs k
      → Σ[ R ∈ Part ] Σ[ Br ∈ Vec (Proc 1 0) (suc I) ]
          R ∈ Qs × R ∈ lu roles k × M [ k ]= R ⇐ P ？· Br

    -- ════════════════════════════════════════════════════════════════
    --  One block, at the end of a walk
    -- ════════════════════════════════════════════════════════════════

    module Blk (k : Fin K) where

      Ps : PartSet
      Ps = lu roles k

      -- Public: `Head` works with the same names.
      module V = BTheory (Views.Local wb sync Ρ k)
      open MPST (wbL k) public using () renaming (~refl to ~reflᴸ)
      open import Definitions.Typing.Alg (wbL k) public
        using ( _⊢at_∶_; a/send; a/recv; a/if; a/end; a/var; a/rec
              ; waitLeaf; waitActive; at/send-inv; at/recv-inv )
      open WellBehaved (wbL k) public
        using () renaming ( recv-overlap to recv-overlapᴸ
                          ; step-arity-det to step-arity-detᴸ )

      -- `k`'s derivation at any state its outsiders lead to.
      der :
        ∀ {H bs Pr}
        → G -[ bs ]-> H → All (λ b → InBlock b × Ps ∉αˢ b) bs
        → M [ k ]= Pr → [] ⊢at Ps ◂ Pr ∶ ([] , H)
      der tr qs lu≡ =
        Per.unskip k (Per.lift k (_ , tr , All.map proj₂ qs)) ~reflᴸ
          (td/lookup ts lu≡)

      -- `k`'s external step at the end of a walk, as a step of its view.
      record Seen (β : Action) : Set where
        field
          H    : Behav
          bs   : List Action
          run  : G -[ bs ]-> H
          qs   : All (λ b → InBlock b × Ps ∉αˢ b) bs
          t′   : Behav
          step : _-<_>->ᵛ_ Ps H β t′

      see :
        ∀ {u β t}
        → Star Walk G u → u -< β >-> t → Ps ∈αˢ β → ¬ Internal Ps β
        → Seen β
      see walk gr own ¬int
        with split/ {Ps} (walk/mixed k walk)
      ... | H , H₁ , (bs , tr , qs) , τs , H₁~u
        with ~R H₁~u gr
      ... | t′ , gr′ , _ =
        record { H = H ; bs = bs ; run = tr ; qs = qs ; t′ = t′
               ; step = inj₂ (¬int , own , H₁ , τs , gr′) }

      -- An own step of `k`'s view is a step of `B` after `k`'s internal
      -- steps.
      own/b :
        ∀ {H β t}
        → _-<_>->ᵛ_ Ps H β t → Ps ∈αˢ β
        → ∃[ H₁ ] Star (_-τ->_ Ps) H H₁ × ∃[ t₁ ] H₁ -< β >-> t₁
      own/b {β = β} (inj₁ (idle , _)) own =
        ⊥-elim (∉αˢ→¬∈αˢ {Ps} {β} idle own)
      own/b (inj₂ (_ , _ , H₁ , τs , gr)) _ = H₁ , τs , _ , gr

      -- An own step of `k`'s view at the end of a walk: `k`'s internal
      -- steps, then an `Active` step.
      own/active :
        ∀ {u α t}
        → Star Walk G u → _-<_>->ᵛ_ Ps u α t → Ps ∈αˢ α → Active
      own/active {α = α} walk vα own@(X , X∈ , X∈α)
        with own/b vα own | vα
      ... | _ | inj₁ (idle , _) = ⊥-elim (∉αˢ→¬∈αˢ {Ps} {α} idle own)
      ... | H₁ , τs , _ , gr | inj₂ (¬intk , _)
        with classify (walk ◅◅ τs/walk τs) gr
      ...   | inj₂ act = act
      ...   | inj₁ (_ , l , int) =
        ⊥-elim (¬intk (subst (λ o → Internal (lu roles o) α)
                         (same-block {β = α} X∈ X∈α int) int))

      -- Along a trace of `k`'s view on which `k` acts, the walk meets an
      -- `Active` step.
      trace/active :
        ∀ {u αs u′}
        → Star Walk G u → u V.-[ αs ]-> u′ → Any (Ps ∈αˢ_) αs → Active
      trace/active walk (V.tr/step {α = α} vα tr) mem
        with Ps ∈αˢ? α
      ... | yes own = own/active walk vα own
      ... | no ¬own with vα | mem
      ...   | inj₂ (_ , own , _) | _          = ⊥-elim (¬own own)
      ...   | inj₁ _             | here own   = ⊥-elim (¬own own)
      ...   | inj₁ (_ , gr)      | there mem′ with classify walk gr
      ...     | inj₂ act         = act
      ...     | inj₁ (walk′ , _) = trace/active walk′ tr mem′

      -- A receiving block of `P`'s multicast is at a receive from `P`, at a
      -- role of `Qs`, of the same arity; or it has a τ step.
      recv-head :
        ∀ {P Qs I} {i : Fin (suc I)} {S u t}
        → Star Walk G u → u -< P ⟶ Qs # i < S > >-> t → P ∉ Ps
        → ∀ R → R ∈ Qs → R ∈ Ps
        → (Σ[ R′ ∈ Part ] Σ[ Br ∈ Vec (Proc 1 0) (suc I) ]
             R′ ∈ Qs × R′ ∈ Ps × M [ k ]= R′ ⇐ P ？· Br)
          ⊎ Progress M
      recv-head {P} {Qs} {I} {i} {S} walk gr P∉ R R∈Qs R∈ =
        go (lookup⇒[]= k M refl) (der run qs (lookup⇒[]= k M refl))
        where
          α = P ⟶ Qs # i < S >

          own : Ps ∈αˢ α
          own =
            R , R∈ , _
            , ev-recv {P} {Qs} {i < S >} (λ { refl → P∉ R∈ }) R∈Qs

          ¬int : ¬ Internal Ps α
          ¬int int = P∉ (int P (_ , ev-sender {P} {Qs} {i < S >}))

          open Seen (see walk gr own ¬int)

          -- A role of `k` taking part in `α` receives in it.
          recvs : ∀ {Y} → Y ∈ Ps → Y ∈α α → Recv α Y
          recvs Y∈ (_ , eqY) with ev-inv {P} {Qs} {i < S >} eqY
          ... | inj₁ (refl , _) = ⊥-elim (P∉ Y∈)
          ... | inj₂ (_ , _ , refl) = _ , _ , eqY

          go :
            ∀ {Pr} → M [ k ]= Pr → [] ⊢at Ps ◂ Pr ∶ ([] , H)
            → (Σ[ R′ ∈ Part ] Σ[ Br ∈ Vec (Proc 1 0) (suc I) ]
                 R′ ∈ Qs × R′ ∈ Ps × M [ k ]= R′ ⇐ P ？· Br)
              ⊎ Progress M
          go lu≡ (_ , a/end done , mem) =
            ⊥-elim (done {[] , H} mem (V.in/α step own))
          go lu≡ (_ , a/var {X = ()} _ , _)
          go lu≡ (_ , a/if etd _ _ , _) = inj₂ (if/progress k etd lu≡)
          go lu≡ (_ , a/rec _ _ _ , _) = inj₂ (nothing , _ , s/rec k lu≡)
          -- `k` sends: the shared role receives in `α`, so `α` is the same
          -- communication, and its sender `P` would be `k`'s.
          go lu≡ td@(_ , a/send X∈ _ _ _ , _)
            with at/send-inv td
          ... | _ , _ , w , _
            with waitLeaf step own w
          ... | foc , _ , α‴ , eqX , vα‴
            with comm-ev (recv-overlapᴸ step vα‴
                            (recvs X∈ (foc V.skip/refl step own)) (_ , eqX))
                   (ev-sender {P} {Qs} {i < S >})
          ... | _ , eqP
            with own/b vα‴ (_ , X∈ , _ , eqX)
          ... | _ , _ , _ , gr‴ =
            ⊥-elim (P∉ (subst (_∈ Ps) (sym (sender/same gr‴ eqX eqP)) X∈))
          -- `k` receives: the same communication, so from `P`, at a role
          -- of `Qs`, with `α`'s arity.
          go lu≡ td@(_ , a/recv {R = R′} {Br = Br′} R′∈ _ _ , _)
            with waitLeaf step own (proj₁ (at/recv-inv td))
          ... | foc , _ , _ , _ , α‴ , eqR′ , vα‴ , _
            with comm-ev (sym (recv-overlapᴸ step vα‴
                                 (recvs R′∈ (foc V.skip/refl step own))
                                 (_ , eqR′)))
                   eqR′
          ... | _ , eq′
            with ev-inv {P} {Qs} {i < S >} eq′
          ... | inj₁ (_ , ())
          ... | inj₂ (R′≢P , R′∈Qs , refl)
            with step-arity-detᴸ step vα‴
                   (ev-recv {P} {Qs} {i < S >} R′≢P R′∈Qs) eqR′
          ... | refl = inj₁ (R′ , Br′ , R′∈Qs , R′∈ , lu≡)

    -- ════════════════════════════════════════════════════════════════
    --  The multicast fires
    -- ════════════════════════════════════════════════════════════════

    fire :
      ∀ l {P Qs I} {i : Fin (suc I)} {E Pr V}
      → P ∈ lu roles l → M [ l ]= P ⇒ Qs ! i < E >∙ Pr → E ⇓ V
      → (∀ k → Ready l P Qs I k) → Progress M
    fire l {P} {Qs} {I} P∈ snd e⇓v all =
      just _ , _
      , s/comm {Rk = λ k → proj₁ (pick k)}
               {Br = λ k → proj₁ (proj₂ (pick k))}
          l P∈ snd e⇓v (λ k r → proj₂ (proj₂ (pick k)) r)
      where
        pick :
          ∀ k → Σ[ R ∈ Part ] Σ[ Br ∈ Vec (Proc 1 0) (suc I) ]
                  (Receives l Qs k
                   → R ∈ Qs × R ∈ lu roles k × M [ k ]= R ⇐ P ？· Br)
        pick k with receives? l Qs k
        ... | yes r = let R , Br , x = all k r in R , Br , λ _ → x
        ... | no ¬r = P , replicate (suc I) ∅ , λ r → ⊥-elim (¬r r)

    -- `P`'s multicast, found at the end of a walk: every receiving block
    -- is ready, or some block has a τ step.
    receivers :
      ∀ l {P Qs I} {i : Fin (suc I)} {S E Pr u t}
      → P ∈ lu roles l → M [ l ]= P ⇒ Qs ! i < E >∙ Pr → [] ⊢e E ∶ S
      → Star Walk G u → u -< P ⟶ Qs # i < S > >-> t → Progress M
    receivers l {P} {Qs} {I} P∈ snd etd walk gr
      with fin-collect {A = Ready l P Qs I} each
      where
        each : ∀ k → Ready l P Qs I k ⊎ Progress M
        each k with receives? l Qs k
        ... | no ¬r = inj₁ λ r → ⊥-elim (¬r r)
        ... | yes (k≢l , R , R∈Qs , ownR)
          with Blk.recv-head k walk gr
                 (λ P∈k → k≢l (trans (sym (∈/owner P∈k)) (∈/owner P∈)))
                 R R∈Qs (subst (λ o → R ∈ lu roles o) ownR (owner/∈ R))
        ...   | inj₁ x = inj₁ λ _ → x
        ...   | inj₂ p = inj₂ p
    ... | inj₂ p = p
    ... | inj₁ all with eval-exp etd
    ...   | _ , e⇓v = fire l P∈ snd e⇓v all

    -- ════════════════════════════════════════════════════════════════
    --  The sender's block, and the start
    -- ════════════════════════════════════════════════════════════════

    module Head (k : Fin K) where

      open Blk k

      -- The sender's block of an `Active` step is at a send, or has a τ
      -- step.  A receive is refuted: it would be the same communication.
      sender :
        ∀ {u β t S₀}
        → Star Walk G u → u -< β >-> t → S₀ ∈ Ps → Send β S₀
        → ¬ Internal Ps β → Progress M
      sender {β = β} walk gr S∈ snd@(_ , _ , eqS) ¬int =
        go (lookup⇒[]= k M refl) (der run qs (lookup⇒[]= k M refl))
        where
          own : Ps ∈αˢ β
          own = _ , S∈ , _ , eqS

          open Seen (see walk gr own ¬int)

          go : ∀ {Pr} → M [ k ]= Pr → [] ⊢at Ps ◂ Pr ∶ ([] , H) → Progress M
          go lu≡ (_ , a/end done , mem) =
            ⊥-elim (done {[] , H} mem (V.in/α step own))
          go lu≡ (_ , a/var {X = ()} _ , _)
          go lu≡ (_ , a/if etd _ _ , _) = if/progress k etd lu≡
          go lu≡ (_ , a/rec _ _ _ , _) = nothing , _ , s/rec k lu≡
          go lu≡ td@(_ , a/recv R∈ _ _ , _)
            with waitLeaf step own (proj₁ (at/recv-inv td))
          ... | foc , _ , _ , _ , α‴ , eqR , vα‴ , (S′ , S′∉ , _ , _ , eqS′)
            with own/b step own
          ... | _ , _ , _ , grβ =
            let _ , eqβS′ =
                  comm-ev (recv-overlapᴸ vα‴ step (_ , _ , eqR)
                             (foc V.skip/refl step own))
                    eqS′
            in ⊥-elim (S′∉ (subst (_∈ Ps) (sym (sender/same grβ eqS eqβS′))
                              S∈))
          go lu≡ td@(_ , a/send P∈ _ _ _ , _)
            with at/send-inv td
          ... | _ , etd , w , _
            with waitLeaf step own w
          ... | _ , _ , α″ , eqP , vα″
            with Balanced.send-action (balL k) vα″ eqP
          ... | _ , refl
            with own/b vα″ (_ , P∈ , _ , eqP)
          ... | _ , ρ , _ , gr″ =
            receivers k P∈ lu≡ etd (run/walk run qs ◅◅ τs/walk ρ) gr″

      -- A block at the start: done, a session step, or an `Active` step.
      status :
        ∀ {Pr} → M [ k ]= Pr → [] ⊢at Ps ◂ Pr ∶ ([] , G)
        → done/proc Pr ⊎ (Progress M ⊎ Active)
      status lu≡ (_ , a/end _ , _) = inj₁ done-∅
      status lu≡ (_ , a/var {X = ()} _ , _)
      status lu≡ (_ , a/if etd _ _ , _) = inj₂ (inj₁ (if/progress k etd lu≡))
      status lu≡ (_ , a/rec _ _ _ , _) =
        inj₂ (inj₁ (nothing , _ , s/rec k lu≡))
      status lu≡ td@(_ , a/send P∈ _ _ _ , _)
        with at/send-inv td
      ... | _ , _ , w , _
        with waitActive (λ { (_ , _ , _ , eq , vα) → V.in/ev vα P∈ eq }) w
      ... | _ , _ , tr , mem = inj₂ (inj₂ (trace/active ε tr mem))
      status lu≡ td@(_ , a/recv R∈ _ _ , _)
        with waitActive
               (λ { (_ , _ , _ , _ , _ , eq , vα , _) → V.in/ev vα R∈ eq })
               (proj₁ (at/recv-inv td))
      ... | _ , _ , tr , mem = inj₂ (inj₂ (trace/active ε tr mem))

    active : Active → Progress M
    active a = Head.sender l walk gr S∈ snd ¬int
      where open Active a

    progress : done M ⊎ Progress M
    progress =
      fin-collect λ j →
        map₂ [ id , active ]′
          (Head.status j (lookup⇒[]= j M refl)
            (Blk.der j tr/refl []ᴬ (lookup⇒[]= j M refl)))

  progress : ∀ {M G} → ⊢ᴸ M ∶ G → done M ⊎ Progress M
  progress ts = Prog.progress ts

  -- ══════════════════════════════════════════════════════════════════
  --  Eventually: finished, or a communication after τ steps
  -- ══════════════════════════════════════════════════════════════════

  open import Safety.Termination wb sync Ρ wbL
    using (τ-depth/processes; τ-depth/decrease; final-run)

  progress/eventual :
    ∀ {M G}
    → ⊢ᴸ M ∶ G
    → ∃[ M′ ] ((M τ⇒ M′ × finished M′)
             ⊎ (∃[ M″ ] ∃[ α ] M τ⇒ M″ × M″ [ just α ]⇒ M′))
  progress/eventual {M} ts =
    go ts (<-wellFounded (τ-depth/processes M))
    where
      go :
        ∀ {M G} → ⊢ᴸ M ∶ G → Acc _<_ (τ-depth/processes M)
        → ∃[ M′ ] ((M τ⇒ M′ × finished M′)
                 ⊎ (∃[ M″ ] ∃[ α ] M τ⇒ M″ × M″ [ just α ]⇒ M′))
      go ts (acc rs) with progress ts
      ... | inj₁ d =
        let M′ , r , fin = final-run ts d in M′ , inj₁ (r , fin)
      ... | inj₂ (just α , M′ , st) = M′ , inj₂ (_ , α , run/end , st)
      ... | inj₂ (nothing , M′ , st)
        with go (preservation/τ ts st) (rs (τ-depth/decrease ts st))
      ...   | M″ , inj₁ (r , fin) = M″ , inj₁ (run/τ st r , fin)
      ...   | M″ , inj₂ (M₁ , α , r , st′) =
        M″ , inj₂ (M₁ , α , run/τ st r , st′)
