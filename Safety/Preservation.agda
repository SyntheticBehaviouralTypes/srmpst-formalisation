{-# OPTIONS --guardedness #-}

-- Preservation: each process typed against its local view, the session's
-- state moving along the global view.
--
-- `existence`: a session communication is a global step.  Recursion on
-- the sender's wait tree.
-- `follow`: every process's typing follows that step, by `Projection`.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero) renaming (_≟_ to _≟f_)
import Data.Fin.Properties as FinP
open import Data.Fin.Subset using (_∈_; _∉_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (id)
open import Data.Vec using (Vec; []; _∷_; _[_]=_; _[_]≔_)
  renaming (lookup to lu)
open import Data.Vec.Properties
  using ([]=⇒lookup; lookup∘update; lookup∘update′)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; subst)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_; _◅◅_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Definitions.Expr
open import Definitions.Behav using (BTheory; WellBehaved; Balanced; Synchronous)
open import Definitions.Typing.Declarative using (module MPST)
import Definitions.Typing.Alg as Alg
import Definitions.Proc as A

module Safety.Preservation
  {N : ℕ} {B : BTheory N} (wb : WellBehaved B) (sync : Synchronous B)
  {K : ℕ} (Ρ : A.Assignment N K)
  where

  open import Definitions.Common N
  open import Definitions.Actions N
  open import Definitions.Proc N
    using ( Proc; NProc; _◂_; unfold/proc; module Subst
          ; _⇒_!_<_>∙_; _⇐_？·_; ifp_then_else_; rec; MessageGuarded )
  open import Definitions.View B
  open import Definitions.View.Lemmas B wb sync
  open BTheory B
  open A.Assignment Ρ
  open A.Over N Ρ
  open Global Ρ using (_-<_>->ᵍ_; block)

  -- Process `j`'s local view.
  Local : Fin K → BTheory N
  Local j = view (lu roles j)

  balL : ∀ j → Balanced (Local j)
  balL j = balanced/view (lu roles j) (Synchronous.bal sync)

  module Typed
    (wbL   : ∀ j → WellBehaved (Local j))
    where

    infix 4 ⊢ᴸ_∶_

    -- Process `j`'s typing, against its own local view.
    infix 4 _⊢ᴸ[_]_∶_

    _⊢ᴸ[_]_∶_ : ∀ {γ} → Vec Sort γ → Fin K → NProc γ 0 → Behav → Set₁
    Γ ⊢ᴸ[ j ] PPr ∶ G = Alg._⊢at_∶_ (wbL j) Γ PPr ([] , G)

    -- Every process typed against its own local view.
    ⊢ᴸ_∶_ : Session → Behav → Set₁
    ⊢ᴸ M ∶ G = ∀ j → [] ⊢ᴸ[ j ] lu roles j ◂ lu M j ∶ G

    -- One process, in its own local view.
    module Per (j : Fin K) where

      private
        Ps = lu roles j
      open MPST (wbL j) using ()
        renaming (_-[¬_]->*_ to _-[¬_]->ᴸ*_; _~_ to _~ᴸ_; ~refl to ~reflᴸ
                 ; skip/refl to skip/reflᴸ)
      open import Definitions.Typing.Alg (wbL j)
        using ( at/send-inv; at/recv-inv; at/if-inv; at/rec-guarded
              ; waitLeaf; Wait; Dom )
      open import Definitions.Typing.Substitution (wbL j)
        using (at/subst-expr; at/rec/unfold; at/unskip)
      open import Definitions.Behav using (module BTheory)

      -- `at/unskip` along outsiders' steps, or along `~` only.
      unskip :
        ∀ {Pr G H H′}
        → G -[¬ Ps ]->ᴸ* H → H ~ᴸ H′
        → [] ⊢ᴸ[ j ] Ps ◂ Pr ∶ G → [] ⊢ᴸ[ j ] Ps ◂ Pr ∶ H′
      unskip = at/unskip (balL j)

      open Projection Ρ j

      -- Outsiders' steps of `B` are steps of the local view.
      lift : ∀ {G G′} → G -[¬ Ps ]->* G′ → G -[¬ Ps ]->ᴸ* G′
      lift (_ , tr/refl , []) = [] , BTheory.tr/refl , []
      lift (_ ∷ _ , tr/step gr tr , idle ∷ idles) =
        let _ , trL , idlesL = lift (_ , tr , idles)
        in _ , BTheory.tr/step (local/idle idle gr) trL , idle ∷ idlesL

      idle :
        ∀ {Pr G α G′}
        → [] ⊢ᴸ[ j ] Ps ◂ Pr ∶ G
        → Ps ∉αˢ α → G -< α >->ᵍ G′
        → [] ⊢ᴸ[ j ] Ps ◂ Pr ∶ G′
      idle td P∉ gv = unskip (lift (project/idle P∉ gv)) ~reflᴸ td

      send :
        ∀ {P Qs I} {i : Fin (suc I)} {E V Pr G G′}
        → P ∈ Ps
        → [] ⊢ᴸ[ j ] Ps ◂ P ⇒ Qs ! i < E >∙ Pr ∶ G
        → E ⇓ V
        → G -< P ⟶ Qs # i < sort/value V > >->ᵍ G′
        → [] ⊢ᴸ[ j ] Ps ◂ Pr ∶ G′
      send {P} {Qs} {i = i} {V = V} P∈ td e⇓v gv
        with project/own
               (P , P∈ , _ , ev-sender {P} {Qs} {i < sort/value V >}) gv
      ... | H , H′ , tr , gr , H′~G′
        with at/send-inv (unskip (lift tr) ~reflᴸ td)
      ... | _ , etd , _ , k with sort/value-typed (exp-pres etd e⇓v)
      ...   | refl =
        unskip skip/reflᴸ (local/~ H′~G′)
          (k ε (_ , ev-sender {P} {Qs} {i < sort/value V >} , gr))

      -- An own role is not an outsider.
      own≢out : ∀ {R P} → R ∈ Ps → P ∉ Ps → R ≢ P
      own≢out R∈ P∉ refl = P∉ R∈

      recv :
        ∀ {P R Qs I} {i : Fin (suc I)} {V} {Br : Vec (Proc 1 0) (suc I)}
          {G G′}
        → R ∈ Ps → R ∈ Qs → P ∉ Ps
        → [] ⊢ᴸ[ j ] Ps ◂ R ⇐ P ？· Br ∶ G
        → G -< P ⟶ Qs # i < sort/value V > >->ᵍ G′
        → [] ⊢ᴸ[ j ] Ps ◂ Subst.[ val V / zero ]e lu Br i ∶ G′
      recv {P} {R} {Qs} {i = i} {V} R∈ R∈Qs P∉ td gv
        with project/own
               ( R , R∈ , _
               , ev-recv {P} {Qs} {i < sort/value V >} (own≢out R∈ P∉) R∈Qs )
               gv
      ... | H , H′ , tr , gr , H′~G′ =
        unskip skip/reflᴸ (local/~ H′~G′)
          (at/subst-expr (balL j) (te/val (value/sort V))
            (proj₂ (at/recv-inv (unskip (lift tr) ~reflᴸ td))
              ε (_ , eqR , gr , P , P∉ , Qs , _ , eqP)))
        where
          eqR = ev-recv {P} {Qs} {i < sort/value V >} (own≢out R∈ P∉) R∈Qs
          eqP = ev-sender {P} {Qs} {i < sort/value V >}

      if-true :
        ∀ {E Pr Pr′ G}
        → [] ⊢ᴸ[ j ] Ps ◂ ifp E then Pr else Pr′ ∶ G
        → [] ⊢ᴸ[ j ] Ps ◂ Pr ∶ G
      if-true td = proj₁ (proj₂ (at/if-inv td))

      if-false :
        ∀ {E Pr Pr′ G}
        → [] ⊢ᴸ[ j ] Ps ◂ ifp E then Pr else Pr′ ∶ G
        → [] ⊢ᴸ[ j ] Ps ◂ Pr′ ∶ G
      if-false td = proj₂ (proj₂ (at/if-inv td))

      -- For `existence`: the sender's wait tree.
      send/wait :
        ∀ {P Qs I} {i : Fin (suc I)} {E Pr G}
        → [] ⊢ᴸ[ j ] Ps ◂ P ⇒ Qs ! i < E >∙ Pr ∶ G
        → ∃[ S ] ([] ⊢e E ∶ S) × Wait Ps (Dom Ps P ((! Qs) # i < S >)) ([] , G)
      send/wait td = let S , etd , w , _ = at/send-inv td in S , etd , w

      -- For `existence`: a block at a receive from `P` takes part only
      -- internally in a step without `P`.
      receiver/busy :
        ∀ {P R I} {Br : Vec (Proc 1 0) (suc I)} {G H H₁ β t}
        → [] ⊢ᴸ[ j ] Ps ◂ R ⇐ P ？· Br ∶ G
        → G -[¬ Ps ]->* H → Star (_-τ->_ Ps) H H₁ → H₁ -< β >-> t
        → Ps ∈αˢ β → ¬ Internal Ps β → P ∉α β → ⊥
      receiver/busy {P} {H = H} {β = β} {t} td tr τs grβ own ¬int P∉β =
        go (inj₂ (¬int , own , _ , τs , grβ))
        where
          go : _-<_>->ᵛ_ Ps H β t → ⊥
          go vβ
            with waitLeaf vβ own
                   (proj₁ (at/recv-inv (unskip (lift tr) ~reflᴸ td)))
          ... | foc , _ , _ , _ , α′ , eq , vα′ , _ =
            ∉α→¬∈α {P} {β} P∉β
              (comm-∈α {α′} {β} {P}
                (WellBehaved.recv-overlap (wbL j) vα′ vβ (_ , _ , eq)
                  (foc (BTheory.skip/refl (Local j)) vβ own))
                (Balanced.recv-sender (balL j) vα′ eq))

      -- For `Safety/Termination.agda`.
      guarded :
        ∀ {Pr G} → [] ⊢ᴸ[ j ] Ps ◂ rec Pr ∶ G → MessageGuarded Pr
      guarded = at/rec-guarded

      guard :
        ∀ {E Pr Pr′ G}
        → [] ⊢ᴸ[ j ] Ps ◂ ifp E then Pr else Pr′ ∶ G
        → [] ⊢e E ∶ s/bool
      guard td = proj₁ (at/if-inv td)

      unfold :
        ∀ {Pr G}
        → [] ⊢ᴸ[ j ] Ps ◂ rec Pr ∶ G
        → [] ⊢ᴸ[ j ] Ps ◂ unfold/proc Pr ∶ G
      unfold = at/rec/unfold (balL j)

    td/lookup :
      ∀ {M G j Pr}
      → ⊢ᴸ M ∶ G → M [ j ]= Pr
      → [] ⊢ᴸ[ j ] lu roles j ◂ Pr ∶ G
    td/lookup {j = j} ts lu≡ with ts j
    ... | tdj rewrite []=⇒lookup lu≡ = tdj

    ⊢ᴸ-update :
      ∀ (M : Session) {G j Pr}
      → ⊢ᴸ M ∶ G
      → [] ⊢ᴸ[ j ] lu roles j ◂ Pr ∶ G
      → ⊢ᴸ M [ j ]≔ Pr ∶ G
    ⊢ᴸ-update M {j = j} {Pr} ts tdj l with l ≟f j
    ... | yes refl rewrite lookup∘update j M Pr = tdj
    ... | no l≢j rewrite lookup∘update′ l≢j M Pr = ts l

    preservation/τ :
      ∀ {M M′ G} → ⊢ᴸ M ∶ G → M [ nothing ]⇒ M′ → ⊢ᴸ M′ ∶ G
    preservation/τ {M} ts (s/if/true j lu≡ _) =
      ⊢ᴸ-update M ts (Per.if-true j (td/lookup ts lu≡))
    preservation/τ {M} ts (s/if/false j lu≡ _) =
      ⊢ᴸ-update M ts (Per.if-false j (td/lookup ts lu≡))
    preservation/τ {M} ts (s/rec j lu≡) =
      ⊢ᴸ-update M ts (Per.unfold j (td/lookup ts lu≡))

    -- A block that neither sends nor receives takes no part in the step.
    other/idle :
      ∀ {j l P Qs c}
      → P ∈ lu roles j → l ≢ j → ¬ Receives j Qs l
      → lu roles l ∉αˢ (P ⟶ Qs # c)
    other/idle {j} {l} {P} {Qs} {c} P∈ l≢j ¬r X X∈ with X ≟f P
    ... | yes refl = ⊥-elim (l≢j (trans (sym (∈/owner X∈)) (∈/owner P∈)))
    ... | no X≢P with X ∈? Qs
    ...   | yes X∈Qs = ⊥-elim (¬r (l≢j , X , X∈Qs , ∈/owner X∈))
    ...   | no X∉Qs = ev-other {P} {Qs} {c} {X} X≢P X∉Qs

    -- Roles of different blocks differ.
    apart : ∀ {j k X Y} → k ≢ j → X ∈ lu roles k → Y ∈ lu roles j → X ≢ Y
    apart k≢j X∈ Y∈ refl = k≢j (trans (sym (∈/owner X∈)) (∈/owner Y∈))

    -- The global step a session step corresponds to moves every process.
    follow :
      ∀ {M M′ G G′ α}
      → ⊢ᴸ M ∶ G → M [ just α ]⇒ M′ → G -< α >->ᵍ G′
      → ⊢ᴸ M′ ∶ G′
    follow {M}
      ts (s/comm {P = P} {Qs} {i = i} {V = V} {Pr} {Rk} {Br}
                 j P∈ snd e⇓v recvs) gv l
      with l ≟f j
    ... | yes refl
      rewrite upd/sender {M} {l} {Pr} {Qs}
                {λ k → Subst.[ val V / zero ]e lu (Br k) i} =
      Per.send l P∈ (td/lookup ts snd) e⇓v gv
    ... | no l≢j with receives? j Qs l
    ...   | yes r
      rewrite upd/recv {M} {j} {Pr} {Qs}
                {λ k → Subst.[ val V / zero ]e lu (Br k) i} {l} r =
      let R∈Qs , R∈ , rcv = recvs l r
      in Per.recv l R∈ R∈Qs (λ P∈l → apart l≢j P∈l P∈ refl)
           (td/lookup ts rcv) gv
    ...   | no ¬r
      rewrite upd/other {M} {j} {Pr} {Qs}
                {λ k → Subst.[ val V / zero ]e lu (Br k) i} {l} l≢j ¬r =
      Per.idle l (ts l) (other/idle P∈ l≢j ¬r) gv

    preservation/τ* :
      ∀ {M M′ G} → ⊢ᴸ M ∶ G → M τ⇒ M′ → ⊢ᴸ M′ ∶ G
    preservation/τ* ts run/end      = ts
    preservation/τ* ts (run/τ st r) = preservation/τ* (preservation/τ ts st) r

    -- ══════════════════════════════════════════════════════════════════
    --  Existence of the global step
    -- ══════════════════════════════════════════════════════════════════

    module Exists where

      -- One communication: role `P` of block `j` sends `c` to `Qs`; every
      -- receiving block `k` is at a receive from `P` at the start `G₀`.
      module Comm
        {j : Fin K} {P : Part} {Qs : PartSet} {c : Choice}
        (P∈ : P ∈ lu roles j)
        {I : ℕ} {Rk : Fin K → Part} {Br : Fin K → Vec (Proc 1 0) (suc I)}
        {G₀ : Behav}
        (recvs : ∀ k → Receives j Qs k
                 → Rk k ∈ Qs × Rk k ∈ lu roles k
                 × [] ⊢ᴸ[ k ] lu roles k ◂ Rk k ⇐ P ？· Br k ∶ G₀)
        where

        private
          Ps = lu roles j
          α  = P ⟶ Qs # c
          module VJ = BTheory (Local j)

        open import Definitions.Typing.Alg (wbL j)
          using ( Behavs; Closed; WaitV; wv/leaf; wv/cycle; wv/step
                ; waitV/unfold-top; Wait; Dom )
        open Projection Ρ j using (own/global)

        -- A step of the walk: internal to a receiving block, or idle for
        -- the sender's block and every receiving block.
        Walk : Behav → Behav → Set
        Walk u v =
          ∃[ β ] u -< β >-> v
          × ( (∃[ k ] Receives j Qs k × Internal (lu roles k) β)
            ⊎ (Ps ∉αˢ β × ∀ k → Receives j Qs k → lu roles k ∉αˢ β) )

        -- To receiving block `k`, a walk is `Mixed`: another block's
        -- internal step is an outsiders' step.
        walk/mixed :
          ∀ {k u v} → Receives j Qs k → Star Walk u v
          → Star (Mixed {lu roles k}) u v
        walk/mixed r ε = ε
        walk/mixed {k} r ((β , gr , inj₂ (_ , idle)) ◅ walk) =
          (β , gr , inj₂ (idle k r)) ◅ walk/mixed r walk
        walk/mixed {k} r ((β , gr , inj₁ (k′ , _ , int)) ◅ walk)
          with k′ ≟f k
        ... | yes refl = (β , gr , inj₁ int) ◅ walk/mixed r walk
        ... | no k′≢k =
          (β , gr , inj₂ λ Z Z∈ → ¬∈α→∉α {Z} {β} λ Z∈β →
             apart k′≢k (int Z Z∈β) Z∈ refl)
          ◅ walk/mixed r walk

        -- (iii) A receiving block is never involved externally.
        busy :
          ∀ {k u t β}
          → Receives j Qs k → Star Walk G₀ u → u -< β >-> t
          → lu roles k ∈αˢ β → ¬ Internal (lu roles k) β → Ps ∉αˢ β → ⊥
        busy {k} r walk grβ own ¬int idle
          with split {lu roles k} (walk/mixed r walk)
        ... | H , H₁ , tr , τs , H₁~u
          with ~R H₁~u grβ
        ... | _ , grβ′ , _ =
          let _ , _ , td = recvs k r
          in Per.receiver/busy k td tr τs grβ′ own ¬int (idle P P∈)

        -- (i) A receiving block's internal step joins the hidden prefix.
        extend :
          ∀ {k u v β}
          → Receives j Qs k → Internal (lu roles k) β → u -< β >-> v
          → ∃[ G′ ] v -< α >->ᵍ G′ → ∃[ G′ ] u -< α >->ᵍ G′
        extend {k} {β = β} r int grβ (G′ , ¬hid , G₁ , τs , grα) =
          let R∈Qs , R∈ , _ = recvs k r
          in G′ , ¬hid , G₁
             , ( β , grβ , Rk k
               , (_ , ev-recv {P} {Qs} {c} (apart (proj₁ r) R∈ P∈) R∈Qs)
               , subst (λ o → Internal (lu roles o) β) (sym (∈/owner R∈)) int )
               ◅ τs
             , grα

        -- (ii) A step idle for every involved block is pulled back.
        pull :
          ∀ {u v β}
          → u -< β >-> v → Ps ∉αˢ β
          → (∀ k → Receives j Qs k → lu roles k ∉αˢ β)
          → ∃[ G′ ] v -< α >->ᵍ G′ → ∃[ G′ ] u -< α >->ᵍ G′
        pull {β = β} grβ idleJ idleR (_ , gv) = pullback Ρ grβ blocks gv
          where
            blocks : ∀ X → X ∈α α → block X ∉αˢ β
            blocks X (_ , eqX) Z Z∈ with ev-inv {P} {Qs} {c} {X} eqX
            ... | inj₁ (refl , _) =
              idleJ Z (subst (λ o → Z ∈ lu roles o) (∈/owner P∈) Z∈)
            ... | inj₂ (_ , X∈Qs , _) with owner X ≟f j
            ...   | yes eq = idleJ Z (subst (λ o → Z ∈ lu roles o) eq Z∈)
            ...   | no ne  = idleR (owner X) (ne , X , X∈Qs , refl) Z Z∈

        -- Which blocks a step the sender's block is idle in involves.
        data Kind (β : Action) : Set where
          k/internal :
            ∀ k → Receives j Qs k → Internal (lu roles k) β → Kind β
          k/idle :
            (∀ k → Receives j Qs k → lu roles k ∉αˢ β) → Kind β
          k/external :
            ∀ k → Receives j Qs k → lu roles k ∈αˢ β
            → ¬ Internal (lu roles k) β → Kind β

        kind : ∀ β → Kind β
        kind β
          with FinP.any? (λ k → receives? j Qs k ×-dec (lu roles k ∈αˢ? β))
        ... | no none =
          k/idle λ k r → ¬∈αˢ→∉αˢ {lu roles k} {β} λ own → none (k , r , own)
        ... | yes (k , r , own) with internal? (lu roles k) β
        ...   | yes int  = k/internal k r int
        ...   | no ¬int  = k/external k r own ¬int

        -- A view step of an idle block is a step of `B`.
        b-step :
          ∀ {u β v} → Ps ∉αˢ β → _-<_>->ᵛ_ Ps u β v → u -< β >-> v
        b-step _ (inj₁ (_ , gr)) = gr
        b-step {β = β} idle (inj₂ (_ , own , _)) =
          ⊥-elim (∉αˢ→¬∈αˢ {Ps} {β} idle own)

        -- The sender's leaves.
        𝒮 : Behavs
        𝒮 u = Dom Ps P ((! Qs) # c) ([] , u)

        c𝒮 : Closed 𝒮
        c𝒮 G~H (foc , _ , α′ , eq , g) =
          VJ.focus/~ G~H foc , _ , α′ , eq , VJ.~L→ G~H g

        -- A leaf is a global step.
        leaf : ∀ {u} → 𝒮 u → ∃[ G′ ] u -< α >->ᵍ G′
        leaf (_ , _ , α′ , eq , vα)
          with Balanced.send-action (balL j) vα eq
        ... | _ , refl = _ , own/global (P , P∈ , _ , ev-sender {P} {Qs} {c}) vα

        -- One step of the walk, by its kind.  The continuation may instead
        -- produce an `X` (the tree hit a cycle), carried back by `back`.
        advance⊎ :
          ∀ {X : Behav → Set}{u v β}
          → (X v → X u)
          → Star Walk G₀ u → _-<_>->ᵛ_ Ps u β v → Ps ∉αˢ β
          → (Star Walk G₀ v → (∃[ G′ ] v -< α >->ᵍ G′) ⊎ X v)
          → (∃[ G′ ] u -< α >->ᵍ G′) ⊎ X u
        advance⊎ {β = β} back walk gr idleJ next with kind β | b-step idleJ gr
        ... | k/external k r own ¬int | grB =
          ⊥-elim (busy r walk grB own ¬int idleJ)
        ... | k/internal k r int | grB
          with next (walk ◅◅ (β , grB , inj₁ (k , r , int)) ◅ ε)
        ...   | inj₁ res = inj₁ (extend r int grB res)
        ...   | inj₂ x   = inj₂ (back x)
        advance⊎ {β = β} back walk gr idleJ next | k/idle idleR | grB
          with next (walk ◅◅ (β , grB , inj₂ (idleJ , idleR)) ◅ ε)
        ...   | inj₁ res = inj₁ (pull grB idleJ idleR res)
        ...   | inj₂ x   = inj₂ (back x)

        -- Structural on the sender's tree.
        ready-or-∈T :
          ∀ {u V} → Star Walk G₀ u → WaitV Ps 𝒮 V u
          → (∃[ G′ ] u -< α >->ᵍ G′) ⊎ Ps VJ.∈T u
        ready-or-∈T walk (wv/leaf x)      = inj₁ (leaf x)
        ready-or-∈T walk (wv/cycle _ inT) = inj₂ inT
        ready-or-∈T walk (wv/step na gr k) =
          advance⊎ (VJ.in/later gr) walk gr (na gr) λ walk′ →
            ready-or-∈T walk′ (k gr)

        -- After a cycle: walk the `∈T` run, re-rooting the tree each step.
        ready-from-∈T :
          ∀ {u} → Star Walk G₀ u → WaitV Ps 𝒮 (λ _ → ⊥) u → Ps VJ.∈T u
          → ∃[ G′ ] u -< α >->ᵍ G′
        ready-from-∈T walk (wv/leaf x) _ = leaf x
        ready-from-∈T walk (wv/cycle (_ , () , _) _) _
        ready-from-∈T walk (wv/step na _ _)
          (_ , _ , VJ.tr/step {α = β} gr′ _ , here px) =
          ⊥-elim (∉αˢ→¬∈αˢ {Ps} {β} (na gr′) px)
        ready-from-∈T walk top@(wv/step na _ kP)
          (_ , H , VJ.tr/step gr′ tr , there mem) =
          [ id , ⊥-elim ]′
            (advance⊎ {X = λ _ → ⊥} id walk gr′ (na gr′) λ walk′ →
               inj₁ (ready-from-∈T walk′
                       (waitV/unfold-top c𝒮 top (λ w → w) (kP gr′))
                       (_ , H , tr , mem)))

        existence :
          Wait Ps (Dom Ps P ((! Qs) # c)) ([] , G₀) → ∃[ G′ ] G₀ -< α >->ᵍ G′
        existence wP with ready-or-∈T ε wP
        ... | inj₁ res = res
        ... | inj₂ inT = ready-from-∈T ε wP inT

      -- The global step a session step corresponds to exists, and every
      -- process follows it.
      preservation/comm :
        ∀ {M M′ G α}
        → ⊢ᴸ M ∶ G → M [ just α ]⇒ M′
        → ∃[ G′ ] G -< α >->ᵍ G′ × ⊢ᴸ M′ ∶ G′
      preservation/comm ts
        st@(s/comm {P = P} {Qs} {i = i} {V = V} {Rk = Rk} {Br}
                   j P∈ snd e⇓v recvs)
        with Per.send/wait j (td/lookup ts snd)
      ... | S , etd , wP with sort/value-typed (exp-pres etd e⇓v)
      ...   | refl =
        let G′ , gv =
              Comm.existence P∈ {Rk = Rk} {Br}
                (λ k r → let R∈Qs , R∈ , rcv = recvs k r
                         in R∈Qs , R∈ , td/lookup ts rcv)
                wP
        in G′ , gv , follow ts st gv
