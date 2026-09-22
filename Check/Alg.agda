{-# OPTIONS --guardedness #-}

-- Decision procedure for `Definitions.Typing.Alg`'s `_&_⊢a_∶_` (TODO.md's
-- set-based, syntax-directed judgment).  EXCLUSIVELY about that judgment:
-- no `⊢p`, no `⊢s`, no `ProcessTyping`/`SessionTyping`, no bridging to the
-- declarative system.  That bridging (via `alg⇒typing`/`typing⇒alg`, both
-- of which are kept and are NOT to be touched) belongs to a different file.
--
-- Written fresh (TODO.md §4/§4a/D6): nothing here imports another
-- `Check/*.agda` file or reuses its decision procedure, even where the
-- underlying idea is forced (e.g. a bounded fixed point over
-- `Vec Bool (size G)` is the only sane way to decide a closure operator on
-- a finite graph) — every such piece is rebuilt from first principles
-- against `Definitions/` alone.

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Induction using (<-wellFounded)
import Data.Nat.Properties as Nat

open import Data.Fin using (Fin; zero; suc)
import Data.Fin.Properties as FinP

open import Data.Vec using (Vec; []; _∷_; lookup; tabulate; replicate)
import Data.Vec.Properties as VecP

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.Any.Properties as AnyProp

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

open import Data.Bool using (Bool; true; false; _∨_; _∧_; T)
import Data.Bool.Properties as BoolP

open import Induction.WellFounded using (Acc; acc)

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable
  using (⌊_⌋; T?; map′; _×-dec_; _→-dec_; toWitness; ¬?)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)

open import Definitions.Behav using (WellBehaved)
open import Definitions.Expr
  using (Sort; s/bool; s/nat; s/unit; Exp; Value; v/bool; v/nat; v/unit
        ; ⊢v_∶_; tv/bool; tv/nat; tv/unit; sort/value
        ; _⊢e_∶_; te/val; te/minus1; te/is-zero; te/var; ⊢e-unique
        ; val; minus1; is-zero; var
        ; s/nat≢s/bool; s/nat≢s/unit)

import Definitions.Typing as Typing

module Check.Alg (N : ℕ) where

  open import Definitions.Graph.Core N hiding (_-<_>->_; step?)
  open import Definitions.Graph.Bisimulation N
    using (Bisimilar; bisim?; bisimulationCorrect; sound; complete)
  open import Definitions.Graph.Action N using (_≟Action_; _≟Sort_)

  module AlgCheck
    (G : Graph)
    (wb : WellBehaved (graphTheory G))
    where

    open Typing.MPST wb
    open import Definitions.Typing.Alg wb

    private
      variable
        γ δ : ℕ

    -- ══════════════════════════════════════════════════════════════════
    --  §0.  Concrete sets: `Vec Bool (size G)`, and generic weight/
    --  monotonicity facts about them (the whole termination argument for
    --  every fixed point below).
    -- ══════════════════════════════════════════════════════════════════

    Bits : Set
    Bits = Vec Bool (size G)

    ⟦_⟧ : Bits → Pred
    ⟦ bits ⟧ t = T (lookup bits t)

    ⊥bits : Bits
    ⊥bits = replicate (size G) false

    ⊥bits-empty : ∀ {i} → T (lookup ⊥bits i) → ⊥
    ⊥bits-empty {i} x = subst T (VecP.lookup-replicate i false) x

    -- Generic facts about `Vec Bool n`, for any `n` (the recursion into a
    -- vector's tail changes its length, so these cannot be pinned to
    -- `Bits = Vec Bool (size G)`).

    wt : ∀ {n} → Vec Bool n → ℕ
    wt [] = 0
    wt (true  ∷ bs) = suc (wt bs)
    wt (false ∷ bs) = wt bs

    wt-bound : ∀ {n} (bs : Vec Bool n) → wt bs ≤ n
    wt-bound [] = z≤n
    wt-bound (true  ∷ bs) = s≤s (wt-bound bs)
    wt-bound (false ∷ bs) = Nat.≤-trans (wt-bound bs) (Nat.n≤1+n _)

    Incl : ∀ {n} → Vec Bool n → Vec Bool n → Set
    Incl bs cs = ∀ i → T (lookup bs i) → T (lookup cs i)

    Incl-refl : ∀ {n} {bs : Vec Bool n} → Incl bs bs
    Incl-refl i x = x

    Incl-trans :
      ∀ {n} {bs cs ds : Vec Bool n} → Incl bs cs → Incl cs ds → Incl bs ds
    Incl-trans f g i x = g i (f i x)

    wt/mono : ∀ {n} {bs cs : Vec Bool n} → Incl bs cs → wt bs ≤ wt cs
    wt/mono {bs = []}         {[]}        incl = z≤n
    wt/mono {bs = true  ∷ bs} {true  ∷ cs} incl =
      s≤s (wt/mono {bs = bs} {cs = cs} (λ i → incl (suc i)))
    wt/mono {bs = true  ∷ bs} {false ∷ cs} incl =
      ⊥-elim (incl zero tt)
    wt/mono {bs = false ∷ bs} {true  ∷ cs} incl =
      Nat.≤-trans
        (wt/mono {bs = bs} {cs = cs} (λ i → incl (suc i))) (Nat.n≤1+n _)
    wt/mono {bs = false ∷ bs} {false ∷ cs} incl =
      wt/mono {bs = bs} {cs = cs} (λ i → incl (suc i))

    -- Strict growth: an inclusion that is not an equality strictly
    -- increases weight.  Induction on both vectors together.
    wt-strict :
      ∀ {n} {bs cs : Vec Bool n} → Incl bs cs → bs ≢ cs → wt bs < wt cs
    wt-strict {bs = []} {[]} incl neq = ⊥-elim (neq refl)
    wt-strict {bs = true ∷ bs} {true ∷ cs} incl neq
      with VecP.≡-dec BoolP._≟_ bs cs
    ... | yes refl = ⊥-elim (neq refl)
    ... | no  bs≢cs =
      s≤s (wt-strict {bs = bs} {cs = cs} (λ i → incl (suc i)) bs≢cs)
    wt-strict {bs = true ∷ bs} {false ∷ cs} incl neq =
      ⊥-elim (incl zero tt)
    wt-strict {bs = false ∷ bs} {true ∷ cs} incl neq =
      s≤s (wt/mono {bs = bs} {cs = cs} (λ i → incl (suc i)))
    wt-strict {bs = false ∷ bs} {false ∷ cs} incl neq
      with VecP.≡-dec BoolP._≟_ bs cs
    ... | yes refl = ⊥-elim (neq refl)
    ... | no  bs≢cs =
      wt-strict {bs = bs} {cs = cs} (λ i → incl (suc i)) bs≢cs

    -- Fuelled iteration, applying `f` OUTERMOST so that `iter (suc k) f x`
    -- unfolds to `f (iter k f x)` definitionally — every equation below
    -- relies on that unfolding rather than a separate `iter-suc` lemma.
    iter : ∀ {A : Set} → ℕ → (A → A) → A → A
    iter zero    f x = x
    iter (suc k) f x = f (iter k f x)

    -- The one fixed-point argument every closure operator below needs:
    -- any INFLATIONARY, MONOTONE endofunction on `Bits` reaches a fixed
    -- point within `suc (size G)` rounds, from ANY starting vector — the
    -- extra round (over the naive `size G` pigeonhole bound) is what makes
    -- this work even when the start is the all-`false` vector (weight 0),
    -- not just a singleton mark.
    private
      grow :
        (f : Bits → Bits)
        → (∀ {bs} → Incl bs (f bs))
        → (∀ {bs cs} → Incl bs cs → Incl (f bs) (f cs))
        → (bs₀ : Bits) (k : ℕ)
        → (wt bs₀ + k ≤ wt (iter k f bs₀))
          ⊎ (f (iter k f bs₀) ≡ iter k f bs₀)
      grow f infl mono bs₀ zero =
        inj₁ (Nat.≤-reflexive (Nat.+-identityʳ (wt bs₀)))
      grow f infl mono bs₀ (suc k)
        with grow f infl mono bs₀ k
      ... | inj₂ fix = inj₂ (cong f fix)
      ... | inj₁ bound
        with VecP.≡-dec BoolP._≟_ (f (iter k f bs₀)) (iter k f bs₀)
      ...   | yes fix = inj₂ (cong f fix)
      ...   | no  ¬fix =
        inj₁
          (subst (_≤ wt (f (iter k f bs₀))) (sym (Nat.+-suc (wt bs₀) k))
            (Nat.≤-trans (s≤s bound)
              (wt-strict {bs = iter k f bs₀} infl (λ eq → ¬fix (sym eq)))))

    fix-within :
      (f : Bits → Bits)
      → (∀ {bs} → Incl bs (f bs))
      → (∀ {bs cs} → Incl bs cs → Incl (f bs) (f cs))
      → (bs₀ : Bits)
      → f (iter (suc (size G)) f bs₀) ≡ iter (suc (size G)) f bs₀
    fix-within f infl mono bs₀
      with grow f infl mono bs₀ (suc (size G))
    ... | inj₂ fix = fix
    ... | inj₁ bound =
      ⊥-elim (Nat.<-irrefl refl
        (Nat.≤-trans (Nat.m≤n+m (suc (size G)) (wt bs₀))
          (Nat.≤-trans bound (wt-bound (iter (suc (size G)) f bs₀)))))

    -- A WEAKER variant: `f` need only include its seed's own one-step
    -- image (not be inflationary at an arbitrary vector) — needed below by
    -- `step₁`, which recomputes each round from `𝒮`/`grows?` rather than
    -- OR-ing in the previous round, so it is inflationary along its OWN
    -- chain from `⊥bits` but not at an arbitrary vector.  The chain
    -- `Incl (iter k f bs₀) (iter (suc k) f bs₀)` for every `k` follows from
    -- the seed fact plus monotonicity alone, by induction on `k` —
    -- everything else repeats `grow`/`fix-within` verbatim against that
    -- chain instead of a general `infl`.
    private
      grow-chain :
        (f : Bits → Bits)
        → (∀ {bs cs} → Incl bs cs → Incl (f bs) (f cs))
        → (bs₀ : Bits) → Incl bs₀ (f bs₀)
        → (k : ℕ)
        → (wt bs₀ + k ≤ wt (iter k f bs₀))
          ⊎ (f (iter k f bs₀) ≡ iter k f bs₀)
      grow-chain f mono bs₀ base zero =
        inj₁ (Nat.≤-reflexive (Nat.+-identityʳ (wt bs₀)))
      grow-chain f mono bs₀ base (suc k)
        with grow-chain f mono bs₀ base k
      ... | inj₂ fix = inj₂ (cong f fix)
      ... | inj₁ bound
        with VecP.≡-dec BoolP._≟_ (f (iter k f bs₀)) (iter k f bs₀)
      ...   | yes fix = inj₂ (cong f fix)
      ...   | no  ¬fix =
        inj₁
          (subst (_≤ wt (f (iter k f bs₀))) (sym (Nat.+-suc (wt bs₀) k))
            (Nat.≤-trans (s≤s bound)
              (wt-strict {bs = iter k f bs₀} (chainIncl k)
                (λ eq → ¬fix (sym eq)))))
        where
          chainIncl : ∀ j → Incl (iter j f bs₀) (f (iter j f bs₀))
          chainIncl zero    = base
          chainIncl (suc j) = mono (chainIncl j)

    fix-within-chain :
      (f : Bits → Bits)
      → (∀ {bs cs} → Incl bs cs → Incl (f bs) (f cs))
      → (bs₀ : Bits) → Incl bs₀ (f bs₀)
      → f (iter (suc (size G)) f bs₀) ≡ iter (suc (size G)) f bs₀
    fix-within-chain f mono bs₀ base
      with grow-chain f mono bs₀ base (suc (size G))
    ... | inj₂ fix = fix
    ... | inj₁ bound =
      ⊥-elim (Nat.<-irrefl refl
        (Nat.≤-trans (Nat.m≤n+m (suc (size G)) (wt bs₀))
          (Nat.≤-trans bound (wt-bound (iter (suc (size G)) f bs₀)))))

    -- The starting point of every fixed point below is always included in
    -- the vector obtained after any number of further rounds — this is all
    -- the "round-count monotonicity" any of them needs.
    incl0 : ∀ (f : Bits → Bits) → (∀ {bs} → Incl bs (f bs))
          → ∀ n (bs₀ : Bits) → Incl bs₀ (iter n f bs₀)
    incl0 f infl zero    bs₀ = Incl-refl {bs = bs₀}
    incl0 f infl (suc n) bs₀ =
      Incl-trans {bs = bs₀} {cs = iter n f bs₀} {ds = f (iter n f bs₀)}
        (incl0 f infl n bs₀) (infl {bs = iter n f bs₀})

    -- A vector `X` that is its own `f`-image is closed under following any
    -- `_-[_]->_` run from one of its own marked states.
    trace-closed :
      (f : Bits → Bits)
      → (X : Bits) → f X ≡ X
      → (∀ {u v α} → T (lookup X u) → u -< α >-> v → T (lookup X v))
      → ∀ {u v αs} → T (lookup X u) → u -[ αs ]-> v → T (lookup X v)
    trace-closed f X fix step Xu tr/refl = Xu
    trace-closed f X fix step Xu (tr/step gr tr) =
      trace-closed f X fix step (step Xu gr) tr

    -- ══════════════════════════════════════════════════════════════════
    --  §1.  Basic decidable primitives
    -- ══════════════════════════════════════════════════════════════════

    T∨ˡ : ∀ {a b} → T a → T (a ∨ b)
    T∨ˡ {true} _ = tt

    T∨ʳ : ∀ {a} b → T b → T (a ∨ b)
    T∨ʳ {true}  b tb = tt
    T∨ʳ {false} b tb = tb

    T∨-elim : ∀ {a b} → T (a ∨ b) → T a ⊎ T b
    T∨-elim {true}  tab = inj₁ tt
    T∨-elim {false} tab = inj₂ tab

    bisim?~ : ∀ (x y : State G) → Dec (x ~ y)
    bisim?~ x y with T? (bisim? G x y)
    ... | yes b = yes (sound (bisimulationCorrect G) b)
    ... | no  ¬b = no (λ r → ¬b (complete (bisimulationCorrect G) r))

    na? : ∀ (P : Part) (s : State G) → Dec (P not-active-in s)
    na? P s with All.all? (λ e → P ∉α? (proj₁ e)) (edges G s)
    ... | yes every =
      yes (λ gr → All.lookup every (step⇒listed {G = G} gr))
    ... | no  ¬every =
      no (λ na → ¬every (All.tabulate (λ mem → na (listed⇒step {G = G} mem))))

    -- Does `s` have a `P`-mentioning edge among its own, immediate steps?
    active? : ∀ (P : Part) (s : State G) → Dec (Any (λ e → P ∈α proj₁ e) (edges G s))
    active? P s = Any.any? (λ e → P ∈α? proj₁ e) (edges G s)

    anyActive→edge :
      ∀ {P} (xs : List (Edge (size G)))
      → Any (λ e → P ∈α proj₁ e) xs
      → Σ[ e ∈ Edge (size G) ] (e ∈ xs × P ∈α proj₁ e)
    anyActive→edge (e ∷ xs) (here px) = e , here refl , px
    anyActive→edge (e ∷ xs) (there a)
      with anyActive→edge xs a
    ... | e′ , mem , px = e′ , there mem , px

    activeToStep :
      ∀ {P s} → Any (λ e → P ∈α proj₁ e) (edges G s) → P ∈T s
    activeToStep {P} {s} a
      with anyActive→edge (edges G s) a
    ... | (α , t) , mem , px = in/α (listed⇒step {G = G} mem) px

    -- ══════════════════════════════════════════════════════════════════
    --  §2.  `∈T?` — unfiltered forward reachability to an active edge.
    --  `P ∈T s` unfolds to "some trace out of `s` mentions `P`"; splitting
    --  that trace at its first `P`-mentioning step turns it into "`s`
    --  reaches, via arbitrary steps, some state with an outgoing `P`-edge",
    --  which is what gets decided here.
    -- ══════════════════════════════════════════════════════════════════

    mem→edgeAny :
      ∀ {t}{xs : List (Edge (size G))}{α} → (α , t) ∈ xs
      → Any (λ e → proj₂ e ≡ t) xs
    mem→edgeAny (here refl) = here refl
    mem→edgeAny (there m)   = there (mem→edgeAny m)

    edgeAny→mem :
      ∀ {t}{xs : List (Edge (size G))} → Any (λ e → proj₂ e ≡ t) xs
      → ∃[ α ] (α , t) ∈ xs
    edgeAny→mem (here {x = (α , t)} refl) = α , here refl
    edgeAny→mem (there {x = e} a) with edgeAny→mem a
    ... | α , mem = α , there mem

    startMark : State G → Bits
    startMark s = tabulate (λ t → ⌊ t FinP.≟ s ⌋)

    startMark-marks : ∀ s → T (lookup (startMark s) s)
    startMark-marks s
      with s FinP.≟ s | VecP.lookup∘tabulate (λ u → ⌊ u FinP.≟ s ⌋) s
    ... | yes _ | eq = subst T (sym eq) tt
    ... | no ¬p | _  = ⊥-elim (¬p refl)

    startMark-sound : ∀ {s t} → T (lookup (startMark s) t) → t ≡ s
    startMark-sound {s} {t} x
      with t FinP.≟ s
         | subst T (VecP.lookup∘tabulate (λ u → ⌊ u FinP.≟ s ⌋) t) x
    ... | yes eq | _  = eq
    ... | no  _  | ()

    edgeTo? : (s t : State G) → Dec (Any (λ e → proj₂ e ≡ t) (edges G s))
    edgeTo? s t = Any.any? (λ e → proj₂ e FinP.≟ t) (edges G s)

    stepReachAny? :
      (bs : Bits) (t : State G)
      → Dec (∃[ s ] T (lookup bs s) × Any (λ e → proj₂ e ≡ t) (edges G s))
    stepReachAny? bs t =
      FinP.any? (λ s → T? (lookup bs s) ×-dec edgeTo? s t)

    expandAll : Bits → Bits
    expandAll bs = tabulate (λ t → lookup bs t ∨ ⌊ stepReachAny? bs t ⌋)

    expandAll-lookup :
      ∀ bs t → lookup (expandAll bs) t ≡ (lookup bs t ∨ ⌊ stepReachAny? bs t ⌋)
    expandAll-lookup bs t = VecP.lookup∘tabulate _ t

    expandAll-infl : ∀ {bs} → Incl bs (expandAll bs)
    expandAll-infl {bs} t x =
      subst T (sym (expandAll-lookup bs t)) (T∨ˡ x)

    expandAll-mono :
      ∀ {bs cs} → Incl bs cs → Incl (expandAll bs) (expandAll cs)
    expandAll-mono {bs} {cs} incl t x
      with T∨-elim (subst T (expandAll-lookup bs t) x)
    ... | inj₁ xb = subst T (sym (expandAll-lookup cs t)) (T∨ˡ (incl t xb))
    ... | inj₂ xr =
      subst T (sym (expandAll-lookup cs t)) (T∨ʳ _ (go xr))
      where
        go : T ⌊ stepReachAny? bs t ⌋ → T ⌊ stepReachAny? cs t ⌋
        go tb with stepReachAny? bs t | stepReachAny? cs t
        ... | yes (u , bsu , anyE) | yes _  = tt
        ... | yes (u , bsu , anyE) | no ¬p  = ⊥-elim (¬p (u , incl u bsu , anyE))
        ... | no  _                | _      = ⊥-elim tb

    expandAll-step :
      ∀ {u t′ α} (bs : Bits) → T (lookup bs u) → u -< α >-> t′
      → T (lookup (expandAll bs) t′)
    expandAll-step {u} {t′} {α} bs bsu gr =
      subst T (sym (expandAll-lookup bs t′)) (T∨ʳ _ go)
      where
        edgeMem : Any (λ e → proj₂ e ≡ t′) (edges G u)
        edgeMem = mem→edgeAny (step⇒listed {G = G} gr)

        go : T ⌊ stepReachAny? bs t′ ⌋
        go with stepReachAny? bs t′
        ... | yes _  = tt
        ... | no  ¬p = ⊥-elim (¬p (u , bsu , edgeMem))

    expandAll-sound :
      ∀ (bs : Bits) (t : State G) → T (lookup (expandAll bs) t)
      → T (lookup bs t) ⊎ (∃[ u ] T (lookup bs u) × ∃[ α ] u -< α >-> t)
    expandAll-sound bs t x
      with T∨-elim (subst T (expandAll-lookup bs t) x)
    ... | inj₁ xb = inj₁ xb
    ... | inj₂ xr with stepReachAny? bs t
    ...   | yes (u , bsu , anyE) =
      inj₂ (u , bsu , proj₁ (edgeAny→mem anyE) , listed⇒step {G = G} (proj₂ (edgeAny→mem anyE)))
    ...   | no ¬p = ⊥-elim xr

    module _ (s : State G) where

      reachAny : Bits
      reachAny = iter (suc (size G)) expandAll (startMark s)

      reachAny-fixed : expandAll reachAny ≡ reachAny
      reachAny-fixed =
        fix-within expandAll (λ {bs} → expandAll-infl {bs})
          (λ {bs} {cs} → expandAll-mono {bs} {cs}) (startMark s)

      reachAny-sound :
        ∀ k (t : State G) → T (lookup (iter k expandAll (startMark s)) t)
        → ∃[ βs ] s -[ βs ]-> t
      reachAny-sound zero t x =
        subst (λ z → ∃[ βs ] s -[ βs ]-> z) (sym (startMark-sound x)) ([] , tr/refl)
      reachAny-sound (suc k) t x
        with expandAll-sound (iter k expandAll (startMark s)) t x
      ... | inj₁ old = reachAny-sound k t old
      ... | inj₂ (u , um , α , gr)
        with reachAny-sound k u um
      ...   | βs , tr = (βs ++ (α ∷ [])) , tr/trans tr (tr/step gr tr/refl)

      reachAny-complete :
        ∀ {t αs} → s -[ αs ]-> t → T (lookup reachAny t)
      reachAny-complete {t} {αs} tr =
        trace-closed expandAll reachAny reachAny-fixed step-closed startProof tr
        where
          step-closed :
            ∀ {u t′ α} → T (lookup reachAny u) → u -< α >-> t′
            → T (lookup reachAny t′)
          step-closed {t′ = t′} Xu gr =
            subst (λ z → T (lookup z t′)) reachAny-fixed
              (expandAll-step reachAny Xu gr)

          startProof : T (lookup reachAny s)
          startProof =
            incl0 expandAll (λ {bs} → expandAll-infl {bs}) (suc (size G))
              (startMark s) s (startMark-marks s)

    ∈T-split :
      ∀ {P s αs t} → s -[ αs ]-> t → Any (P ∈α_) αs
      → ∃[ u ] (∃[ βs ] s -[ βs ]-> u) × Any (λ e → P ∈α proj₁ e) (edges G u)
    ∈T-split {P} (tr/step {G = s} gr rest) (here px) =
      s , ([] , tr/refl) , go (step⇒listed {G = G} gr) px
      where
        go :
          ∀ {xs α t} → (α , t) ∈ xs → P ∈α α
          → Any (λ e → P ∈α proj₁ e) xs
        go (here refl) px = here px
        go (there m)   px = there (go m px)
    ∈T-split (tr/step {α = α} gr rest) (there mem)
      with ∈T-split rest mem
    ... | u , (βs , tr) , act = u , (α ∷ βs , tr/step gr tr) , act

    ∈T? : ∀ (P : Part) (s : State G) → Dec (P ∈T s)
    ∈T? P s
      with FinP.any? (λ t → T? (lookup (reachAny s) t) ×-dec active? P t)
    ... | yes (t , Xt , anyAct) =
      yes (build (reachAny-sound s (suc (size G)) t Xt))
      where
        build : ∃[ βs ] s -[ βs ]-> t → P ∈T s
        build (βs , tr) with anyActive→edge (edges G t) anyAct
        ... | (α , u) , mem , px =
          _ , _ , tr/trans tr (tr/step (listed⇒step {G = G} mem) tr/refl)
          , AnyProp.++⁺ʳ βs (here px)
    ... | no ¬found =
      no (λ { (αs , t , tr , anyMem) →
        let u , (βs , tr′) , act = ∈T-split tr anyMem
        in ¬found (u , reachAny-complete s tr′ , act) })

    -- ══════════════════════════════════════════════════════════════════
    --  §3.  `Reach₀?` — forward reachability FILTERED AT THE ACTION LEVEL.
    --
    --  `Reach₀ P 𝒜 s = ∃ a∈𝒜. a -[¬P]->* s` filters the RUN's labels
    --  (`All (P ∉α_) αs`), not the states it passes through: a state can
    --  have both a `P`-edge and an unrelated edge enabled at once (that is
    --  what the diamond/interleaving axioms are for), so gating on "`P` is
    --  inactive at this whole state" — `na?`, built for `Wait` below, where
    --  that IS the right gate — would wrongly reject a valid witness here
    --  that simply avoids the `P`-edge without the state being wholesale
    --  `P`-free.  Hence a second, independent fixed point, seeded at the
    --  anchor set itself rather than a singleton.
    -- ══════════════════════════════════════════════════════════════════

    EdgeToNotP : Part → State G → List (Edge (size G)) → Set
    EdgeToNotP P t xs = Any (λ e → (proj₂ e ≡ t) × P ∉α proj₁ e) xs

    edgeToNotP? : ∀ P t xs → Dec (EdgeToNotP P t xs)
    edgeToNotP? P t xs =
      Any.any? (λ e → (proj₂ e FinP.≟ t) ×-dec (P ∉α? proj₁ e)) xs

    mem→edgeNotP :
      ∀ {P t xs α} → (α , t) ∈ xs → P ∉α α → EdgeToNotP P t xs
    mem→edgeNotP (here refl) pna = here (refl , pna)
    mem→edgeNotP (there m)   pna = there (mem→edgeNotP m pna)

    edgeNotP→mem :
      ∀ {P t xs} → EdgeToNotP P t xs → ∃[ α ] ((α , t) ∈ xs) × P ∉α α
    edgeNotP→mem {t = t} (here {x = (α , .t)} (refl , pna)) =
      α , here refl , pna
    edgeNotP→mem {t = t} (there {x = e} a)
      with edgeNotP→mem a
    ... | α , mem , pna = α , there mem , pna

    stepReachNotP? :
      (P : Part) (bs : Bits) (t : State G)
      → Dec (∃[ s ] T (lookup bs s) × EdgeToNotP P t (edges G s))
    stepReachNotP? P bs t =
      FinP.any? (λ s → T? (lookup bs s) ×-dec edgeToNotP? P t (edges G s))

    expandNotP : Part → Bits → Bits
    expandNotP P bs = tabulate (λ t → lookup bs t ∨ ⌊ stepReachNotP? P bs t ⌋)

    expandNotP-lookup :
      ∀ P bs t
      → lookup (expandNotP P bs) t ≡ (lookup bs t ∨ ⌊ stepReachNotP? P bs t ⌋)
    expandNotP-lookup P bs t = VecP.lookup∘tabulate _ t

    expandNotP-infl : ∀ {P bs} → Incl bs (expandNotP P bs)
    expandNotP-infl {P} {bs} t x =
      subst T (sym (expandNotP-lookup P bs t)) (T∨ˡ x)

    expandNotP-mono :
      ∀ {P bs cs} → Incl bs cs → Incl (expandNotP P bs) (expandNotP P cs)
    expandNotP-mono {P} {bs} {cs} incl t x
      with T∨-elim (subst T (expandNotP-lookup P bs t) x)
    ... | inj₁ xb =
      subst T (sym (expandNotP-lookup P cs t)) (T∨ˡ (incl t xb))
    ... | inj₂ xr =
      subst T (sym (expandNotP-lookup P cs t)) (T∨ʳ _ (go xr))
      where
        go : T ⌊ stepReachNotP? P bs t ⌋ → T ⌊ stepReachNotP? P cs t ⌋
        go tb with stepReachNotP? P bs t | stepReachNotP? P cs t
        ... | yes (u , bsu , anyE) | yes _  = tt
        ... | yes (u , bsu , anyE) | no ¬p  = ⊥-elim (¬p (u , incl u bsu , anyE))
        ... | no  _                | _      = ⊥-elim tb

    expandNotP-step :
      ∀ {P u t′ α} (bs : Bits) → T (lookup bs u) → u -< α >-> t′ → P ∉α α
      → T (lookup (expandNotP P bs) t′)
    expandNotP-step {P} {u} {t′} bs bsu gr pna =
      subst T (sym (expandNotP-lookup P bs t′)) (T∨ʳ _ go)
      where
        edgeMem : EdgeToNotP P t′ (edges G u)
        edgeMem = mem→edgeNotP (step⇒listed {G = G} gr) pna

        go : T ⌊ stepReachNotP? P bs t′ ⌋
        go with stepReachNotP? P bs t′
        ... | yes _  = tt
        ... | no  ¬p = ⊥-elim (¬p (u , bsu , edgeMem))

    expandNotP-sound :
      ∀ P (bs : Bits) (t : State G) → T (lookup (expandNotP P bs) t)
      → T (lookup bs t)
        ⊎ (∃[ u ] T (lookup bs u) × ∃[ α ] (u -< α >-> t) × P ∉α α)
    expandNotP-sound P bs t x
      with T∨-elim (subst T (expandNotP-lookup P bs t) x)
    ... | inj₁ xb = inj₁ xb
    ... | inj₂ xr with stepReachNotP? P bs t
    ...   | yes (u , bsu , anyE) =
      let α , mem , pna = edgeNotP→mem anyE
      in inj₂ (u , bsu , α , listed⇒step {G = G} mem , pna)
    ...   | no ¬p = ⊥-elim xr

    module _ (P : Part) (𝒜 : Bits) where

      reachNotP : Bits
      reachNotP = iter (suc (size G)) (expandNotP P) 𝒜

      reachNotP-fixed : expandNotP P reachNotP ≡ reachNotP
      reachNotP-fixed =
        fix-within (expandNotP P) (λ {bs} → expandNotP-infl {P} {bs})
          (λ {bs} {cs} → expandNotP-mono {P} {bs} {cs}) 𝒜

      reachNotP-sound :
        ∀ k (t : State G) → T (lookup (iter k (expandNotP P) 𝒜) t)
        → ∃[ a ] T (lookup 𝒜 a) × (a -[¬ P ]->* t)
      reachNotP-sound zero t x = t , x , skip/refl
      reachNotP-sound (suc k) t x
        with expandNotP-sound P (iter k (expandNotP P) 𝒜) t x
      ... | inj₁ old = reachNotP-sound k t old
      ... | inj₂ (u , um , α , gr , pna)
        with reachNotP-sound k u um
      ...   | a , 𝒜a , tr = a , 𝒜a , skip/cat tr (skip/one gr pna)

      reachNotP-complete :
        ∀ {a t} → T (lookup 𝒜 a) → a -[¬ P ]->* t → T (lookup reachNotP t)
      reachNotP-complete {a} {t} 𝒜a (αs , tr , allP) =
        trace-closed¬ tr allP startProof
        where
          step-closed :
            ∀ {u t′ α} → T (lookup reachNotP u) → u -< α >-> t′ → P ∉α α
            → T (lookup reachNotP t′)
          step-closed {t′ = t′} Xu gr pna =
            subst (λ z → T (lookup z t′)) reachNotP-fixed
              (expandNotP-step reachNotP Xu gr pna)

          startProof : T (lookup reachNotP a)
          startProof =
            incl0 (expandNotP P) (λ {bs} → expandNotP-infl {P} {bs})
              (suc (size G)) 𝒜 a 𝒜a

          trace-closed¬ :
            ∀ {u v βs} → u -[ βs ]-> v → All.All (P ∉α_) βs
            → T (lookup reachNotP u) → T (lookup reachNotP v)
          trace-closed¬ tr/refl All.[] Xu = Xu
          trace-closed¬ (tr/step gr tr) (px All.∷ pxs) Xu =
            trace-closed¬ tr pxs (step-closed Xu gr px)

    Reach₀? : ∀ (P : Part) (𝒜 : Bits) (s : State G) → Dec (Reach₀ P ⟦ 𝒜 ⟧ s)
    Reach₀? P 𝒜 s =
      map′ r0-sound r0-complete (T? (lookup (reachNotP P 𝒜) s))
      where
        r0-sound : T (lookup (reachNotP P 𝒜) s) → Reach₀ P ⟦ 𝒜 ⟧ s
        r0-sound x with reachNotP-sound P 𝒜 (suc (size G)) s x
        ... | a , 𝒜a , tr = a , 𝒜a , tr

        r0-complete : Reach₀ P ⟦ 𝒜 ⟧ s → T (lookup (reachNotP P 𝒜) s)
        r0-complete (a , 𝒜a , tr) = reachNotP-complete P 𝒜 𝒜a tr

    -- ══════════════════════════════════════════════════════════════════
    --  §4.  `Wait?` — the `WaitV` search (TODO.md §3.1/§7 step 6).
    --
    --  `P ∈T s` splits the problem into two INDEPENDENT regions:
    --
    --    * `¬ P ∈T s`: `wv/cycle` needs `P ∈T s`, and `∈T` is
    --      BACKWARD-closed (`in/later`), so no cycle can fire anywhere at
    --      or below `s` — the visited set is irrelevant there, and
    --      `WaitV P 𝒮 V s` for ANY `V` is decided by a single, plain least
    --      fixed point (`noCycleTable`), computed ONCE.
    --    * `P ∈T s`: a revisit of the (bisimilarity-closed) visited set
    --      is itself a valid answer (`wv/cycle`), so the visited set
    --      strictly grows on every OTHER recursive step (`wv/step`) — that
    --      is the whole termination argument, no separate measure needed.
    -- ══════════════════════════════════════════════════════════════════

    stepOut? : (s : State G) → Dec (∃[ α ] ∃[ t ] (s -< α >-> t))
    stepOut? s = go (edges G s) refl
      where
        go :
          (xs : List (Edge (size G))) → edges G s ≡ xs
          → Dec (∃[ α ] ∃[ t ] (s -< α >-> t))
        go [] eq =
          no (λ { (α , t , gr) →
            abs (subst ((α , t) ∈_) eq (step⇒listed {G = G} gr)) })
          where
            abs : ∀ {A : Set} {x : A} → x ∈ ([] {A = A}) → ⊥
            abs ()
        go ((α , t) ∷ xs) eq =
          yes (α , t , listed⇒step {G = G} (subst ((α , t) ∈_) (sym eq) (here refl)))

    AllSucc : Bits → State G → Set
    AllSucc X s = ∀ {β u} → s -< β >-> u → T (lookup X u)

    allSucc? : ∀ X s → Dec (AllSucc X s)
    allSucc? X s
      with All.all? (λ e → T? (lookup X (proj₂ e))) (edges G s)
    ... | yes every =
      yes (λ gr → All.lookup every (step⇒listed {G = G} gr))
    ... | no  ¬every =
      no (λ every → ¬every (All.tabulate (λ mem → every (listed⇒step {G = G} mem))))

    module _ (P : Part) (𝒮 : Bits) where

      -- ── The `¬ P ∈T` region: a least fixed point, computed once ──

      Grows : Bits → State G → Set
      Grows X s = (P not-active-in s) × (∃[ α ] ∃[ t ] (s -< α >-> t)) × AllSucc X s

      grows? : ∀ X s → Dec (Grows X s)
      grows? X s with na? P s | stepOut? s | allSucc? X s
      ... | yes na | yes out | yes every = yes (na , out , every)
      ... | no  ¬na | _      | _         = no (λ { (na , _ , _) → ¬na na })
      ... | _       | no ¬out | _        = no (λ { (_ , out , _) → ¬out out })
      ... | _       | _      | no ¬every = no (λ { (_ , _ , e) → ¬every e })

      step₁ : Bits → Bits
      step₁ X = tabulate (λ s → lookup 𝒮 s ∨ ⌊ grows? X s ⌋)

      step₁-lookup :
        ∀ X s → lookup (step₁ X) s ≡ (lookup 𝒮 s ∨ ⌊ grows? X s ⌋)
      step₁-lookup X s = VecP.lookup∘tabulate _ s

      step₁-base : Incl ⊥bits (step₁ ⊥bits)
      step₁-base i x = ⊥-elim (⊥bits-empty x)

      step₁-mono : ∀ {X Y} → Incl X Y → Incl (step₁ X) (step₁ Y)
      step₁-mono {X} {Y} incl i x
        with T∨-elim (subst T (step₁-lookup X i) x)
      ... | inj₁ leaf = subst T (sym (step₁-lookup Y i)) (T∨ˡ leaf)
      ... | inj₂ gr   = subst T (sym (step₁-lookup Y i)) (T∨ʳ _ (go gr))
        where
          go : T ⌊ grows? X i ⌋ → T ⌊ grows? Y i ⌋
          go tg with grows? X i | grows? Y i
          ... | yes (na , out , every) | yes _  = tt
          ... | yes (na , out , every) | no ¬g  =
            ⊥-elim (¬g (na , out , λ gr′ → incl _ (every gr′)))
          ... | no  _                  | _      = ⊥-elim tg

      noCycleTable : Bits
      noCycleTable = iter (suc (size G)) step₁ ⊥bits

      noCycleTable-fixed : step₁ noCycleTable ≡ noCycleTable
      noCycleTable-fixed = fix-within-chain step₁ step₁-mono ⊥bits step₁-base

      table-sound :
        ∀ k {Vpred : Pred} {s}
        → T (lookup (iter k step₁ ⊥bits) s) → WaitV P ⟦ 𝒮 ⟧ Vpred s
      table-sound zero {s = s} x = ⊥-elim (⊥bits-empty x)
      table-sound (suc k) {Vpred} {s} x
        with T∨-elim (subst T (step₁-lookup (iter k step₁ ⊥bits) s) x)
      ... | inj₁ leaf = wv/leaf leaf
      ... | inj₂ gr with grows? (iter k step₁ ⊥bits) s
      ...   | yes (na , (_ , _ , gr′) , every) =
        wv/step na gr′ (λ gr″ → table-sound k (every gr″))
      ...   | no ¬g = ⊥-elim gr

      markIt :
        ∀ {s} → (T (lookup 𝒮 s) ⊎ Grows noCycleTable s)
        → T (lookup noCycleTable s)
      markIt {s} d =
        subst (λ z → T (lookup z s)) noCycleTable-fixed
          (subst T (sym (step₁-lookup noCycleTable s)) (bit d))
        where
          bit2 : Grows noCycleTable s → T ⌊ grows? noCycleTable s ⌋
          bit2 g with grows? noCycleTable s
          ... | yes _  = tt
          ... | no  ¬g = ⊥-elim (¬g g)

          bit :
            (T (lookup 𝒮 s) ⊎ Grows noCycleTable s)
            → T (lookup 𝒮 s ∨ ⌊ grows? noCycleTable s ⌋)
          bit (inj₁ l) = T∨ˡ l
          bit (inj₂ g) = T∨ʳ _ (bit2 g)

      table-complete :
        ∀ {Vpred : Pred} {s}
        → ¬ (P ∈T s) → WaitV P ⟦ 𝒮 ⟧ Vpred s → T (lookup noCycleTable s)
      table-complete ¬inT (wv/leaf x)      = markIt (inj₁ x)
      table-complete ¬inT (wv/cycle _ inT) = ⊥-elim (¬inT inT)
      table-complete ¬inT (wv/step na gr k) =
        markIt
          (inj₂ (na , (_ , _ , gr) ,
            λ gr′ → table-complete (λ inT → ¬inT (in/later gr′ inT)) (k gr′)))

      -- ── The `P ∈T` region: a visited-set walk in which a revisit is
      --    itself a valid answer ──

      Vof : Bits → Pred
      Vof V w = ∃[ a ] T (lookup V a) × (a ~ w)

      vof? : ∀ V w → Dec (Vof V w)
      vof? V w = FinP.any? (λ a → T? (lookup V a) ×-dec bisim?~ a w)

      vof/trans : ∀ {V a w} → Vof V a → a ~ w → Vof V w
      vof/trans (b , vb , b~a) a~w = b , vb , ~trans b~a a~w

      mark : Bits → State G → Bits
      mark V s = tabulate (λ t → lookup V t ∨ ⌊ t FinP.≟ s ⌋)

      mark-lookup :
        ∀ V s t → lookup (mark V s) t ≡ (lookup V t ∨ ⌊ t FinP.≟ s ⌋)
      mark-lookup V s t = VecP.lookup∘tabulate _ t

      mark-in : ∀ V s → T (lookup (mark V s) s)
      mark-in V s with s FinP.≟ s | mark-lookup V s s
      ... | yes _ | eq = subst T (sym eq) (T∨ʳ _ tt)
      ... | no ¬p | _  = ⊥-elim (¬p refl)

      mark-old : ∀ V s {t} → T (lookup V t) → T (lookup (mark V s) t)
      mark-old V s {t} x = subst T (sym (mark-lookup V s t)) (T∨ˡ x)

      mark-sound : ∀ V s {t} → T (lookup (mark V s) t) → T (lookup V t) ⊎ (t ≡ s)
      mark-sound V s {t} x
        with T∨-elim (subst T (mark-lookup V s t) x)
      ... | inj₁ tv = inj₁ tv
      ... | inj₂ te = inj₂ (toWitness te)

      vof/mark→ : ∀ V s {w} → Vof (mark V s) w → Vof V w ⊎ (s ~ w)
      vof/mark→ V s (a , ma , a~w) with mark-sound V s ma
      ... | inj₁ va   = inj₁ (a , va , a~w)
      ... | inj₂ refl = inj₂ a~w

      vof/mark← : ∀ V s {w} → Vof V w ⊎ (s ~ w) → Vof (mark V s) w
      vof/mark← V s (inj₁ (a , va , a~w)) = a , mark-old V s va , a~w
      vof/mark← V s (inj₂ s~w)            = s , mark-in V s , s~w

      AllWait : Bits → State G → Set₁
      AllWait W s = ∀ {β u} → s -< β >-> u → WaitV P ⟦ 𝒮 ⟧ (Vof W) u

      allWait? :
        ∀ W s → (∀ u → Dec (WaitV P ⟦ 𝒮 ⟧ (Vof W) u)) → Dec (AllWait W s)
      allWait? W s dec with All.all? (λ e → dec (proj₂ e)) (edges G s)
      ... | yes every =
        yes (λ gr → All.lookup every (step⇒listed {G = G} gr))
      ... | no  ¬every =
        no (λ every → ¬every (All.tabulate (λ mem → every (listed⇒step {G = G} mem))))

      -- The visited set strictly grows on every recursive call: if it did
      -- not, `s` would already be its own anchor (`~refl`), contradicting
      -- `¬anc` below. No separate phase/size measure is needed.
      smaller : ∀ V s → ¬ Vof V s → size G ∸ wt (mark V s) < size G ∸ wt V
      smaller V s ¬anc =
        Nat.∸-monoʳ-<
          (wt-strict {bs = V} {cs = mark V s} (λ i x → mark-old V s x)
            (λ e → ¬anc (s , subst (λ z → T (lookup z s)) (sym e) (mark-in V s) , ~refl)))
          (wt-bound (mark V s))

      WaitV?-acc :
        ∀ V s → Acc _<_ (size G ∸ wt V) → Dec (WaitV P ⟦ 𝒮 ⟧ (Vof V) s)
      WaitV?-acc V s (acc rs) with T? (lookup 𝒮 s)
      ... | yes leaf = yes (wv/leaf leaf)
      ... | no  ¬leaf with ∈T? P s
      ...   | no ¬inT =
        map′ (table-sound (suc (size G))) (table-complete ¬inT)
          (T? (lookup noCycleTable s))
      ...   | yes inT with vof? V s
      ...     | yes anc = yes (wv/cycle (s , anc , ~refl) inT)
      ...     | no  ¬anc with na? P s | stepOut? s
      ...       | no ¬na | _ =
        no (λ { (wv/leaf x)               → ¬leaf x
              ; (wv/cycle (a , va , a~s) _) → ¬anc (vof/trans {V = V} va a~s)
              ; (wv/step na _ _)          → ¬na na })
      ...       | yes _  | no ¬out =
        no (λ { (wv/leaf x)               → ¬leaf x
              ; (wv/cycle (a , va , a~s) _) → ¬anc (vof/trans {V = V} va a~s)
              ; (wv/step _ gr _)          → ¬out (_ , _ , gr) })
      ...       | yes na | yes (_ , _ , gr)
        with allWait? (mark V s) s
               (λ u → WaitV?-acc (mark V s) u (rs (smaller V s ¬anc)))
      ...         | yes every =
        yes (wv/step na gr (λ gr′ → waitV/mono (vof/mark→ V s) (every gr′)))
      ...         | no ¬every =
        no (λ { (wv/leaf x)               → ¬leaf x
              ; (wv/cycle (a , va , a~s) _) → ¬anc (vof/trans {V = V} va a~s)
              ; (wv/step _ _ k)           →
                  ¬every (λ gr′ → waitV/mono (vof/mark← V s) (k gr′)) })

      Wait? : (s : State G) → Dec (Wait P ⟦ 𝒮 ⟧ s)
      Wait? s =
        map′ (waitV/mono empty→) (waitV/mono →empty)
          (WaitV?-acc ⊥bits s (<-wellFounded (size G ∸ wt ⊥bits)))
        where
          empty→ : ∀ {w} → Vof ⊥bits w → ⊥
          empty→ (a , x , _) = ⊥-elim (⊥bits-empty x)

          →empty : ∀ {w} → ⊥ → Vof ⊥bits w
          →empty ()

    -- ══════════════════════════════════════════════════════════════════
    --  §5.  `algSet` — deciding `_&_⊢a_∶_` itself (TODO.md §7 step 6).
    --
    --  Read every rule as an algorithm: find its existentials, decide its
    --  premises, and the two usually go hand in hand.  `𝒮` occurs only in
    --  `⊆`-premises in each rule, so validity is closed under arbitrary
    --  union (a bigger `𝒮` only ever has to satisfy the SAME `sub`/`done`,
    --  and `Wait`/`Reach₀` are monotone in their leaf — `waitV/leaf-mono`,
    --  already proved), so there IS a genuine largest `𝒮` at each `Pr`,
    --  reached by always plugging in the recursively-largest continuation.
    --
    --  `tclosed`/`⌈W⌉`-closure is the one place this needs NEW lemmas
    --  (not the open, unproved "any derivation normalises to closed sets"
    --  from TODO.md §5.2′ — that is not needed here): `algSet` maintains,
    --  by construction, that the set it returns is `~`-closed, by
    --  induction on `Pr`, using `∈~`/`wait/~`/`reach₀/~`/`⌈⌉/closed`
    --  (already proved) plus the two small facts below.
    -- ══════════════════════════════════════════════════════════════════

    T∧-elim : ∀ {a b} → T (a ∧ b) → T a × T b
    T∧-elim {true} tab = tt , tab

    T∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
    T∧-intro {true} ta tb = tb

    -- Intersection and union of concrete sets, and their closure.

    _∩b_ : Bits → Bits → Bits
    bs ∩b cs = tabulate (λ i → lookup bs i ∧ lookup cs i)

    ∩b-lookup : ∀ bs cs i → lookup (bs ∩b cs) i ≡ (lookup bs i ∧ lookup cs i)
    ∩b-lookup bs cs i = VecP.lookup∘tabulate _ i

    ∩b-closed : ∀ {bs cs} → Closed ⟦ bs ⟧ → Closed ⟦ cs ⟧ → Closed ⟦ bs ∩b cs ⟧
    ∩b-closed {bs} {cs} cb cc {u} {t} u~t x
      with T∧-elim (subst T (∩b-lookup bs cs u) x)
    ... | xb , xc =
      subst T (sym (∩b-lookup bs cs t)) (T∧-intro (cb u~t xb) (cc u~t xc))

    _∪b_ : Bits → Bits → Bits
    bs ∪b cs = tabulate (λ i → lookup bs i ∨ lookup cs i)

    ∪b-lookup : ∀ bs cs i → lookup (bs ∪b cs) i ≡ (lookup bs i ∨ lookup cs i)
    ∪b-lookup bs cs i = VecP.lookup∘tabulate _ i

    ∪b-closed : ∀ {bs cs} → Closed ⟦ bs ⟧ → Closed ⟦ cs ⟧ → Closed ⟦ bs ∪b cs ⟧
    ∪b-closed {bs} {cs} cb cc {u} {t} u~t x
      with T∨-elim (subst T (∪b-lookup bs cs u) x)
    ... | inj₁ xb = subst T (sym (∪b-lookup bs cs t)) (T∨ˡ (cb u~t xb))
    ... | inj₂ xc = subst T (sym (∪b-lookup bs cs t)) (T∨ʳ _ (cc u~t xc))

    -- The `~`-closed singleton `⌈ W ⌉`, concretely: everything bisimilar
    -- to `W`.
    closure : State G → Bits
    closure W = tabulate (λ s → ⌊ bisim?~ W s ⌋)

    closure-lookup : ∀ W s → lookup (closure W) s ≡ ⌊ bisim?~ W s ⌋
    closure-lookup W s = VecP.lookup∘tabulate _ s

    closure-sound : ∀ {W s} → T (lookup (closure W) s) → W ~ s
    closure-sound {W} {s} x = toWitness (subst T (closure-lookup W s) x)

    closure-complete : ∀ {W s} → W ~ s → T (lookup (closure W) s)
    closure-complete {W} {s} w~s
      with bisim?~ W s | closure-lookup W s
    ... | yes _    | eq = subst T (sym eq) tt
    ... | no ¬w~s  | _  = ⊥-elim (¬w~s w~s)

    closure-closed : ∀ {W} → Closed ⟦ closure W ⟧
    closure-closed {W} {u} {t} u~t x =
      closure-complete (~trans (closure-sound x) u~t)

    -- Closure of the leaf families `s/send`/`s/recv` build `Wait` over,
    -- given the continuation's own closure — the two facts TODO.md §5.2′
    -- would otherwise have needed a general (unproved) theorem for.

    sendLeaf-closed :
      ∀ {α} {𝒯 : Pred} → Closed 𝒯
      → Closed (λ u → ∃[ u′ ] (u -< α >-> u′) × 𝒯 u′)
    sendLeaf-closed tc u~v (u′ , gr , tu′) =
      let v′ , gr′ , u′~v′ = ~L u~v gr
      in v′ , gr′ , tc u′~v′ tu′

    recvLeaf-closed :
      ∀ {P′ Q I} {𝒯 : Fin (suc I) → Sort → Pred}
      → (∀ {j U} → Closed (𝒯 j U))
      → Closed
          (λ u →
            (Σ[ j ∈ Fin (suc I) ] ∃[ U ] ∃[ t ] (u -< P′ ⟶ Q # j < U > >-> t))
            × (∀ {j U t} → u -< P′ ⟶ Q # j < U > >-> t → 𝒯 j U t))
    recvLeaf-closed tc {u} {w} u~w ((j , U , t , gr) , cov) =
      let t′ , gr′ , t~t′ = ~L u~w gr
      in (j , U , t′ , gr′)
       , λ gr₂ →
           let t₁ , gr₁ , t₁~t₂ = ~R u~w gr₂
           in tc t₁~t₂ (cov gr₁)

    -- ── Two more decidable, structural pieces every rule needs ──

    valTyped : ∀ V → ⊢v V ∶ sort/value V
    valTyped (v/bool _) = tv/bool
    valTyped (v/nat _)  = tv/nat
    valTyped v/unit     = tv/unit

    inferExpr? : ∀ {γ} (Γ : Vec Sort γ) (E : Exp γ) → Dec (Σ[ S ∈ Sort ] Γ ⊢e E ∶ S)
    inferExpr? Γ (val V) = yes (sort/value V , te/val (valTyped V))
    inferExpr? Γ (minus1 E) with inferExpr? Γ E
    ... | yes (s/nat  , td) = yes (s/nat , te/minus1 td)
    ... | yes (s/bool , td) = no (λ { (_ , te/minus1 td′) → s/nat≢s/bool (⊢e-unique td′ td) })
    ... | yes (s/unit , td) = no (λ { (_ , te/minus1 td′) → s/nat≢s/unit (⊢e-unique td′ td) })
    ... | no ¬E             = no (λ { (_ , te/minus1 td) → ¬E (s/nat , td) })
    inferExpr? Γ (is-zero E) with inferExpr? Γ E
    ... | yes (s/nat  , td) = yes (s/bool , te/is-zero td)
    ... | yes (s/bool , td) = no (λ { (_ , te/is-zero td′) → s/nat≢s/bool (⊢e-unique td′ td) })
    ... | yes (s/unit , td) = no (λ { (_ , te/is-zero td′) → s/nat≢s/unit (⊢e-unique td′ td) })
    ... | no ¬E             = no (λ { (_ , te/is-zero td) → ¬E (s/nat , td) })
    inferExpr? Γ (var x) = yes (lookup Γ x , te/var)

    checkExpr? : ∀ {γ} (Γ : Vec Sort γ) (E : Exp γ) (S : Sort) → Dec (Γ ⊢e E ∶ S)
    checkExpr? Γ E S with inferExpr? Γ E
    ... | no ¬wt = no (λ etd → ¬wt (S , etd))
    ... | yes (S′ , etd) with S ≟Sort S′
    ...   | yes refl = yes etd
    ...   | no S≢S′  = no (λ etd′ → S≢S′ (⊢e-unique etd′ etd))

    messageGuarded? : ∀ {γ δ} (Pr : Proc γ δ) → Dec (MessageGuarded Pr)
    messageGuarded? (_ ! _ < _ >∙ _) = yes mg/send
    messageGuarded? (Σ _ ？· _)      = yes mg/recv
    messageGuarded? (ifp _ then A else B)
      with messageGuarded? A | messageGuarded? B
    ... | yes ga | yes gb = yes (mg/if ga gb)
    ... | no ¬ga | _      = no (λ { (mg/if ga gb) → ¬ga ga })
    ... | _      | no ¬gb = no (λ { (mg/if ga gb) → ¬gb gb })
    messageGuarded? (rec _) = no (λ ())
    messageGuarded? (v _)   = no (λ ())
    messageGuarded? ∅       = no (λ ())

    -- `Sort` has exactly three constructors, so a bound quantifier over it
    -- is decided by three-way case split, not a general enumeration.
    anySort? : ∀ {ϕ : Sort → Set} → (∀ U → Dec (ϕ U)) → Dec (∃[ U ] ϕ U)
    anySort? dec with dec s/bool | dec s/nat | dec s/unit
    ... | yes p | _     | _     = yes (s/bool , p)
    ... | _     | yes p | _     = yes (s/nat , p)
    ... | _     | _     | yes p = yes (s/unit , p)
    ... | no ¬a | no ¬b | no ¬c =
      no (λ { (s/bool , p) → ¬a p ; (s/nat , p) → ¬b p ; (s/unit , p) → ¬c p })

    allSort? : ∀ {ϕ : Sort → Set} → (∀ U → Dec (ϕ U)) → Dec (∀ U → ϕ U)
    allSort? dec with dec s/bool | dec s/nat | dec s/unit
    ... | yes a | yes b | yes c =
      yes (λ { s/bool → a ; s/nat → b ; s/unit → c })
    ... | no ¬a | _     | _     = no (λ f → ¬a (f s/bool))
    ... | _     | no ¬b | _     = no (λ f → ¬b (f s/nat))
    ... | _     | _     | no ¬c = no (λ f → ¬c (f s/unit))

    -- ── Bridging any decidable, abstractly-specified `Pred` to a concrete
    --    `Bits` vector, uniformly — every leaf below is built this way. ──

    -- Level-polymorphic in the DECIDED proposition (not in `Bits`, which is
    -- always `Set`): `Wait`/`WaitV` land in `Set₁`, so leaves built from
    -- them need this to unify against `Dec` at that level.
    toBits : ∀ {ℓ} {ϕ : Behav → Set ℓ} → (∀ (s : State G) → Dec (ϕ s)) → Bits
    toBits dec = tabulate (λ s → ⌊ dec s ⌋)

    toBits-lookup :
      ∀ {ℓ} {ϕ : Behav → Set ℓ} (dec : ∀ s → Dec (ϕ s)) s
      → lookup (toBits dec) s ≡ ⌊ dec s ⌋
    toBits-lookup dec s = VecP.lookup∘tabulate _ s

    toBits-sound :
      ∀ {ℓ} {ϕ : Behav → Set ℓ} (dec : ∀ s → Dec (ϕ s)) {s}
      → T (lookup (toBits dec) s) → ϕ s
    toBits-sound dec {s} x with dec s | subst T (toBits-lookup dec s) x
    ... | yes p | _  = p
    ... | no ¬p | ()

    toBits-complete :
      ∀ {ℓ} {ϕ : Behav → Set ℓ} (dec : ∀ s → Dec (ϕ s)) {s}
      → ϕ s → T (lookup (toBits dec) s)
    toBits-complete dec {s} p
      with dec s | toBits-lookup dec s
    ... | yes _  | eq = subst T (sym eq) tt
    ... | no ¬p  | _  = ⊥-elim (¬p p)

    decided-closed :
      ∀ {ℓ} {ϕ : Behav → Set ℓ} (bits : Bits)
      → (∀ {s} → T (lookup bits s) → ϕ s)
      → (∀ {s} → ϕ s → T (lookup bits s))
      → Closed ϕ → Closed ⟦ bits ⟧
    decided-closed bits snd cmp cl u~v x = cmp (cl u~v (snd x))

    toBits-closed :
      ∀ {ℓ} {ϕ : Behav → Set ℓ} (dec : ∀ s → Dec (ϕ s)) → Closed ϕ → Closed ⟦ toBits dec ⟧
    toBits-closed dec = decided-closed (toBits dec) (toBits-sound dec) (toBits-complete dec)

    -- ── A generic "search the edges of `u`" decision, reused by `s/send`
    --    (exact action match) and `s/recv` (shape match) alike. ──

    AnyEdge : (Action → State G → Set) → State G → Set
    AnyEdge Ψ u = Any (λ e → Ψ (proj₁ e) (proj₂ e)) (edges G u)

    anyEdge? :
      ∀ {Ψ : Action → State G → Set} → (∀ α t → Dec (Ψ α t))
      → ∀ u → Dec (AnyEdge Ψ u)
    anyEdge? dec u = Any.any? (λ e → dec (proj₁ e) (proj₂ e)) (edges G u)

    anyEdge→mem :
      ∀ {Ψ : Action → State G → Set} {u} → AnyEdge Ψ u
      → ∃[ α ] ∃[ t ] ((α , t) ∈ edges G u) × Ψ α t
    anyEdge→mem {Ψ} {u} mem = go (edges G u) mem
      where
        go :
          (xs : List (Edge (size G))) → Any (λ e → Ψ (proj₁ e) (proj₂ e)) xs
          → ∃[ α ] ∃[ t ] ((α , t) ∈ xs) × Ψ α t
        go (e ∷ xs) (here px) = proj₁ e , proj₂ e , here refl , px
        go (e ∷ xs) (there a) with go xs a
        ... | α , t , mem′ , ψ = α , t , there mem′ , ψ

    anyEdge→step :
      ∀ {Ψ : Action → State G → Set} {u} → AnyEdge Ψ u
      → ∃[ α ] ∃[ t ] (u -< α >-> t) × Ψ α t
    anyEdge→step {Ψ} {u} mem
      with anyEdge→mem {Ψ} {u} mem
    ... | α , t , mem′ , ψ = α , t , listed⇒step {G = G} mem′ , ψ

    step→anyEdge :
      ∀ {Ψ : Action → State G → Set} {u α t} → u -< α >-> t → Ψ α t
      → AnyEdge Ψ u
    step→anyEdge {Ψ} gr ψ = go (step⇒listed {G = G} gr) ψ
      where
        go :
          ∀ {xs α t} → (α , t) ∈ xs → Ψ α t
          → Any (λ e → Ψ (proj₁ e) (proj₂ e)) xs
        go (here refl) ψ = here ψ
        go (there m)   ψ = there (go m ψ)

    -- ══════════════════════════════════════════════════════════════════
    --  §5a. `algSet` — one case per rule.  A rule is untypeable at ANY 𝒮
    --  only via an UNCONDITIONAL, 𝒮-independent premise failing (`etd` in
    --  `s/send`/`s/if`, `mg` in `s/rec` — and, for `s/if`, either branch
    --  itself being untypeable at any set).  `s/recv`/`s/var`/`s/end`, and
    --  `s/rec` once `mg` holds, are always typeable at least at `∅`.
    -- ══════════════════════════════════════════════════════════════════

    AlgOK : ∀ {γ δ} → Vec Sort γ → Vec Behav δ → Part → Proc γ δ → Set₁
    AlgOK Γ Δ P Pr = Σ[ bits ∈ Bits ] (Γ & Δ ⊢a P ◂ Pr ∶ ⟦ bits ⟧) × Closed ⟦ bits ⟧

    AlgResult : ∀ {γ δ} → Vec Sort γ → Vec Behav δ → Part → Proc γ δ → Set₁
    AlgResult Γ Δ P Pr =
      AlgOK Γ Δ P Pr ⊎ ¬ (Σ[ 𝒮 ∈ Pred ] Γ & Δ ⊢a P ◂ Pr ∶ 𝒮)

    resultBits : ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec Behav δ} {P Pr} → AlgResult Γ Δ P Pr → Bits
    resultBits (inj₁ (bits , _ , _)) = bits
    resultBits (inj₂ _)              = ⊥bits

    resultClosed :
      ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec Behav δ} {P Pr} (r : AlgResult Γ Δ P Pr)
      → Closed ⟦ resultBits r ⟧
    resultClosed (inj₁ (_ , _ , cl)) = cl
    resultClosed (inj₂ _)            = λ _ x → ⊥-elim (⊥bits-empty x)

    algSet : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec Behav δ) (P : Part) (Pr : Proc γ δ) → AlgResult Γ Δ P Pr

    algBr :
      ∀ {γ δ n} (Γ : Vec Sort γ) (Δ : Vec Behav δ) (Q : Part)
      (Br : Vec (Proc (suc γ) δ) n) (j : Fin n) (U : Sort)
      → AlgResult (U ∷ Γ) Δ Q (lookup Br j)

    -- `∅` — `a/end`'s only field is `𝒮`-conditional, so this is always
    -- typeable; the largest set is exactly `{s | ¬ P ∈T s}`, closed
    -- because `∈T` itself is (`∈~`).
    algSet Γ Δ P ∅ =
      inj₁ (toBits dec , a/end (toBits-sound dec) , toBits-closed dec endClosed)
      where
        dec : ∀ s → Dec (¬ (P ∈T s))
        dec s = ¬? (∈T? P s)

        endClosed : Closed (λ s → ¬ (P ∈T s))
        endClosed u~w ¬pu pw = ¬pu (∈~ (~sym u~w) pw)

    -- `v X` — likewise always typeable; largest set is `Wait P (Reach₀ P
    -- ⌈ lookup Δ X ⌉)`, closed via `wait/~`/`reach₀/~`/`⌈⌉/closed` (`Alg.agda`)
    -- bridged from the concrete `reachNotP` through `reachNotP-sound`.
    algSet Γ Δ P (v X) =
      inj₁ (toBits waitDec , a/var sub , toBits-closed waitDec waitClosed)
      where
        anchorBits : Bits
        anchorBits = closure (lookup Δ X)

        waitDec : ∀ s → Dec (Wait P ⟦ reachNotP P anchorBits ⟧ s)
        waitDec s = Wait? P (reachNotP P anchorBits) s

        bridge : ∀ {s} → ⟦ reachNotP P anchorBits ⟧ s → Reach₀ P ⌈ lookup Δ X ⌉ s
        bridge {s} x =
          let a , 𝒜a , tr = reachNotP-sound P anchorBits (suc (size G)) s x
          in a , closure-sound 𝒜a , tr

        sub : ∀ {s} → T (lookup (toBits waitDec) s) → Wait P (Reach₀ P ⌈ lookup Δ X ⌉) s
        sub {s} m = waitV/leaf-mono bridge (toBits-sound waitDec m)

        reach-closed : Closed ⟦ reachNotP P anchorBits ⟧
        reach-closed = decided-closed (reachNotP P anchorBits) snd′ cmp′ (reach₀/~ closure-closed)
          where
            snd′ : ∀ {s} → T (lookup (reachNotP P anchorBits) s) → Reach₀ P ⟦ anchorBits ⟧ s
            snd′ {s} x =
              let a , 𝒜a , tr = reachNotP-sound P anchorBits (suc (size G)) s x
              in a , 𝒜a , tr

            cmp′ : ∀ {s} → Reach₀ P ⟦ anchorBits ⟧ s → T (lookup (reachNotP P anchorBits) s)
            cmp′ (a , 𝒜a , tr) = reachNotP-complete P anchorBits 𝒜a tr

        waitClosed : Closed (Wait P ⟦ reachNotP P anchorBits ⟧)
        waitClosed = wait/~ reach-closed

    -- `ifp E then A else B` — untypeable at any 𝒮 iff `E` isn't boolean,
    -- or either branch is untypeable at any 𝒮; otherwise the largest set
    -- is the intersection of both branches' largest sets.
    algSet Γ Δ P (ifp E then A else B) with checkExpr? Γ E s/bool
    ... | no ¬bt = inj₂ (λ { (𝒮 , a/if etd _ _) → ¬bt etd })
    ... | yes etd with algSet Γ Δ P A | algSet Γ Δ P B
    ...   | inj₂ ¬A | _ = inj₂ (λ { (𝒮 , a/if _ ttd _) → ¬A (𝒮 , ttd) })
    ...   | _ | inj₂ ¬B = inj₂ (λ { (𝒮 , a/if _ _ ftd) → ¬B (𝒮 , ftd) })
    ...   | inj₁ (bitsA , derivA , closedA) | inj₁ (bitsB , derivB , closedB) =
      inj₁
        ( bitsA ∩b bitsB
        , a/if etd (alg/mono narrowA derivA) (alg/mono narrowB derivB)
        , ∩b-closed {bs = bitsA} {cs = bitsB} closedA closedB
        )
      where
        narrowA : ∀ {s} → T (lookup (bitsA ∩b bitsB) s) → T (lookup bitsA s)
        narrowA {s} x = proj₁ (T∧-elim (subst T (∩b-lookup bitsA bitsB s) x))

        narrowB : ∀ {s} → T (lookup (bitsA ∩b bitsB) s) → T (lookup bitsB s)
        narrowB {s} x = proj₂ (T∧-elim (subst T (∩b-lookup bitsA bitsB s) x))

    -- `Q ! i < E >∙ Pr` — untypeable at any 𝒮 iff `E` has no sort, or the
    -- continuation is untypeable at any 𝒮; otherwise the largest set is
    -- `Wait P (leaf)` for the recursively-largest continuation.
    algSet Γ Δ P (Q ! i < E >∙ Pr) with inferExpr? Γ E
    ... | no ¬ex = inj₂ (λ { (𝒮 , a/send {S = S} etd _ _ _) → ¬ex (S , etd) })
    ... | yes (S , etd) with algSet Γ Δ P Pr
    ...   | inj₂ ¬Pr = inj₂ (λ { (𝒮 , a/send _ td _ _) → ¬Pr (_ , td) })
    ...   | inj₁ (bits , deriv , closed) =
      inj₁ (toBits waitDec , a/send etd deriv closed sub , toBits-closed waitDec waitClosed)
      where
        Ψ : Action → State G → Set
        Ψ α t = (α ≡ (P ⟶ Q # i < S >)) × T (lookup bits t)

        Ψ? : ∀ α t → Dec (Ψ α t)
        Ψ? α t = (α ≟Action (P ⟶ Q # i < S >)) ×-dec T? (lookup bits t)

        leaf : Pred
        leaf u = ∃[ u′ ] (u -< P ⟶ Q # i < S > >-> u′) × ⟦ bits ⟧ u′

        leafDec : ∀ u → Dec (leaf u)
        leafDec u = map′ snd′ cmp′ (anyEdge? Ψ? u)
          where
            snd′ : AnyEdge Ψ u → leaf u
            snd′ mem with anyEdge→step mem
            ... | α , t , gr , (refl , tb) = t , gr , tb

            cmp′ : leaf u → AnyEdge Ψ u
            cmp′ (t , gr , tb) = step→anyEdge gr (refl , tb)

        waitDec : ∀ s → Dec (Wait P ⟦ toBits leafDec ⟧ s)
        waitDec s = Wait? P (toBits leafDec) s

        bridge : ∀ {u} → ⟦ toBits leafDec ⟧ u → ∃[ u′ ] (u -< P ⟶ Q # i < S > >-> u′) × ⟦ bits ⟧ u′
        bridge {u} x = toBits-sound leafDec x

        sub :
          ∀ {s} → T (lookup (toBits waitDec) s)
          → Wait P (λ u → ∃[ u′ ] (u -< P ⟶ Q # i < S > >-> u′) × ⟦ bits ⟧ u′) s
        sub {s} m = waitV/leaf-mono bridge (toBits-sound waitDec m)

        leafClosed : Closed leaf
        leafClosed = sendLeaf-closed closed

        waitClosed : Closed (Wait P ⟦ toBits leafDec ⟧)
        waitClosed = wait/~ (toBits-closed leafDec leafClosed)

    -- `Σ S ？· Br` — always typeable at least at `∅` (`s/recv`'s own
    -- fields are all `𝒮`/`𝒯`-conditional).  `algBr` makes `lookup Br j`
    -- structural (`Br` shrinks going in, the branch shrinks coming out) —
    -- `lookup Br j` itself is not a subterm `Br` as far as the termination
    -- checker can see, so calling `algSet` on it directly would not do.
    algSet Γ Δ Q (Σ_？·_ S {I} Br) =
      inj₁ (toBits waitDec , a/recv conts (λ {j} {U} → 𝒯closed {j} {U}) sub , toBits-closed waitDec waitClosed)
      where
        𝒯 : Fin (suc I) → Sort → Pred
        𝒯 j U = ⟦ resultBits (algBr Γ Δ Q Br j U) ⟧

        𝒯closed : ∀ {j U} → Closed (𝒯 j U)
        𝒯closed {j} {U} = resultClosed (algBr Γ Δ Q Br j U)

        conts : ∀ {j U t} → 𝒯 j U t → (U ∷ Γ) & Δ ⊢a Q ◂ lookup Br j ∶ 𝒯 j U
        conts {j} {U} {t} tjut with algBr Γ Δ Q Br j U
        ... | inj₁ (bits , deriv , _) = deriv
        ... | inj₂ _ = ⊥-elim (⊥bits-empty tjut)

        MatchΨ : Action → State G → Set
        MatchΨ α _ = Σ[ j ∈ Fin (suc I) ] ∃[ U ] (α ≡ (S ⟶ Q # j < U >))

        MatchΨ? : ∀ α t → Dec (MatchΨ α t)
        MatchΨ? α _ =
          FinP.any? (λ j → anySort? (λ U → α ≟Action (S ⟶ Q # j < U >)))

        CoversAt : Edge (size G) → Set
        CoversAt (α , t) = ∀ j U → α ≡ (S ⟶ Q # j < U >) → 𝒯 j U t

        coversAt? : ∀ e → Dec (CoversAt e)
        coversAt? (α , t) =
          FinP.all? (λ j → allSort? (λ U → (α ≟Action (S ⟶ Q # j < U >)) →-dec T? (lookup (resultBits (algBr Γ Δ Q Br j U)) t)))

        leaf : Pred
        leaf u =
          (Σ[ j ∈ Fin (suc I) ] ∃[ U ] ∃[ t ] (u -< S ⟶ Q # j < U > >-> t))
          × (∀ {j U t} → u -< S ⟶ Q # j < U > >-> t → 𝒯 j U t)

        leafDec : ∀ u → Dec (leaf u)
        leafDec u = map′ snd′ cmp′ (anyEdge? MatchΨ? u ×-dec All.all? coversAt? (edges G u))
          where
            snd′ : AnyEdge MatchΨ u × All.All CoversAt (edges G u) → leaf u
            snd′ (mem , allOK) with anyEdge→step mem
            ... | α , t , gr , (j , U , eq) =
              (j , U , t , subst (λ a → u -< a >-> t) eq gr)
              , (λ {j′} {U′} {t′} gr′ → All.lookup allOK (step⇒listed {G = G} gr′) j′ U′ refl)

            cmp′ : leaf u → AnyEdge MatchΨ u × All.All CoversAt (edges G u)
            cmp′ ((j , U , t , gr) , cov) =
              step→anyEdge gr (j , U , refl)
              , All.tabulate
                  (λ {e} mem j′ U′ eq →
                    cov (subst (λ a → u -< a >-> proj₂ e) eq (listed⇒step {G = G} mem)))

        waitDec : ∀ s → Dec (Wait Q ⟦ toBits leafDec ⟧ s)
        waitDec s = Wait? Q (toBits leafDec) s

        sub : ∀ {s} → T (lookup (toBits waitDec) s) → Wait Q leaf s
        sub {s} m = waitV/leaf-mono (toBits-sound leafDec) (toBits-sound waitDec m)

        leafClosed : Closed leaf
        leafClosed = recvLeaf-closed 𝒯closed

        waitClosed : Closed (Wait Q ⟦ toBits leafDec ⟧)
        waitClosed = wait/~ (toBits-closed leafDec leafClosed)

    -- `rec Pr` — untypeable at any 𝒮 iff `Pr` isn't `MessageGuarded`
    -- (unconditional); otherwise always typeable at least at `∅`.  The
    -- anchor set is the union, over every `W : State G` that PASSES
    -- (`⌈ W ⌉ ⊆` the recursively, structurally-smaller-in-`Pr`-computed
    -- set for `Pr` under `W ∷ Δ`), of `⌈ W ⌉` — built as a union of closed
    -- singletons so its closedness needs no fact relating the (a priori
    -- unrelated) recursive results at different, bisimilar anchors.
    algSet Γ Δ P (rec Pr) with messageGuarded? Pr
    ... | no ¬mg = inj₂ (λ { (𝒮 , a/rec mg _ _) → ¬mg mg })
    ... | yes mg =
      inj₁ (toBits waitDec , a/rec mg td sub , toBits-closed waitDec waitClosed)
      where
        passes? : (W : State G) → Dec (∀ w → W ~ w → T (lookup (resultBits (algSet Γ (W ∷ Δ) P Pr)) w))
        passes? W = FinP.all? (λ w → (bisim?~ W w) →-dec T? (lookup (resultBits (algSet Γ (W ∷ Δ) P Pr)) w))

        passBits : Bits
        passBits = toBits passes?

        AnchorPred : Pred
        AnchorPred w = ∃[ W ] T (lookup passBits W) × (W ~ w)

        anchorDec : ∀ w → Dec (AnchorPred w)
        anchorDec w = FinP.any? (λ W → T? (lookup passBits W) ×-dec bisim?~ W w)

        anchorBits : Bits
        anchorBits = toBits anchorDec

        anchorBits-closed : Closed ⟦ anchorBits ⟧
        anchorBits-closed = toBits-closed anchorDec cl
          where
            cl : Closed AnchorPred
            cl w~w′ (W , pW , W~w) = W , pW , ~trans W~w w~w′

        td : ∀ {W′} → T (lookup anchorBits W′) → Γ & (W′ ∷ Δ) ⊢a P ◂ Pr ∶ ⌈ W′ ⌉
        td {W′} p with toBits-sound anchorDec p
        ... | (W , pW , W~W′) with algSet Γ (W ∷ Δ) P Pr | toBits-sound passes? pW
        ...   | inj₁ (bits , deriv , _) | passesW =
          alg/mono narrow (alg/bisim (~ᵛ/∷ W~W′ ~ᵛ-refl) (alg/mono (λ {w} → passesW w) deriv))
          where
            narrow : ∀ {w} → W′ ~ w → W ~ w
            narrow {w} W′~w = ~trans W~W′ W′~w
        ...   | inj₂ _ | passesW = ⊥-elim (⊥bits-empty (passesW W ~refl))

        waitDec : ∀ s → Dec (Wait P ⟦ reachNotP P anchorBits ⟧ s)
        waitDec s = Wait? P (reachNotP P anchorBits) s

        sub : ∀ {s} → T (lookup (toBits waitDec) s) → Wait P (Reach₀ P ⟦ anchorBits ⟧) s
        sub {s} m = waitV/leaf-mono bridge (toBits-sound waitDec m)
          where
            bridge : ∀ {u} → ⟦ reachNotP P anchorBits ⟧ u → Reach₀ P ⟦ anchorBits ⟧ u
            bridge {u} x = reachNotP-sound P anchorBits (suc (size G)) u x

        reach-closed : Closed ⟦ reachNotP P anchorBits ⟧
        reach-closed = decided-closed (reachNotP P anchorBits) snd′ cmp′ (reach₀/~ anchorBits-closed)
          where
            snd′ : ∀ {s} → T (lookup (reachNotP P anchorBits) s) → Reach₀ P ⟦ anchorBits ⟧ s
            snd′ {s} x =
              let a , 𝒜a , tr = reachNotP-sound P anchorBits (suc (size G)) s x
              in a , 𝒜a , tr

            cmp′ : ∀ {s} → Reach₀ P ⟦ anchorBits ⟧ s → T (lookup (reachNotP P anchorBits) s)
            cmp′ (a , 𝒜a , tr) = reachNotP-complete P anchorBits 𝒜a tr

        waitClosed : Closed (Wait P ⟦ reachNotP P anchorBits ⟧)
        waitClosed = wait/~ reach-closed

    algBr Γ Δ Q (B ∷ Bs) zero    U = algSet (U ∷ Γ) Δ Q B
    algBr Γ Δ Q (B ∷ Bs) (suc j) U = algBr Γ Δ Q Bs j U
