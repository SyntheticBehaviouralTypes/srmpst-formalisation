{-# OPTIONS --guardedness #-}

-- Deciding `Wait` on a finite graph — the graph-walking half of the set-based
-- checker (TODO.md §7 step 6).
--
-- `WaitV P 𝒮 V s` is a finite tree over a visited SET, so the decision splits
-- on `∈T?` exactly as TODO.md §3.1 predicted, and the two halves are ORDERED,
-- not nested:
--
--   * **`¬ P ∈T s`** — `wv/cycle` demands `P ∈T s`, and `¬ P ∈T` is forward
--     closed (`∈T` is backward closed, `in/later`), so no cycle can fire at `s`
--     or anywhere below it.  The derivation is then built from `wv/leaf` and
--     `wv/step` alone and does not mention `V` at all.  That is a plain least
--     fixpoint, computed ONCE as the table `noCycle` and consulted by lookup.
--
--   * **`P ∈T s`** — cycles are available, so a revisit SUCCEEDS.  That is what
--     makes the search here trivial to terminate and, unlike `Check/Alg.agda`'s
--     old forward search, it needs no `Justified`/`FailedFrom` apparatus and no
--     four-component measure: a revisit is an answer, never a failure.  The
--     visited set grows strictly on every recursive call, so `wt`/`Incl` from
--     `Reachability.agda` is the whole termination argument.
--
-- The visited set is read UP TO `~` (`Vof`), which is what makes
-- `Vof (mark V s)` and `Vof V ∪ ⌈ s ⌉` the same predicate in both directions —
-- with a raw index only the `yes` direction would transfer, and the `no`
-- direction is the one that needs it.

open import Data.Bool using (Bool; true; false; _∨_; T)
import Data.Bool.Properties as BoolP
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Induction using (<-wellFounded)
import Data.Nat.Properties as Nat

open import Data.Fin using (Fin)
import Data.Fin.Properties as FinP

open import Data.Vec using (Vec; lookup; tabulate; replicate)
import Data.Vec.Properties as VecP

open import Data.List using (List; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

open import Induction.WellFounded using (Acc; acc)

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; T?; map′; _×-dec_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)

open import Definitions.Behav using (BTheory; WellBehaved)
import Definitions.Typing as Typing
import Check.Core as Core

module Check.Wait (N : ℕ) where

  open import Definitions.Common N using (Part)

  open import Definitions.Graph.Core N
    using (Graph; State; size; edges; Edge; graphTheory; listed⇒step; step⇒listed)
    renaming (_-<_>->_ to GStep)

  open import Definitions.Graph.Reachability N
    using ( iter; iter-suc; wt; Incl; wt/mono; wt/strict; wt-bound
          ; T→≡true; ≡true→T; ∈T? )

  open Core.Processes N using (module GraphChecker)

  module WaitCheck
    (G : Graph)
    (wb : WellBehaved (graphTheory G))
    (P : Part)
    (𝒮 : State G → Set)
    (𝒮? : ∀ s → Dec (𝒮 s))
    where

    open Typing.MPST wb
    open GraphChecker G wb using (na?; bisim?~)
    open import Definitions.Typing.Alg wb
      using (WaitV; wv/leaf; wv/cycle; wv/step; waitV/mono; Behavs)

    Bits : Set
    Bits = Vec Bool (size G)

    -- ══════════════════════════════════════════════════════════════════
    --  Successors
    -- ══════════════════════════════════════════════════════════════════

    StepOut : State G → Set
    StepOut s = ∃[ α ] ∃[ t ] (s -< α >-> t)

    stepOut/aux :
      ∀ s (xs : List (Edge (size G)))
      → edges G s ≡ xs
      → Dec (StepOut s)

    stepOut/aux s [] eq = no ¬out
      where
        ¬out : ¬ StepOut s
        ¬out (α , t , gr)
          with subst ((α , t) ∈_) eq (step⇒listed {G = G} gr)
        ... | ()

    stepOut/aux s ((α , t) ∷ xs) eq =
      yes (α , t , listed⇒step {G = G} (subst ((α , t) ∈_) (sym eq) (here refl)))

    stepOut? : ∀ s → Dec (StepOut s)
    stepOut? s = stepOut/aux s (edges G s) refl

    -- Every successor of `s` is marked in `X`.
    AllSucc : Bits → State G → Set
    AllSucc X s = ∀ {β u} → s -< β >-> u → T (lookup X u)

    allSucc? : ∀ X s → Dec (AllSucc X s)
    allSucc? X s
      with All.all? (λ e → T? (lookup X (proj₂ e))) (edges G s)
    ... | yes every =
      yes λ gr → All.lookup every (step⇒listed {G = G} gr)
    ... | no ¬every =
      no λ every → ¬every (All.tabulate λ mem → every (listed⇒step {G = G} mem))

    -- ══════════════════════════════════════════════════════════════════
    --  The `¬ P ∈T` region: a least fixpoint, computed once
    -- ══════════════════════════════════════════════════════════════════

    Grows : Bits → State G → Set
    Grows X s = (P not-active-in s) × StepOut s × AllSucc X s

    grows? : ∀ X s → Dec (Grows X s)
    grows? X s with na? P s | stepOut? s | allSucc? X s
    ... | yes na | yes out | yes every = yes (na , out , every)
    ... | no ¬na | _       | _         = no λ { (na , _ , _) → ¬na na }
    ... | _      | no ¬out | _         = no λ { (_ , out , _) → ¬out out }
    ... | _      | _       | no ¬every = no λ { (_ , _ , e) → ¬every e }

    ⊥bits : Bits
    ⊥bits = replicate (size G) false

    step₁ : Bits → Bits
    step₁ X = tabulate (λ s → ⌊ 𝒮? s ⌋ ∨ ⌊ grows? X s ⌋)

    step₁-lookup :
      ∀ X s → lookup (step₁ X) s ≡ (⌊ 𝒮? s ⌋ ∨ ⌊ grows? X s ⌋)
    step₁-lookup X s = VecP.lookup∘tabulate _ s

    -- One round more than `size G`: the chain `⊥bits ⊆ step₁ ⊥bits ⊆ ⋯` can
    -- grow at most `size G` times, so round `suc (size G)` is necessarily
    -- stable — and stable AT `noCycle`, which is what `table-fixed` needs.
    noCycle : Bits
    noCycle = iter (suc (size G)) step₁ ⊥bits

    -- ── Soundness of the table: a marked state carries a derivation, at ANY
    --    visited set, because the tree it builds uses no cycle. ──

    table-sound :
      ∀ k {V : Behavs}{s}
      → T (lookup (iter k step₁ ⊥bits) s)
      → WaitV P 𝒮 V s

    table-sound zero {s = s} x =
      ⊥-elim (subst T (VecP.lookup-replicate s false) x)

    table-sound (suc k) {V}{s} x
      with 𝒮? s
         | grows? (iter k step₁ ⊥bits) s
         | subst T (step₁-lookup (iter k step₁ ⊥bits) s)
             (subst (λ z → T (lookup z s)) (iter-suc k step₁ ⊥bits) x)
    ... | yes leaf | _                          | _ = wv/leaf leaf
    ... | no _     | yes (na , (_ , _ , gr) , every) | _ =
      wv/step na gr (λ gr′ → table-sound k (every gr′))
    ... | no _     | no _                       | ()

    -- ── The table is a fixed point ──

    step₁/mono : ∀ {X Y} → Incl X Y → Incl (step₁ X) (step₁ Y)
    step₁/mono {X}{Y} incl i x
      with 𝒮? i | grows? X i | subst T (step₁-lookup X i) x
    ... | yes leaf | _ | _ =
      subst T (sym (step₁-lookup Y i)) (leafBit leaf)
      where
        leafBit : 𝒮 i → T (⌊ 𝒮? i ⌋ ∨ ⌊ grows? Y i ⌋)
        leafBit l with 𝒮? i
        ... | yes _ = _
        ... | no ¬l = ⊥-elim (¬l l)
    ... | no ¬leaf | yes (na , out , every) | _ =
      subst T (sym (step₁-lookup Y i)) (growBit (na , out , λ gr → incl _ (every gr)))
      where
        growBit : Grows Y i → T (⌊ 𝒮? i ⌋ ∨ ⌊ grows? Y i ⌋)
        growBit g with 𝒮? i | grows? Y i
        ... | yes _ | _      = _
        ... | no _  | yes _  = _
        ... | no _  | no ¬g  = ⊥-elim (¬g g)
    ... | no _ | no _ | ()

    ⊥bits-min : ∀ {X} → Incl ⊥bits X
    ⊥bits-min {X} i x = ⊥-elim (subst T (VecP.lookup-replicate i false) x)

    chain : ∀ k → Incl (iter k step₁ ⊥bits) (iter (suc k) step₁ ⊥bits)
    chain zero    = ⊥bits-min {step₁ ⊥bits}   -- pinned: `Incl` hides it under `lookup`
    chain (suc k) i =
      subst₂
        (λ u v → T (lookup u i) → T (lookup v i))
        (sym (iter-suc k step₁ ⊥bits))
        (sym (iter-suc (suc k) step₁ ⊥bits))
        (step₁/mono (chain k) i)

    grow :
      ∀ k
      → (k ≤ wt (iter k step₁ ⊥bits))
      ⊎ (step₁ (iter k step₁ ⊥bits) ≡ iter k step₁ ⊥bits)

    grow zero = inj₁ z≤n
    grow (suc k) = go (grow k)
      where
        X : Bits
        X = iter k step₁ ⊥bits

        fixStep : step₁ X ≡ X → step₁ (iter (suc k) step₁ ⊥bits) ≡ iter (suc k) step₁ ⊥bits
        fixStep fix =
          let e : iter (suc k) step₁ ⊥bits ≡ X
              e = trans (iter-suc k step₁ ⊥bits) fix
          in trans (cong step₁ e) (trans fix (sym e))

        growStep : k ≤ wt X → step₁ X ≢ X → suc k ≤ wt (iter (suc k) step₁ ⊥bits)
        growStep bound ¬fix =
          let strict : suc (wt X) ≤ wt (step₁ X)
              strict = wt/strict {left = X} {right = step₁ X}
                         (subst (Incl X) (iter-suc k step₁ ⊥bits) (chain k))
                         (λ e → ¬fix (sym e))
              weqn : wt (step₁ X) ≡ wt (iter (suc k) step₁ ⊥bits)
              weqn = cong wt (sym (iter-suc k step₁ ⊥bits))
          in subst (suc k ≤_) weqn (Nat.≤-trans (s≤s bound) strict)

        go :
          (k ≤ wt X) ⊎ (step₁ X ≡ X)
          → (suc k ≤ wt (iter (suc k) step₁ ⊥bits))
          ⊎ (step₁ (iter (suc k) step₁ ⊥bits) ≡ iter (suc k) step₁ ⊥bits)
        go (inj₂ fix) = inj₂ (fixStep fix)
        go (inj₁ bound) with VecP.≡-dec BoolP._≟_ (step₁ X) X
        ... | yes fix  = inj₂ (fixStep fix)
        ... | no ¬fix  = inj₁ (growStep bound ¬fix)

    table-fixed : step₁ noCycle ≡ noCycle
    table-fixed with grow (suc (size G))
    ... | inj₂ fix = fix
    ... | inj₁ bound =
      ⊥-elim (Nat.<-irrefl refl
               (Nat.≤-trans bound (wt-bound (iter (suc (size G)) step₁ ⊥bits))))

    -- ── Completeness of the table.  The derivation cannot use `wv/cycle`
    --    anywhere below `s`, because `¬ P ∈T` is forward closed (`in/later`),
    --    so the visited set plays no part and the table sees every node. ──

    markIt : ∀ {s} → (𝒮 s ⊎ Grows noCycle s) → T (lookup noCycle s)
    markIt {s} d =
      subst (λ z → T (lookup z s)) table-fixed
        (subst T (sym (step₁-lookup noCycle s)) (bit d))
      where
        bit : (𝒮 s ⊎ Grows noCycle s) → T (⌊ 𝒮? s ⌋ ∨ ⌊ grows? noCycle s ⌋)
        bit (inj₁ l) with 𝒮? s
        ... | yes _  = _
        ... | no ¬l  = ⊥-elim (¬l l)
        bit (inj₂ g) with 𝒮? s | grows? noCycle s
        ... | yes _ | _      = _
        ... | no _  | yes _  = _
        ... | no _  | no ¬g  = ⊥-elim (¬g g)

    table-complete :
      ∀ {V : Behavs}{s}
      → ¬ (P ∈T s)
      → WaitV P 𝒮 V s
      → T (lookup noCycle s)

    table-complete ¬inT (wv/leaf x) =
      markIt (inj₁ x)

    table-complete ¬inT (wv/cycle _ inT) =
      ⊥-elim (¬inT inT)

    table-complete ¬inT (wv/step na gr k) =
      markIt (inj₂
        (na , (_ , _ , gr)
            , λ gr′ → table-complete (λ inT → ¬inT (in/later gr′ inT)) (k gr′)))

    -- ══════════════════════════════════════════════════════════════════
    --  The `P ∈T` region: a visited-set walk in which a revisit SUCCEEDS
    -- ══════════════════════════════════════════════════════════════════

    -- The visited set, read up to `~`.  This is what makes `Vof (mark V s)`
    -- and `Vof V ∪ ⌈ s ⌉` interchangeable in BOTH directions.
    Vof : Bits → Behavs
    Vof V w = ∃[ a ] T (lookup V a) × (a ~ w)

    vof? : ∀ V w → Dec (Vof V w)
    vof? V w = FinP.any? (λ a → T? (lookup V a) ×-dec bisim?~ a w)

    vof/trans : ∀ {V a w} → Vof V a → a ~ w → Vof V w
    vof/trans (b , vb , b~a) a~w = b , vb , ~trans b~a a~w

    mark : Bits → State G → Bits
    mark V s = tabulate (λ t → lookup V t ∨ ⌊ t FinP.≟ s ⌋)

    mark-lookup : ∀ V s t → lookup (mark V s) t ≡ (lookup V t ∨ ⌊ t FinP.≟ s ⌋)
    mark-lookup V s t = VecP.lookup∘tabulate _ t

    mark-in : ∀ V s → T (lookup (mark V s) s)
    mark-in V s = subst T (sym (mark-lookup V s s)) go
      where
        go : T (lookup V s ∨ ⌊ s FinP.≟ s ⌋)
        go with lookup V s | s FinP.≟ s
        ... | true  | _      = _
        ... | false | yes _  = _
        ... | false | no ¬p  = ⊥-elim (¬p refl)

    mark-old : ∀ V s {t} → T (lookup V t) → T (lookup (mark V s) t)
    mark-old V s {t} x = subst T (sym (mark-lookup V s t)) (go x)
      where
        go : T (lookup V t) → T (lookup V t ∨ ⌊ t FinP.≟ s ⌋)
        go y with lookup V t
        ... | true = _

    mark-sound : ∀ V s {t} → T (lookup (mark V s) t) → T (lookup V t) ⊎ (t ≡ s)
    mark-sound V s {t} x = go (subst T (mark-lookup V s t) x)
      where
        go : T (lookup V t ∨ ⌊ t FinP.≟ s ⌋) → T (lookup V t) ⊎ (t ≡ s)
        go y with lookup V t | t FinP.≟ s
        ... | true  | _        = inj₁ _
        ... | false | yes t≡s  = inj₂ t≡s

    vof/mark→ : ∀ V s {w} → Vof (mark V s) w → Vof V w ⊎ (s ~ w)
    vof/mark→ V s (a , ma , a~w) with mark-sound V s ma
    ... | inj₁ va   = inj₁ (a , va , a~w)
    ... | inj₂ refl = inj₂ a~w

    vof/mark← : ∀ V s {w} → Vof V w ⊎ (s ~ w) → Vof (mark V s) w
    vof/mark← V s (inj₁ (a , va , a~w)) = a , mark-old V s va , a~w
    vof/mark← V s (inj₂ s~w)            = s , mark-in V s , s~w

    AllWait : Bits → State G → Set₁
    AllWait W s = ∀ {β u} → s -< β >-> u → WaitV P 𝒮 (Vof W) u

    allWait? :
      ∀ W s → (∀ u → Dec (WaitV P 𝒮 (Vof W) u)) → Dec (AllWait W s)
    allWait? W s dec with All.all? (λ e → dec (proj₂ e)) (edges G s)
    ... | yes every =
      yes λ gr → All.lookup every (step⇒listed {G = G} gr)
    ... | no ¬every =
      no λ every → ¬every (All.tabulate λ mem → every (listed⇒step {G = G} mem))

    -- The visited set grows strictly on every recursive call, which is the
    -- whole termination argument — no `size/proc`, no phase component, no
    -- `Justified`/`FailedFrom`.
    smaller :
      ∀ V s → ¬ Vof V s → size G ∸ wt (mark V s) < size G ∸ wt V
    smaller V s ¬anc =
      Nat.∸-monoʳ-<
        (wt/strict {left = V} {right = mark V s}
          (λ i x → mark-old V s x)
          (λ e → ¬anc (s , subst (λ z → T (lookup z s)) (sym e) (mark-in V s) , ~refl)))
        (wt-bound (mark V s))

    -- `tbl` is the `noCycle` table, taken as an ARGUMENT rather than read as
    -- the module-level definition.  Agda shares argument thunks but re-unfolds
    -- definition applications, so `lookup noCycle s` written directly here
    -- rebuilds the whole `iter (suc (size G)) step₁ ⊥bits` fixpoint at every
    -- node of the walk.  Measured on `Tests/Perf09_RevisitSpine`: 138s as a
    -- definition, 9s as an argument.  Its two correctness facts ride along for
    -- the same reason — they mention `tbl`, not `noCycle`.
    wait?/acc :
      (tbl : Bits)
      → (∀ {V : Behavs}{s} → T (lookup tbl s) → WaitV P 𝒮 V s)
      → (∀ {V : Behavs}{s} → ¬ P ∈T s → WaitV P 𝒮 V s → T (lookup tbl s))
      → ∀ V s → Acc _<_ (size G ∸ wt V) → Dec (WaitV P 𝒮 (Vof V) s)

    wait?/acc tbl tsound tcomplete V s (acc rs) with 𝒮? s
    ... | yes leaf = yes (wv/leaf leaf)
    ... | no ¬leaf with ∈T? G P s
    ...   | no ¬inT =
      map′ tsound (tcomplete ¬inT) (T? (lookup tbl s))
    ...   | yes inT with vof? V s
    ...     | yes anc = yes (wv/cycle (s , anc , ~refl) inT)
    ...     | no ¬anc with na? P s | stepOut? s
    ...       | no ¬na | _ =
      no λ { (wv/leaf x) → ¬leaf x
           ; (wv/cycle (a , va , a~s) _) → ¬anc (vof/trans {V} va a~s)
           ; (wv/step na _ _) → ¬na na }
    ...       | yes _ | no ¬out =
      no λ { (wv/leaf x) → ¬leaf x
           ; (wv/cycle (a , va , a~s) _) → ¬anc (vof/trans {V} va a~s)
           ; (wv/step _ gr _) → ¬out (_ , _ , gr) }
    ...       | yes na | yes (_ , _ , gr)
      with allWait? (mark V s) s
             (λ u → wait?/acc tbl tsound tcomplete (mark V s) u
                      (rs (smaller V s ¬anc)))
    ...         | yes every =
      yes (wv/step na gr (λ gr′ → waitV/mono (vof/mark→ V s) (every gr′)))
    ...         | no ¬every =
      no λ { (wv/leaf x) → ¬leaf x
           ; (wv/cycle (a , va , a~s) _) → ¬anc (vof/trans {V} va a~s)
           ; (wv/step _ _ k) →
               ¬every (λ gr′ → waitV/mono (vof/mark← V s) (k gr′)) }

    -- `Wait P 𝒮 = WaitV P 𝒮 ∅`, and `Vof ⊥bits` is empty.
    wait? : ∀ s → Dec (WaitV P 𝒮 (λ _ → ⊥) s)
    wait? s =
      map′ (waitV/mono empty→) (waitV/mono →empty)
        (wait?/acc noCycle (table-sound (suc (size G))) table-complete
           ⊥bits s (<-wellFounded (size G ∸ wt ⊥bits)))
      where
        empty→ : ∀ {w} → Vof ⊥bits w → ⊥
        empty→ (a , x , _) = subst T (VecP.lookup-replicate a false) x

        →empty : ∀ {w} → ⊥ → Vof ⊥bits w
        →empty ()
