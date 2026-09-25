{-# OPTIONS --guardedness #-}

-- Deciding `⊢a` over a concrete graph.
--
-- `Probing.probe` walks the process by plain structural recursion.  Its set
-- argument is where typing is PROBED: the answer is the largest subset where
-- the process is typed, or `none` when that subset is empty.  Each rule's
-- premises are decided over finitely many states; the continuation of a
-- send/receive is probed at the states the rule would hand it.
--
-- `alg?` is the old question — typed at exactly this set? — answered from
-- one probe.
--
-- COST.  Every set is TABULATED once into a `Vec Bool` table (`memo`) and
-- passed on as an ARGUMENT, so Agda shares it: a definition is re-unfolded
-- at every use, an argument is evaluated once (CLAUDE.md, thunk sharing).
-- The graph-level facts (idle and `¬P` reachability, bisimilarity, `∈T`,
-- activity) are tabulated once per probe in `Env`.
--
-- Built on `Definitions/*`, plus `Check/Core.agda`'s `checkExpression`.

open import Level using () renaming (suc to lsuc; zero to lzero)

open import Data.Nat using (ℕ; zero; suc; _∸_; _<_; _≤_)
open import Data.Nat.Induction using (<-wellFounded)
import Data.Nat.Properties as Nat

open import Data.Fin using (Fin; zero; suc) renaming (_≟_ to _≟Fin_)
import Data.Fin.Properties as FinP

open import Data.Vec using (Vec; []; _∷_; lookup; replicate; _[_]≔_)
import Data.Vec as V
import Data.Vec.Properties as VecP

open import Data.List using (List; []; _∷_; filter)
open import Data.List.Membership.Propositional
  renaming (_∈_ to _∈L_)
open import Data.List.Membership.Propositional.Properties
  using (∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties using (any⁺; any⁻)
import Data.List
open import Data.Bool using (_∧_)
open import Data.Bool.Properties using (T-∧)
open import Function.Bundles using (Equivalence)
open import Data.Nat using (_≡ᵇ_)
open import Data.Fin using (toℕ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

open import Data.Product using (Σ-syntax; ∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Bool using (Bool; true; false; T)

open import Function using (_∘_)

open import Induction.WellFounded using (Acc; acc)

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable
  using (⌊_⌋; T?; map′; _×-dec_; _→-dec_; ¬?; toWitness; fromWitness)
open import Relation.Unary using (Decidable; _∈_; _⊆_; _∩_; Satisfiable)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_; _◅◅_)

open import Definitions.Behav using (WellBehaved)
open import Definitions.Expr using (Sort; s/bool; s/nat; s/unit; _⊢e_∶_; ⊢e-unique)
open import Check.Core using (checkExpression)

import Definitions.Typing as Typing

module Check.Alg (N : ℕ) where

  open import Definitions.Graph.Core N
    using (Graph; graph; size; outgoing; edges; Edge
          ; listed⇒step; step⇒listed; graphTheory)
    renaming (step? to edge?)
  open import Definitions.Graph.Bisimulation N
    using (Matrix; approximation; bisimulationCorrect; sound; complete)
  open import Definitions.Graph.Action N
    using (eqFin; eqFin-sound; eqFin-refl
          ; eqAction; eqAction-sound; eqAction-refl)
    renaming (_≟Actionᵇ_ to _≟A_)
  open import Definitions.Graph.Reachability N
    using (Step; PathVia; path/nil; path/cons; reachVia; reachVia-sound
          ; reachVia-complete; T→≡true; ≡true→T; reach→∈T; ∈T→reach; active?
          ; anyActive→∈; ∈α-lift; wt; wt/strict; wt-bound)

  module AlgCheck
    (G : Graph)
    (wb : WellBehaved (graphTheory G))
    where

    open Typing.MPST wb
    open import Definitions.Typing.Alg wb
    open import Definitions.Typing.AlgNorm wb using (waitFind)

    private
      variable
        γ δ : ℕ

      n : ℕ
      n = size G

    -- ══════════════════════════════════════════════════════════════════
    --  Finite quantification
    -- ══════════════════════════════════════════════════════════════════

    any-anchors? :
      ∀ δ {A : Vec Behav δ → Set} → (∀ ws → Dec (A ws)) → Dec (∃ A)
    any-anchors? zero A? with A? []
    ... | yes a = yes ([] , a)
    ... | no ¬a = no λ { ([] , a) → ¬a a }
    any-anchors? (suc δ) A?
      with FinP.any? (λ w → any-anchors? δ (λ ws → A? (w ∷ ws)))
    ... | yes (w , ws , a) = yes (w ∷ ws , a)
    ... | no ¬a = no λ { (w ∷ ws , a) → ¬a (w , ws , a) }

    all-anchors? :
      ∀ δ {A : Vec Behav δ → Set} → (∀ ws → Dec (A ws)) → Dec (∀ ws → A ws)
    all-anchors? zero A? with A? []
    ... | yes a = yes λ { [] → a }
    ... | no ¬a = no λ all → ¬a (all [])
    all-anchors? (suc δ) A?
      with FinP.all? (λ w → all-anchors? δ (λ ws → A? (w ∷ ws)))
    ... | yes all = yes λ { (w ∷ ws) → all w ws }
    ... | no ¬all = no λ all → ¬all (λ w ws → all (w ∷ ws))

    any-state? : {A : States δ} → Decidable A → Dec (Satisfiable A)
    any-state? {δ} A? =
      map′ (λ { (ws , s , a) → (ws , s) , a })
           (λ { ((ws , s) , a) → ws , s , a })
           (any-anchors? δ (λ ws → FinP.any? (λ s → A? (ws , s))))

    all-state? : {A : States δ} → Decidable A → Dec (∀ x → x ∈ A)
    all-state? {δ} A? =
      map′ (λ all → λ { (ws , s) → all ws s }) (λ all ws s → all (ws , s))
           (all-anchors? δ (λ ws → FinP.all? (λ s → A? (ws , s))))

    ⊆? : {A B : States δ} → Decidable A → Decidable B → Dec (A ⊆ B)
    ⊆? A? B? =
      map′ (λ all {x} → all x) (λ sub x → sub)
           (all-state? (λ x → A? x →-dec B? x))

    any-sort? : {A : Sort → Set} → (∀ U → Dec (A U)) → Dec (∃ A)
    any-sort? A? with A? s/bool | A? s/nat | A? s/unit
    ... | yes a | _     | _     = yes (_ , a)
    ... | no _  | yes a | _     = yes (_ , a)
    ... | no _  | no _  | yes a = yes (_ , a)
    ... | no b  | no m  | no u  =
      no λ { (s/bool , a) → b a ; (s/nat , a) → m a ; (s/unit , a) → u a }

    all-sort? : {A : Sort → Set} → (∀ U → Dec (A U)) → Dec (∀ U → A U)
    all-sort? A? with A? s/bool | A? s/nat | A? s/unit
    ... | yes b | yes m | yes u =
      yes λ { s/bool → b ; s/nat → m ; s/unit → u }
    ... | no ¬b | _     | _     = no λ all → ¬b (all s/bool)
    ... | _     | no ¬m | _     = no λ all → ¬m (all s/nat)
    ... | _     | _     | no ¬u = no λ all → ¬u (all s/unit)

    -- ══════════════════════════════════════════════════════════════════
    --  Tables
    -- ══════════════════════════════════════════════════════════════════
    --
    -- A decision read off a precomputed bit.  Only the bit is inspected to
    -- choose `yes`/`no`; the original decision is consulted only when the
    -- proof itself is demanded.

    fromBit : ∀ {B : Set}(d : Dec B){b} → b ≡ ⌊ d ⌋ → Dec B
    fromBit d {true}  eq = yes (toWitness (subst T eq tt))
    fromBit d {false} eq = no λ x → subst T (sym eq) (fromWitness x)

    -- Behaviours.
    memoB : {A : Behav → Set} → (∀ s → Dec (A s)) → ∀ s → Dec (A s)
    memoB A? = with-table (V.tabulate (λ s → ⌊ A? s ⌋)) (λ s → VecP.lookup∘tabulate _ s)
      where
        with-table : (tbl : Vec Bool n) → (∀ s → lookup tbl s ≡ ⌊ A? s ⌋) → ∀ s → Dec _
        with-table tbl spec s = fromBit (A? s) (spec s)

    -- States: one table per anchor, nested.
    Tab : ℕ → Set
    Tab zero    = Vec Bool n
    Tab (suc δ) = Vec (Tab δ) n

    lookupT : Tab δ → State δ → Bool
    lookupT {zero}  t ([] , s)     = lookup t s
    lookupT {suc δ} t (w ∷ ws , s) = lookupT (lookup t w) (ws , s)

    tabulateT : (State δ → Bool) → Tab δ
    tabulateT {zero}  f = V.tabulate (λ s → f ([] , s))
    tabulateT {suc δ} f = V.tabulate (λ w → tabulateT (λ { (ws , s) → f (w ∷ ws , s) }))

    lookup∘tabulateT : ∀ (f : State δ → Bool) x → lookupT (tabulateT f) x ≡ f x
    lookup∘tabulateT {zero}  f ([] , s)     = VecP.lookup∘tabulate _ s
    lookup∘tabulateT {suc δ} f (w ∷ ws , s) =
      trans (cong (λ t → lookupT t (ws , s)) (VecP.lookup∘tabulate _ w))
            (lookup∘tabulateT (λ { (ws′ , s′) → f (w ∷ ws′ , s′) }) (ws , s))

    memo : {A : States δ} → Decidable A → Decidable A
    memo A? = with-table (tabulateT (λ x → ⌊ A? x ⌋)) (lookup∘tabulateT _)
      where
        with-table : (tbl : Tab _) → (∀ x → lookupT tbl x ≡ ⌊ A? x ⌋) → Decidable _
        with-table tbl spec x = fromBit (A? x) (spec x)

    -- Dependent tables, for the branches of a receive.
    record ⊤₁ : Set₁ where
      constructor tt₁

    AllFin′ : (m : ℕ) → (Fin m → Set₁) → Set₁
    AllFin′ zero    B = ⊤₁
    AllFin′ (suc m) B = B zero × AllFin′ m (B ∘ suc)

    record AllFin (m : ℕ)(B : Fin m → Set₁) : Set₁ where
      constructor wrap
      field unwrap : AllFin′ m B

    lookupAll : ∀ {m B} → AllFin m B → (i : Fin m) → B i
    lookupAll {suc m} (wrap (b , _))  zero    = b
    lookupAll {suc m} (wrap (_ , bs)) (suc i) = lookupAll (wrap bs) i

    tabulateAll : ∀ {m B} → ((i : Fin m) → B i) → AllFin m B
    tabulateAll {zero}  f = wrap tt₁
    tabulateAll {suc m} f = wrap (f zero , AllFin.unwrap (tabulateAll (f ∘ suc)))

    record Sorted (B : Sort → Set₁) : Set₁ where
      constructor sorted
      field at-bool : B s/bool
            at-nat  : B s/nat
            at-unit : B s/unit

    lookupSort : ∀ {B} → Sorted B → ∀ U → B U
    lookupSort t s/bool = Sorted.at-bool t
    lookupSort t s/nat  = Sorted.at-nat t
    lookupSort t s/unit = Sorted.at-unit t

    tabulateSort : ∀ {B} → (∀ U → B U) → Sorted B
    tabulateSort f = sorted (f s/bool) (f s/nat) (f s/unit)

    -- ══════════════════════════════════════════════════════════════════
    --  Steps, participation
    -- ══════════════════════════════════════════════════════════════════

    -- Action equality is decided by a BIT (`eqAction`, `Graph/Action.agda`).

    -- Is `(α , t)` an edge out of `s`?  A scan of `s`'s edges by bits.
    step? : ∀ s α t → Dec (s -< α >-> t)
    step? s α t =
      map′ (λ x → listed⇒step {G = G}
                    (Any.map (λ { {α′ , t′} px →
                                  let a , b = Equivalence.to T-∧ px
                                  in sym (cong₂ _,_ (eqAction-sound α′ α a) (eqFin-sound b)) })
                             (any⁻ hit (edges G s) x)))
           (λ gr → any⁺ hit
                     (Any.map (λ { refl → Equivalence.from T-∧ (eqAction-refl α , eqFin-refl t) })
                              (step⇒listed {G = G} gr)))
           (T? (Data.List.any hit (edges G s)))
      where
        hit : Edge n → Bool
        hit (α′ , t′) = eqAction α′ α ∧ eqFin t′ t

    Steps : Behav → Set
    Steps s = ∃[ β ] ∃[ u ] s -< β >-> u

    steps? : ∀ s → Dec (Steps s)
    steps? s = from (edges G s) (listed⇒step {G = G}) (step⇒listed {G = G})
      where
        from : (es : List (Edge n))
             → (∀ {α u} → (α , u) ∈L es → s -< α >-> u)
             → (∀ {α u} → s -< α >-> u → (α , u) ∈L es)
             → Dec (Steps s)
        from []            _   back = no λ { (_ , _ , gr) → case (back gr) }
          where case : ∀ {e} → e ∈L [] → ⊥
                case ()
        from ((β , u) ∷ _) fwd _    = yes (β , u , fwd (here refl))

    -- A property of every edge in a list.  The decider may use the
    -- membership proof, which `WaitDec`'s recursive call needs.
    all-edges? :
      ∀ {ℓ}{B : Edge n → Set ℓ}(es : List (Edge n))
      → (∀ {e} → e ∈L es → Dec (B e))
      → Dec (∀ {e} → e ∈L es → B e)
    all-edges? [] _ = yes λ ()
    all-edges? (e ∷ es) B? with B? (here refl) | all-edges? es (B? ∘ there)
    ... | yes b | yes bs = yes λ { (here refl) → b ; (there m) → bs m }
    ... | no ¬b | _      = no λ all → ¬b (all (here refl))
    ... | _     | no ¬bs = no λ all → ¬bs (all ∘ there)

    -- A property of every step out of `u`, decided over `u`'s edge list only.
    all-out? :
      ∀ u {B : Action → Behav → Set} → (∀ α t → Dec (B α t))
      → Dec (∀ α t → u -< α >-> t → B α t)
    all-out? u B? =
      map′ (λ all α t gr → all (step⇒listed {G = G} gr))
           (λ all {e} mem → all (proj₁ e) (proj₂ e) (listed⇒step {G = G} mem))
           (all-edges? (edges G u) λ {e} _ → B? (proj₁ e) (proj₂ e))

    Active : Part → Behav → Set
    Active P s = ∃[ α ] ∃[ t ] s -< α >-> t × P ∈α α

    ∉α⇐ : ∀ {P α} → ¬ P ∈α α → P ∉α α
    ∉α⇐ ¬p = (λ eq → ¬p (∈S eq)) , (λ eq → ¬p (∈R eq))

    active⇒? : ∀ P s → Dec (Active P s)
    active⇒? P s with active? G P s
    ... | yes any =
      let (α , u) , mem , px = anyActive→∈ G (edges G s) any
      in yes (α , u , listed⇒step {G = G} mem , px)
    ... | no ¬any =
      no λ { (_ , _ , gr , px) → ¬any (∈α-lift G (step⇒listed {G = G} gr) px) }

    idle : ∀ {P s} → ¬ Active P s → P not-active-in s
    idle {P} ¬act {α} gr = ∉α⇐ {P} {α} (λ px → ¬act (_ , _ , gr , px))

    -- ══════════════════════════════════════════════════════════════════
    --  Reachability, as rows of reachable states
    -- ══════════════════════════════════════════════════════════════════

    -- Idle walks: `PathVia` filtered by "`P` is not active here".
    ok : Part → Behav → Bool
    ok P s = ⌊ ¬? (active? G P s) ⌋

    -- Over any filter that agrees with `ok P` (in practice: its table).
    path⇒walk :
      ∀ {P}{ok′ : Behav → Bool} → (∀ s → ok′ s ≡ ok P s)
      → ∀ {s t k} → PathVia G ok′ s t k → Star (_⇝[ P ]_) s t
    path⇒walk ok≡ path/nil = ε
    path⇒walk {P} ok≡ (path/cons oks gr rest) =
      (idle (λ { (_ , _ , gr′ , px) →
                 toWitness (subst T (ok≡ _) oks)
                   (∈α-lift G (step⇒listed {G = G} gr′) px) })
      , _ , gr) ◅ path⇒walk ok≡ rest

    walk⇒path :
      ∀ {P}{ok′ : Behav → Bool} → (∀ s → ok′ s ≡ ok P s)
      → ∀ {s t} → Star (_⇝[ P ]_) s t → ∃[ k ] PathVia G ok′ s t k
    walk⇒path ok≡ ε = _ , path/nil
    walk⇒path {P} ok≡ ((na , _ , gr) ◅ rest) =
      let k , p = walk⇒path ok≡ rest
      in suc k ,
         path/cons
           (subst T (sym (ok≡ _)) (fromWitness λ any →
              let (α , u) , mem , px = anyActive→∈ G _ any
              in ∉c→¬∈c (na (listed⇒step {G = G} mem)) px))
           gr p

    -- `¬P`-labelled runs: plain reachability in the graph without `P`'s edges.
    G¬ : Part → Graph
    G¬ P = graph n (V.map (filter (λ e → P ∉α? proj₁ e)) (outgoing G))

    edge¬⇒ :
      ∀ {P s α t} → Step (G¬ P) s α t → s -< α >-> t × P ∉α α
    edge¬⇒ {P} {s} gr
      with ∈-filter⁻ (λ e → P ∉α? proj₁ e)
             (subst (_ ∈L_) (VecP.lookup-map s _ (outgoing G))
                (step⇒listed {G = G¬ P} gr))
    ... | mem , P∉α = listed⇒step {G = G} mem , P∉α

    ⇒edge¬ :
      ∀ {P s α t} → s -< α >-> t → P ∉α α → Step (G¬ P) s α t
    ⇒edge¬ {P} {s} gr P∉α =
      listed⇒step {G = G¬ P}
        (subst (_ ∈L_) (sym (VecP.lookup-map s _ (outgoing G)))
          (∈-filter⁺ (λ e → P ∉α? proj₁ e) (step⇒listed {G = G} gr) P∉α))

    path⇒run : ∀ {P s t k} → PathVia (G¬ P) (λ _ → true) s t k → s -[¬ P ]->* t
    path⇒run path/nil = skip/refl
    path⇒run (path/cons _ gr rest) =
      let gr′ , P∉α = edge¬⇒ gr in tr¬/step gr′ P∉α (path⇒run rest)

    run⇒path :
      ∀ {P s t αs} → s -[ αs ]-> t → All (P ∉α_) αs
      → ∃[ k ] PathVia (G¬ P) (λ _ → true) s t k
    run⇒path tr/refl _ = _ , path/nil
    run⇒path (tr/step gr tr) (P∉α ∷ all) =
      let k , p = run⇒path tr all in suc k , path/cons tt (⇒edge¬ gr P∉α) p

    -- Reading a reachability row.
    row? :
      ∀ (H : Graph)(ok′ : Fin (size H) → Bool)(rows : Vec (Vec Bool (size H)) (size H))
      → (∀ s → lookup rows s ≡ reachVia H ok′ s)
      → ∀ s t → Dec (∃[ k ] PathVia H ok′ s t k)
    row? H ok′ rows spec s t =
      map′ (λ x → reachVia-sound H ok′ s
                    (T→≡true (subst (λ r → T (lookup r t)) (spec s) x)))
           (λ { (_ , p) → subst (λ r → T (lookup r t)) (sym (spec s))
                            (≡true→T (reachVia-complete H ok′ s p)) })
           (T? (lookup (lookup rows s) t))

    -- ══════════════════════════════════════════════════════════════════
    --  The graph-level facts, tabulated once
    -- ══════════════════════════════════════════════════════════════════

    record Env (P : Part) : Set where
      field
        walk?   : ∀ s t → Dec (Star (_⇝[ P ]_) s t)
        unskip? : ∀ s t → Dec (s -[¬ P ]->* t)
        act?    : ∀ s → Dec (Active P s)
        inT?    : ∀ s → Dec (P ∈T s)
        moves?  : ∀ s → Dec (Steps s)
        bisim?  : ∀ s t → Dec (s ~ t)

    -- Every table is an ARGUMENT here, so it is computed once.
    mkEnv :
      ∀ P
      → (oks : Vec Bool n) → (∀ s → lookup oks s ≡ ok P s)
      → (idles : Vec (Vec Bool n) n)
      → (∀ s → lookup idles s ≡ reachVia G (lookup oks) s)
      → (runs : Vec (Vec Bool n) n)
      → (∀ s → lookup runs s ≡ reachVia (G¬ P) (λ _ → true) s)
      → (m : Matrix G) → m ≡ approximation G
      → (alls : Vec (Vec Bool n) n) → (∀ s → lookup alls s ≡ reachVia G (λ _ → true) s)
      → Env P
    mkEnv P oks oks≡ idles idles≡ runs runs≡ m m≡ alls alls≡ = record
      { walk?   = λ s t → map′ (path⇒walk oks≡ ∘ proj₂) (walk⇒path oks≡)
                                (row? G (lookup oks) idles idles≡ s t)
      ; unskip? = λ s t → map′ (path⇒run ∘ proj₂)
                                (λ { (_ , tr , all) → run⇒path tr all })
                                (row? (G¬ P) (λ _ → true) runs runs≡ s t)
      ; act?    = memoB (active⇒? P)
      -- `P ∈T s` iff `s` reaches a state where `P` acts: read off the rows.
      ; inT?    = memoB λ s →
          map′ (λ { (t , (_ , path) , act) → reach→∈T G path act })
               (λ inT → let t , _ , path , act = ∈T→reach G inT in t , (_ , path) , act)
               (FinP.any? λ t → row? G (λ _ → true) alls alls≡ s t ×-dec active? G P t)
      ; moves?  = memoB steps?
      ; bisim?  = λ s t →
          map′ (λ x → sound (bisimulationCorrect G)
                        (subst (λ r → T (lookup (lookup r s) t)) m≡ x))
               (λ r → subst (λ r′ → T (lookup (lookup r′ s) t)) (sym m≡)
                        (complete (bisimulationCorrect G) r))
               (T? (lookup (lookup m s) t))
      }

    -- The per-GRAPH tables: the bisimilarity matrix and plain reachability.
    record Shared : Set where
      constructor shared
      field
        matrix  : Matrix G
        matrix≡ : matrix ≡ approximation G
        reach   : Vec (Vec Bool n) n
        reach≡  : ∀ s → lookup reach s ≡ reachVia G (λ _ → true) s

    -- Built once, as arguments.
    shared-tables : Shared
    shared-tables =
      shared (approximation G) refl
             (V.tabulate (reachVia G (λ _ → true))) (λ s → VecP.lookup∘tabulate _ s)

    -- Every participant's `Env` is built from the SAME shared tables.
    env-with : Shared → ∀ P → Env P
    -- The idle filter is tabulated first, and the idle rows read the table.
    env-with (shared m m≡ alls alls≡) P =
      with-oks (V.tabulate (ok P)) (λ s → VecP.lookup∘tabulate _ s)
      where
        with-oks : (oks : Vec Bool n) → (∀ s → lookup oks s ≡ ok P s) → Env P
        with-oks oks oks≡ =
          mkEnv P oks oks≡
            (V.tabulate (reachVia G (lookup oks)))       (λ s → VecP.lookup∘tabulate _ s)
            (V.tabulate (reachVia (G¬ P) (λ _ → true))) (λ s → VecP.lookup∘tabulate _ s)
            m m≡ alls alls≡

    env : ∀ P → Env P
    env = env-with shared-tables

    -- ══════════════════════════════════════════════════════════════════
    --  Expressions and guardedness
    -- ══════════════════════════════════════════════════════════════════

    -- Expressions: `checkExpression` (`Check/Core.agda`).
    exp? : (Γ : Vec Sort γ) → ∀ E S → Dec (Γ ⊢e E ∶ S)
    exp? = checkExpression

    guarded? : (Pr : Proc γ δ) → Dec (MessageGuarded Pr)
    guarded? (_ ! _ < _ >∙ _) = yes mg/send
    guarded? (Σ _ ？· _)      = yes mg/recv
    guarded? (ifp _ then A else B) =
      map′ (λ (a , b) → mg/if a b) (λ { (mg/if a b) → a , b })
           (guarded? A ×-dec guarded? B)
    guarded? ∅       = no λ ()
    guarded? (v _)   = no λ ()
    guarded? (rec _) = no λ ()

    -- ══════════════════════════════════════════════════════════════════
    --  Probes
    -- ══════════════════════════════════════════════════════════════════

    -- `𝒮` is where typing is PROBED, not where it must hold.  The answer is
    -- the largest subset `𝒯 ⊆ 𝒮` where `Pr` is typed; `none` when it is
    -- empty.
    record Typed (Γ : Vec Sort γ)(P : Part)(Pr : Proc γ δ)(𝒮 : States δ) : Set₁ where
      field
        𝒯     : States δ
        𝒯?    : Decidable 𝒯
        sub   : 𝒯 ⊆ 𝒮
        typed : Γ ⊢a P ◂ Pr ∶ 𝒯
        max   : ∀ {𝒰} → Γ ⊢a P ◂ Pr ∶ 𝒰 → 𝒰 ∩ 𝒮 ⊆ 𝒯
        some  : Satisfiable 𝒯

    data Probe (Γ : Vec Sort γ)(P : Part)(Pr : Proc γ δ)(𝒮 : States δ) : Set₁ where
      found : Typed Γ P Pr 𝒮 → Probe Γ P Pr 𝒮
      none  : (∀ {𝒰} → Γ ⊢a P ◂ Pr ∶ 𝒰 → ¬ Satisfiable (𝒰 ∩ 𝒮)) → Probe Γ P Pr 𝒮

    -- What a probe found, as a set (empty for `none`).
    hit : ∀ {Γ : Vec Sort γ}{P}{Pr : Proc γ δ}{𝒮} → Probe Γ P Pr 𝒮 → States δ
    hit (found T) = Typed.𝒯 T
    hit (none _)  = λ _ → ⊥

    hit? : ∀ {Γ : Vec Sort γ}{P}{Pr : Proc γ δ}{𝒮}(r : Probe Γ P Pr 𝒮) → Decidable (hit r)
    hit? (found T) = Typed.𝒯? T
    hit? (none _)  = λ _ → no λ ()

    from-hit :
      ∀ {Γ : Vec Sort γ}{P}{Pr : Proc γ δ}{𝒮 X}(r : Probe Γ P Pr 𝒮)
      → X ⊆ hit r → Satisfiable X → Γ ⊢a P ◂ Pr ∶ X
    from-hit (found T) sub _       = alg/mono sub (Typed.typed T)
    from-hit (none _)  sub (_ , x) = ⊥-elim (sub x)

    into-hit :
      ∀ {Γ : Vec Sort γ}{P}{Pr : Proc γ δ}{𝒮}(r : Probe Γ P Pr 𝒮)
      → ∀ {𝒰} → Γ ⊢a P ◂ Pr ∶ 𝒰 → 𝒰 ∩ 𝒮 ⊆ hit r
    into-hit (found T) d     = Typed.max T d
    into-hit (none n)  d x∈  = n d (_ , x∈)

    -- The answer is stored as a TABLE.
    finish :
      ∀ {Γ : Vec Sort γ}{P}{Pr : Proc γ δ}{𝒮}
      → (𝒯 : States δ) → Decidable 𝒯 → 𝒯 ⊆ 𝒮
      → (Satisfiable 𝒯 → Γ ⊢a P ◂ Pr ∶ 𝒯)
      → (∀ {𝒰} → Γ ⊢a P ◂ Pr ∶ 𝒰 → 𝒰 ∩ 𝒮 ⊆ 𝒯)
      → Probe Γ P Pr 𝒮
    finish 𝒯 𝒯? = finish-with 𝒯 (memo 𝒯?)
      where
        finish-with :
          ∀ {Γ : Vec Sort γ}{P}{Pr : Proc γ δ}{𝒮}
          → (𝒯 : States δ) → Decidable 𝒯 → 𝒯 ⊆ 𝒮
          → (Satisfiable 𝒯 → Γ ⊢a P ◂ Pr ∶ 𝒯)
          → (∀ {𝒰} → Γ ⊢a P ◂ Pr ∶ 𝒰 → 𝒰 ∩ 𝒮 ⊆ 𝒯)
          → Probe Γ P Pr 𝒮
        finish-with 𝒯 𝒯? sub typed max with any-state? 𝒯?
        ... | yes some = found record
          { 𝒯 = 𝒯 ; 𝒯? = 𝒯? ; sub = sub ; typed = typed some ; max = max ; some = some }
        ... | no ¬some = none λ d (x , x∈) → ¬some (x , max d x∈)

    -- ══════════════════════════════════════════════════════════════════
    --  Probing, for one participant `P` over its tables `E`
    -- ══════════════════════════════════════════════════════════════════

    module Probing (P : Part)(E : Env P) where

      open Env E

      -- ── Deciding `Wait` ──
      --
      -- A walk with a visited set `V` of graph states, read up to `~`.  A
      -- revisit where `P ∈T` fails can never close, and the path from the
      -- first visit back to the revisit refutes every tree.

      module WaitDec (L : Behavs)(L? : Decidable L) where

        Vis : Vec Bool n → Behavs
        Vis V w = ∃[ a ] T (lookup V a) × a ~ w

        vis? : ∀ V s → Dec (Vis V s)
        vis? V s = FinP.any? (λ a → T? (lookup V a) ×-dec bisim? a s)

        mark : Vec Bool n → Behav → Vec Bool n
        mark V s = V [ s ]≔ true

        marked : ∀ V s → T (lookup (mark V s) s)
        marked V s rewrite VecP.lookup∘update s V true = tt

        kept : ∀ V s {a} → T (lookup V a) → T (lookup (mark V s) a)
        kept V s {a} x with a ≟Fin s
        ... | yes refl = marked V s
        ... | no a≢s rewrite VecP.lookup∘update′ a≢s V true = x

        vis/mark→ : ∀ V s {v} → Vis (mark V s) v → Vis V v ⊎ (s ~ v)
        vis/mark→ V s (a , ma , a~v) with a ≟Fin s
        ... | yes refl = inj₂ a~v
        ... | no a≢s rewrite VecP.lookup∘update′ a≢s V true = inj₁ (a , ma , a~v)

        vis/mark← : ∀ V s {v} → Vis V v ⊎ (s ~ v) → Vis (mark V s) v
        vis/mark← V s (inj₁ (a , ma , a~v)) = a , kept V s ma , a~v
        vis/mark← V s (inj₂ s~v)           = s , marked V s , s~v

        -- A step the walk takes: out of a non-leaf, idle state.
        _↝_ : Behav → Behav → Set
        s ↝ t = ¬ L s × P not-active-in s × ∃[ β ] s -< β >-> t

        ∈T/back : ∀ {s u} → Star _↝_ s u → P ∈T u → P ∈T s
        ∈T/back ε inT = inT
        ∈T/back ((_ , _ , _ , gr) ◅ rest) inT = in/later gr (∈T/back rest inT)

        -- A loop `s₀ ↝⁺ s₀` through states where `P ∉T` refutes every tree
        -- rooted on it.
        mutual
          refute :
            ∀ {W : Behavs}{s₀ m₀ u}
            → ¬ P ∈T s₀ → s₀ ↝ m₀ → Star _↝_ m₀ s₀
            → Star _↝_ s₀ u → Star _↝_ u s₀
            → WaitV P L W u → ⊥
          refute ¬inT x loop from ε        w = next ¬inT x loop from x loop w
          refute ¬inT x loop from (y ◅ to) w = next ¬inT x loop from y to w

          -- `u ↝ u′` is the loop's next step out of `u`.
          next :
            ∀ {W : Behavs}{s₀ m₀ u u′}
            → ¬ P ∈T s₀ → s₀ ↝ m₀ → Star _↝_ m₀ s₀
            → Star _↝_ s₀ u → u ↝ u′ → Star _↝_ u′ s₀
            → WaitV P L W u → ⊥
          next ¬inT x loop from (¬l , _ , _) to (wv/leaf l) = ¬l l
          next ¬inT x loop from _ to (wv/cycle _ inT) = ¬inT (∈T/back from inT)
          next ¬inT x loop from y@(_ , _ , _ , gr) to (wv/step _ _ k) =
            refute ¬inT x loop (from ◅◅ (y ◅ ε)) to (k gr)

        -- Every visited state has a non-empty walk to the current one.
        Inv : Vec Bool n → Behav → Set
        Inv V s = ∀ a → T (lookup V a) → ∃[ m ] a ↝ m × Star _↝_ m s

        vis/~ : ∀ {V a s} → Vis V a → a ~ s → Vis V s
        vis/~ (b , vb , b~a) a~s = b , vb , ~trans b~a a~s

        inv/step : ∀ {V s u} → Inv V s → s ↝ u → Inv (mark V s) u
        inv/step {V} {s} inv x a ma with a ≟Fin s
        ... | yes refl = _ , x , ε
        ... | no a≢s rewrite VecP.lookup∘update′ a≢s V true =
          let m , a↝m , m↝*s = inv a ma
          in m , a↝m , m↝*s ◅◅ (x ◅ ε)

        -- Marking an unmarked state shrinks the measure.
        shrink : ∀ V s → ¬ T (lookup V s) → n ∸ wt (mark V s) < n ∸ wt V
        shrink V s ¬vs =
          Nat.∸-monoʳ-<
            (wt/strict {left = V} {right = mark V s} (λ i → kept V s {i})
               (λ eq → ¬vs (subst (λ w → T (lookup w s)) (sym eq) (marked V s))))
            (wt-bound (mark V s))

        -- Neither a leaf nor a cycle is available at `s`.
        stuck :
          ∀ {V s} → ¬ L s → ¬ (P ∈T s × Vis V s)
          → WaitV P L (Vis V) s → ∃[ β ] ∃[ u ] s -< β >-> u × P not-active-in s
            × (∀ {β u} → s -< β >-> u → WaitV P L (λ v → Vis V v ⊎ (s ~ v)) u)
        stuck ¬l ¬cyc (wv/leaf l) = ⊥-elim (¬l l)
        stuck {V} ¬l ¬cyc (wv/cycle (a , va , a~s) inT) =
          ⊥-elim (¬cyc (inT , vis/~ {V} va a~s))
        stuck ¬l ¬cyc (wv/step na gr k) = _ , _ , gr , na , k

        wait-go :
          ∀ V s → Inv V s → Acc _<_ (n ∸ wt V) → Dec (WaitV P L (Vis V) s)
        wait-go V s inv (acc rs) with L? s
        ... | yes l = yes (wv/leaf l)
        ... | no ¬l with inT? s ×-dec vis? V s
        ...   | yes (inT , anc) = yes (wv/cycle (s , anc , ~refl) inT)
        ...   | no ¬cyc with act? s
        ...     | yes (_ , _ , gr , px) =
          no λ w → let _ , _ , _ , na , _ = stuck {V} ¬l ¬cyc w in ∉c→¬∈c (na gr) px
        ...     | no ¬act with moves? s
        ...       | no ¬st =
          no λ w → let β , u , gr , _ = stuck {V} ¬l ¬cyc w in ¬st (β , u , gr)
        ...       | yes (_ , _ , gr₀) with T? (lookup V s)
        ...         | yes vs =
          let m , s↝m , m↝*s = inv s vs
          in no (refute (λ inT → ¬cyc (inT , s , vs , ~refl)) s↝m m↝*s ε ε)
        ...         | no ¬vs
          with all-edges? (edges G s)
                 (λ mem → wait-go (mark V s) _
                            (inv/step {V} inv (¬l , idle ¬act , _ , listed⇒step {G = G} mem))
                            (rs (shrink V s ¬vs)))
        ...           | yes all =
          yes (wv/step (idle ¬act) gr₀ λ gr →
                waitV/mono (vis/mark→ V s) (all (step⇒listed {G = G} gr)))
        ...           | no ¬all =
          no λ w → let _ , _ , _ , _ , k = stuck {V} ¬l ¬cyc w
                   in ¬all λ mem → waitV/mono (vis/mark← V s) (k (listed⇒step {G = G} mem))

        wait? : ∀ s → Dec (WaitV P L (λ _ → ⊥) s)
        wait? s =
          map′ (waitV/mono empty) (waitV/mono λ ())
            (wait-go (replicate n false) s
               (λ a x → ⊥-elim (empty′ a x)) (<-wellFounded _))
          where
            empty′ : ∀ a → T (lookup (replicate n false) a) → ⊥
            empty′ a x rewrite VecP.lookup-replicate a false = x

            empty : ∀ {v} → Vis (replicate n false) v → ⊥
            empty (a , x , _) = empty′ a x

      Wait? : {L : States δ} → Decidable L → Decidable (Wait P L)
      Wait? L? (ws , s) = WaitDec.wait? _ (λ t → L? (ws , t)) s

      -- `Wait` lives in `Set₁`; a set of states stores the decided bit.
      Ready : {L : States δ} → Decidable L → States δ
      Ready L? x = T ⌊ Wait? L? x ⌋

      Ready? : {L : States δ}(L? : Decidable L) → Decidable (Ready L?)
      Ready? L? x = T? ⌊ Wait? L? x ⌋

      ready→ : ∀ {L : States δ}{L? : Decidable L}{x} → x ∈ Ready L? → x ∈ Wait P L
      ready→ = toWitness

      →ready : ∀ {L : States δ}{L? : Decidable L}{x} → x ∈ Wait P L → x ∈ Ready L?
      →ready = fromWitness

      -- The leaves of a tree are idle-reachable from its root.
      leaf : ∀ {L : States δ}{ws s}
           → (ws , s) ∈ Wait P L → ∃[ u ] (ws , u) ∈ L × Star (_⇝[ P ]_) s u
      leaf w = waitFind {γ = 0}{δ = 0} ∅ (waitV/walk w)

      -- ── The sets the rules mention ──

      Post? : ∀ α {X : States δ} → Decidable X → Decidable (Post α X)
      -- Order in each search: the CHEAPER test first.  Reachability rows are
      -- the expensive tables, so they come after a set lookup; an edge test
      -- is cheaper than a set entry, so it comes first.
      Post? α X? (ws , t) =
        map′ (λ (s , gr , x) → s , x , gr) (λ (s , x , gr) → s , gr , x)
          (FinP.any? (λ s → step? s α t ×-dec X? (ws , s)))

      Front? : {X : States δ} → Decidable X → Decidable (Front P X)
      -- `X` is a probe set (small, already tabulated); an idle-reachability
      -- row is expensive to build, so it is only built for states in `X`.
      Front? X? (ws , u) =
        map′ (λ (a , r) → r , a) (λ (r , a) → a , r)
          (act? u ×-dec FinP.any? (λ s → X? (ws , s) ×-dec walk? s u))

      Dom? : ∀ α → Decidable (Dom {δ = δ} α)
      Dom? α (_ , s) = FinP.any? (step? s α)

      Offers? : ∀ Q I → Decidable (Offers {δ = δ} Q P I)
      Offers? Q I (_ , s) =
        FinP.any? λ j → any-sort? λ U → FinP.any? (step? s (Q ⟶ P # j < U >))

      Ended? : Decidable (Ended {δ = δ} P)
      Ended? (_ , s) = ¬? (inT? s)

      Unskip? : {X : States δ} → Decidable X → Decidable (Unskip P X)
      -- Here `X` is an entry set, costlier than a `¬P`-run row: row first.
      Unskip? X? (ws , s) =
        map′ (λ (a , r , x) → a , x , r) (λ (a , x , r) → a , r , x)
          (FinP.any? (λ a → unskip? a s ×-dec X? (ws , a)))

      Var? : (X : Fin δ) → Decidable (Var X)
      Var? X (ws , s) = bisim? (lookup ws X) s

      Diag? : {X : States δ} → Decidable X → Decidable (Diag X)
      Diag? X? (W ∷ ws , s) = X? (ws , W) ×-dec bisim? W s

      -- A send or receive: the states `α` out of the frontier of `𝒮`.
      After : Action → States δ → States δ
      After α 𝒮 = Post α (Front P 𝒮)

      After? : ∀ α {𝒮 : States δ} → Decidable 𝒮 → Decidable (After α 𝒮)
      After? α 𝒮? = Post? α (memo (Front? 𝒮?))

      -- A `rec`: every state an idle walk from `𝒮` reaches, run back along
      -- `¬P` steps.
      Past : States δ → States δ
      Past 𝒮 (ws , a) = ∃[ s ] (ws , s) ∈ 𝒮 × ∃[ t ] Star (_⇝[ P ]_) s t × a -[¬ P ]->* t

      Past? : {𝒮 : States δ} → Decidable 𝒮 → Decidable (Past 𝒮)
      Past? 𝒮? (ws , a) =
        FinP.any? λ s → 𝒮? (ws , s) ×-dec FinP.any? λ t → walk? s t ×-dec unskip? a t

      -- ── The cases ──

      module _ {Γ : Vec Sort γ}{𝒮 : States δ}(𝒮? : Decidable 𝒮) where

        send-case :
          ∀ {Q I}{i : Fin (suc I)}{E S}{Pr : Proc γ δ}
          → Γ ⊢e E ∶ S
          → (dom? : Decidable (Dom {δ = δ} (P ⟶ Q # i < S >)))   -- a TABLE
          → Probe Γ P Pr (After (P ⟶ Q # i < S >) 𝒮)
          → Probe Γ P (Q ! i < E >∙ Pr) 𝒮
        send-case {Q = Q}{i = i}{E}{S}{Pr} etd dom? r =
          finish 𝒯 𝒯? proj₁ typed max
          where
            α = P ⟶ Q # i < S >

            𝒯 : States _
            𝒯 (ws , s) =
              (ws , s) ∈ 𝒮 × (ws , s) ∈ Ready dom?
              × (∀ u t → Star (_⇝[ P ]_) s u → u -< α >-> t → (ws , t) ∈ hit r)

            𝒯? : Decidable 𝒯
            -- Scans each reachable `u`'s edges, not every `(u , t)`.
            𝒯? (ws , s) =
              𝒮? (ws , s) ×-dec Ready? dom? (ws , s)
              ×-dec map′ (λ all u t run gr → all u run α t gr refl)
                         (λ all u run α′ t gr → λ { refl → all u t run gr })
                      (FinP.all? λ u → walk? s u →-dec
                         all-out? u (λ α′ t → (α′ ≟A α) →-dec hit? r (ws , t)))

            typed : Satisfiable 𝒯 → Γ ⊢a P ◂ Q ! i < E >∙ Pr ∶ 𝒯
            typed ((ws , s) , x∈) =
              a/send etd (λ {x} x∈′ → ready→ {L? = dom?}{x} (proj₁ (proj₂ x∈′)))
                (from-hit r
                   (λ { {ws′ , t} (u , ((s′ , s∈ , run) , _) , gr) →
                        proj₂ (proj₂ s∈) u t run gr })
                   (let u , (t , gr) , run =
                          leaf {L = Dom α}{ws}{s}
                            (ready→ {L? = dom?}{ws , s} (proj₁ (proj₂ x∈)))
                    in (ws , t) , u , ((s , x∈ , run) , (α , t , gr , ∈S refl)) , gr))

            max : ∀ {𝒰} → Γ ⊢a P ◂ Q ! i < E >∙ Pr ∶ 𝒰 → 𝒰 ∩ 𝒮 ⊆ 𝒯
            max (a/send etd′ rdy td) {ws , s} (x∈𝒰 , x∈𝒮) with ⊢e-unique etd′ etd
            ... | refl =
              x∈𝒮 , →ready {L? = dom?}{ws , s} (rdy {ws , s} x∈𝒰) ,
              λ u t run gr →
                into-hit r td
                  ( (u , ((s , x∈𝒰 , run) , (α , t , gr , ∈S refl)) , gr)
                  , (u , ((s , x∈𝒮 , run) , (α , t , gr , ∈S refl)) , gr) )

        -- `res` is a TABLE of the branch probes, one per `(j , U)`.
        recv-case :
          ∀ {Q I}{Br : Vec (Proc (suc γ) δ) (suc I)}
          → (offers? : Decidable (Offers {δ = δ} Q P I))   -- a TABLE
          → AllFin (suc I) (λ j → Sorted λ U →
              Probe (U ∷ Γ) P (lookup Br j) (After (Q ⟶ P # j < U >) 𝒮))
          → Probe Γ P (Σ Q ？· Br) 𝒮
        recv-case {Q = Q}{I}{Br} offers? tbl =
          finish 𝒯 𝒯? proj₁ typed max
          where
            α : Fin (suc I) → Sort → Action
            α j U = Q ⟶ P # j < U >

            res : ∀ j U → Probe (U ∷ Γ) P (lookup Br j) (After (α j U) 𝒮)
            res j U = lookupSort (lookupAll tbl j) U

            𝒯 : States _
            𝒯 (ws , s) =
              (ws , s) ∈ 𝒮 × (ws , s) ∈ Ready offers?
              × (∀ j U u t → Star (_⇝[ P ]_) s u → u -< α j U >-> t
                           → (ws , t) ∈ hit (res j U))

            𝒯? : Decidable 𝒯
            -- Scans each reachable `u`'s edges, not every `(u , t)`.
            𝒯? (ws , s) =
              𝒮? (ws , s) ×-dec Ready? offers? (ws , s)
              ×-dec map′ (λ all j U u t run gr → all u run (α j U) t gr j U refl)
                         (λ all u run α′ t gr j U → λ { refl → all j U u t run gr })
                      (FinP.all? λ u → walk? s u →-dec
                         all-out? u (λ α′ t → FinP.all? λ j → all-sort? λ U →
                           (α′ ≟A α j U) →-dec hit? (res j U) (ws , t)))

            typed : Satisfiable 𝒯 → Γ ⊢a P ◂ Σ Q ？· Br ∶ 𝒯
            typed _ =
              a/recv (λ {x} x∈ → ready→ {L? = offers?}{x} (proj₁ (proj₂ x∈)))
                λ {j}{U} sat →
                  from-hit (res j U)
                    (λ { {ws , t} (u , ((s , s∈ , run) , _) , gr) →
                         proj₂ (proj₂ s∈) j U u t run gr })
                    sat

            max : ∀ {𝒰} → Γ ⊢a P ◂ Σ Q ？· Br ∶ 𝒰 → 𝒰 ∩ 𝒮 ⊆ 𝒯
            max (a/recv rdy conts) {ws , s} (x∈𝒰 , x∈𝒮) =
              x∈𝒮 , →ready {L? = offers?}{ws , s} (rdy {ws , s} x∈𝒰) ,
              λ j U u t run gr →
                let y∈𝒰 = u , ((s , x∈𝒰 , run) , (α j U , t , gr , ∈R refl)) , gr
                    y∈C = u , ((s , x∈𝒮 , run) , (α j U , t , gr , ∈R refl)) , gr
                in into-hit (res j U) (conts (_ , y∈𝒰)) (y∈𝒰 , y∈C)

        if-case :
          ∀ {E}{A B : Proc γ δ}
          → Γ ⊢e E ∶ s/bool
          → Probe Γ P A 𝒮 → Probe Γ P B 𝒮
          → Probe Γ P (ifp E then A else B) 𝒮
        if-case etd rA rB =
          finish (hit rA ∩ hit rB) (λ x → hit? rA x ×-dec hit? rB x)
            (λ x∈ → sub rA (proj₁ x∈))
            (λ sat → a/if etd (from-hit rA proj₁ sat) (from-hit rB proj₂ sat))
            (λ { (a/if _ ttd ftd) x∈ → into-hit rA ttd x∈ , into-hit rB ftd x∈ })
          where
            sub : ∀ {Pr : Proc γ δ}(r : Probe Γ P Pr 𝒮) → hit r ⊆ 𝒮
            sub (found T) = Typed.sub T
            sub (none _)  = λ ()

        end-case : Probe Γ P ∅ 𝒮
        end-case =
          finish (𝒮 ∩ Ended P) (λ x → 𝒮? x ×-dec Ended? x) proj₁
            (λ _ → a/end proj₂)
            (λ { (a/end done) {x} (x∈𝒰 , x∈𝒮) → x∈𝒮 , done {x} x∈𝒰 })

        -- `L?` is the leaf set's TABLE.
        var-case : (X : Fin δ) → Decidable (Unskip P (Var X)) → Probe Γ P (v X) 𝒮
        var-case X L? =
          finish (𝒮 ∩ Ready L?)
            (λ x → 𝒮? x ×-dec Ready? L? x) proj₁
            (λ _ → a/var λ {x} x∈ → ready→ {L? = L?}{x} (proj₂ x∈))
            (λ { (a/var rdy) {x} (x∈𝒰 , x∈𝒮) → x∈𝒮 , →ready {L? = L?}{x} (rdy {x} x∈𝒰) })

        -- The entry states all of whose `~`-copies the body types at.
        Entry : ∀ {Pr : Proc γ (suc δ)} → Probe Γ P Pr (Diag (Past 𝒮)) → States δ
        Entry r (ws , W) = (ws , W) ∈ Past 𝒮 × (∀ s → W ~ s → (W ∷ ws , s) ∈ hit r)

        Entry? :
          ∀ {Pr : Proc γ (suc δ)} → Decidable (Past 𝒮)
          → (r : Probe Γ P Pr (Diag (Past 𝒮))) → Decidable (Entry r)
        Entry? past? r (ws , W) =
          past? (ws , W) ×-dec FinP.all? λ s → bisim? W s →-dec hit? r (W ∷ ws , s)

        -- `L?` is the TABLE of `Unskip P (Entry r)`.
        rec-case :
          ∀ {Pr : Proc γ (suc δ)}
          → MessageGuarded Pr
          → (r : Probe Γ P Pr (Diag (Past 𝒮)))
          → (L? : Decidable (Unskip P (Entry r)))
          → Probe Γ P (rec Pr) 𝒮
        rec-case {Pr} guarded r L? =
          finish 𝒯 (λ x → 𝒮? x ×-dec Ready? L? x) proj₁ typed max
          where
            𝒯 : States _
            𝒯 = 𝒮 ∩ Ready L?

            typed : Satisfiable 𝒯 → Γ ⊢a P ◂ rec Pr ∶ 𝒯
            typed ((ws , s) , x∈) =
              a/rec guarded
                (from-hit r (λ { {_ ∷ _ , _} ((_ , all) , W~s) → all _ W~s })
                   (let _ , (a , a∈ , _) , _ =
                          leaf {L = Unskip P (Entry r)}
                            (ready→ {L? = L?}{ws , s} (proj₂ x∈))
                    in (a ∷ ws , a) , a∈ , ~refl))
                (λ {x} x∈′ → ready→ {L? = L?}{x} (proj₂ x∈′))

            max : ∀ {𝒰} → Γ ⊢a P ◂ rec Pr ∶ 𝒰 → 𝒰 ∩ 𝒮 ⊆ 𝒯
            max (a/rec {𝒜 = 𝒜′} _ td rdy) {ws , s} (x∈𝒰 , x∈𝒮) =
              x∈𝒮 ,
              →ready {L? = L?}{ws , s}
                (waitV/leaf-mono
                  (λ { {t} ((a , a∈′ , tr) , run) →
                       let past = s , x∈𝒮 , t , run , tr
                       in a , (past , λ s′ a~s′ →
                                into-hit r td ((a∈′ , a~s′) , (past , a~s′))) , tr })
                  (waitV/walk (rdy {ws , s} x∈𝒰)))

      -- ── The recursion ──
      --
      -- Every set handed on is `memo`ised AT THE CALL, i.e. as an argument.

      mutual

        probe :
          ∀ {γ δ}(Γ : Vec Sort γ)(Pr : Proc γ δ)(𝒮 : States δ)
          → Decidable 𝒮 → Probe Γ P Pr 𝒮

        probe Γ (Q ! i < E >∙ Pr) 𝒮 𝒮?
          with any-sort? (exp? Γ E)
        ... | no ¬e = none λ { (a/send etd _ _) _ → ¬e (_ , etd) }
        ... | yes (S , etd) =
          send-case 𝒮? etd (memo (Dom? (P ⟶ Q # i < S >)))
            (probe Γ Pr (After (P ⟶ Q # i < S >) 𝒮)
               (memo (After? (P ⟶ Q # i < S >) 𝒮?)))

        probe Γ (Σ Q ？· Br) 𝒮 𝒮? =
          recv-case 𝒮? (memo (Offers? Q _)) (tabulateAll λ j → tabulateSort λ U →
            branch Br j (U ∷ Γ) (After (Q ⟶ P # j < U >) 𝒮)
              (memo (After? (Q ⟶ P # j < U >) 𝒮?)))

        probe Γ (ifp E then A else B) 𝒮 𝒮?
          with exp? Γ E s/bool
        ... | no ¬e = none λ { (a/if etd _ _) _ → ¬e etd }
        ... | yes etd =
          if-case 𝒮? etd (probe Γ A 𝒮 𝒮?) (probe Γ B 𝒮 𝒮?)

        probe Γ ∅ 𝒮 𝒮? = end-case 𝒮?

        probe Γ (v X) 𝒮 𝒮? = var-case 𝒮? X (memo (Unskip? (Var? X)))

        probe Γ (rec Pr) 𝒮 𝒮?
          with guarded? Pr
        ... | no ¬g = none λ { (a/rec g _ _) _ → ¬g g }
        ... | yes g = rec-probe Γ Pr 𝒮? g (memo (Past? 𝒮?))

        -- `past?` is shared by the body's probe set and the entry set.
        rec-probe :
          ∀ {γ δ}(Γ : Vec Sort γ)(Pr : Proc γ (suc δ)){𝒮 : States δ}
          → (𝒮? : Decidable 𝒮) → MessageGuarded Pr → Decidable (Past 𝒮)
          → Probe Γ P (rec Pr) 𝒮
        rec-probe Γ Pr {𝒮} 𝒮? g past? =
          rec-entry 𝒮? g past? (probe Γ Pr (Diag (Past 𝒮)) (memo (Diag? past?)))

        rec-entry :
          ∀ {γ δ}{Γ : Vec Sort γ}{Pr : Proc γ (suc δ)}{𝒮 : States δ}
          → (𝒮? : Decidable 𝒮) → MessageGuarded Pr → Decidable (Past 𝒮)
          → (r : Probe Γ P Pr (Diag (Past 𝒮)))
          → Probe Γ P (rec Pr) 𝒮
        rec-entry 𝒮? g past? r =
          rec-case 𝒮? g r (memo (Unskip? (memo (Entry? 𝒮? past? r))))

        branch :
          ∀ {γ δ m}(Br : Vec (Proc γ δ) m)(j : Fin m)
            (Γ : Vec Sort γ)(𝒮 : States δ)
          → Decidable 𝒮 → Probe Γ P (lookup Br j) 𝒮
        branch (B ∷ Bs) zero    Γ = probe Γ B
        branch (B ∷ Bs) (suc j)   = branch Bs j

    -- ══════════════════════════════════════════════════════════════════
    --  The old question: typed at exactly this set?
    -- ══════════════════════════════════════════════════════════════════

    -- An empty set is not probed: only the state-free facts matter.
    ∅s : States δ
    ∅s _ = ⊥

    alg-empty? : (Γ : Vec Sort γ)(P : Part)(Pr : Proc γ δ) → Dec (Γ ⊢a P ◂ Pr ∶ ∅s)
    alg-empty? Γ P (Q ! i < E >∙ Pr) with any-sort? (exp? Γ E) | alg-empty? Γ P Pr
    ... | no ¬e | _ = no λ { (a/send etd _ _) → ¬e (_ , etd) }
    ... | yes (S , etd) | yes td =
      yes (a/send etd (λ ()) (alg/mono (λ { (_ , ((_ , () , _) , _) , _) }) td))
    ... | yes _ | no ¬td = no λ { (a/send _ _ td) → ¬td (alg/mono (λ ()) td) }
    alg-empty? Γ P (Σ Q ？· Br) =
      yes (a/recv (λ ()) λ { (_ , _ , ((_ , () , _) , _) , _) })
    alg-empty? Γ P (ifp E then A else B)
      with exp? Γ E s/bool | alg-empty? Γ P A | alg-empty? Γ P B
    ... | yes etd | yes a | yes b = yes (a/if etd a b)
    ... | no ¬e | _ | _ = no λ { (a/if etd _ _) → ¬e etd }
    ... | _ | no ¬a | _ = no λ { (a/if _ a _) → ¬a a }
    ... | _ | _ | no ¬b = no λ { (a/if _ _ b) → ¬b b }
    alg-empty? Γ P ∅ = yes (a/end λ ())
    alg-empty? Γ P (v X) = yes (a/var λ ())
    alg-empty? Γ P (rec Pr) with guarded? Pr | alg-empty? Γ P Pr
    ... | yes g | yes td =
      yes (a/rec {𝒜 = ∅s} g (alg/mono (λ { {_ ∷ _ , _} (() , _) }) td) λ ())
    ... | no ¬g | _ = no λ { (a/rec g _ _) → ¬g g }
    ... | _ | no ¬td = no λ { (a/rec _ td _) → ¬td (alg/mono (λ ()) td) }

    alg?-in :
      ∀ {γ δ}{P : Part} → Env P
      → (Γ : Vec Sort γ)(Pr : Proc γ δ)(𝒮 : States δ) → Decidable 𝒮
      → Dec (Γ ⊢a P ◂ Pr ∶ 𝒮)
    alg?-in {P = P} E Γ Pr 𝒮 𝒮? = decide (memo 𝒮?)
      where
        decide : Decidable 𝒮 → Dec (Γ ⊢a P ◂ Pr ∶ 𝒮)
        decide 𝒮? with any-state? 𝒮?
        ... | no ¬sat =
          map′ (alg/mono λ x∈ → ⊥-elim (¬sat (_ , x∈))) (alg/mono λ ())
               (alg-empty? Γ P Pr)
        ... | yes sat = answer (Probing.probe P E Γ Pr 𝒮 𝒮?)
          where
            answer : Probe Γ P Pr 𝒮 → Dec (Γ ⊢a P ◂ Pr ∶ 𝒮)
            answer r with ⊆? 𝒮? (hit? r)
            ... | yes sub = yes (from-hit r sub sat)
            ... | no ¬sub = no λ d → ¬sub λ x∈ → into-hit r d (x∈ , x∈)

    alg? :
      ∀ {γ δ}
        (Γ : Vec Sort γ)
        (P : Part)
        (Pr : Proc γ δ)
        (𝒮 : States δ)
      → Decidable 𝒮
      → Dec (Γ ⊢a P ◂ Pr ∶ 𝒮)
    alg? Γ P Pr 𝒮 𝒮? = alg?-in (env P) Γ Pr 𝒮 𝒮?
