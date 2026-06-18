{-# OPTIONS --guardedness #-}

-- Deciding `⊢a` over a concrete graph.  `Probing.probe` returns the largest
-- subset of the probed set where the process is typed; `alg?` is one probe
-- at a singleton.
--
-- Every set is tabulated (`memo`) and passed as an argument, so Agda
-- evaluates it once; graph facts are tabulated per participant in `Env`.

open import Data.Nat using (ℕ; zero; suc; _∸_; _<_)
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
open import Data.Bool.Properties using (T-∧)
open import Function.Bundles using (Equivalence)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

open import Data.Product using (Σ-syntax; ∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Product.Properties using (≡-dec)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Bool using (Bool; true; false; T; _∧_)
open import Data.Maybe using (just; nothing)

open import Function using (_∘_)

open import Induction.WellFounded using (Acc; acc)

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable
  using (⌊_⌋; T?; map′; _×-dec_; _→-dec_; ¬?; toWitness; fromWitness)
open import Relation.Unary using (Decidable; _∈_; _⊆_; _∩_; Satisfiable)
open import Data.Fin.Subset using () renaming (_∈_ to _∈ˢ_)
open import Data.Fin.Subset.Properties using () renaming (_∈?_ to _∈ˢ?_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; cong)
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
  open import Definitions.Graph.Bisimulation N
    using (Matrix; approximation; bisimulationCorrect; sound; complete)
  open import Definitions.Graph.Action N
    using (eqFin; eqFin-sound; eqFin-refl
          ; eqMaybeEvent; eqMaybeEvent-sound; eqMaybeEvent-refl)
  open import Definitions.Graph.Reachability N
    using (Step; PathVia; path/nil; path/cons; reachVia; reachFix; reachFix≡; reachVia-sound
          ; reachVia-complete; T→≡true; ≡true→T; reach→∈T; ∈T→reach; active?
          ; anyActive→∈; ∈α-lift; wt; wt/strict; wt-bound)

  module AlgCheck
    (G : Graph)
    (wb : WellBehaved (graphTheory G))
    where

    open Typing.MPST wb
    open import Definitions.Typing.Alg wb
    open import Definitions.Typing.MainLeaf wb using (waitFind)

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
    -- A decision read off a precomputed bit; the proof is built on demand.

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

    -- Is `P`'s event in `α` exactly `e`?  One bit.
    matchEv : Part → Event → Action → Bool
    matchEv P e α = eqMaybeEvent (ev α P) (just e)

    matchEv-sound : ∀ P e α → T (matchEv P e α) → ev α P ≡ just e
    matchEv-sound P e α = eqMaybeEvent-sound (ev α P) (just e)

    matchEv-refl : ∀ P e α → ev α P ≡ just e → T (matchEv P e α)
    matchEv-refl P e α eq =
      subst (λ x → T (eqMaybeEvent x (just e))) (sym eq)
        (eqMaybeEvent-refl (just e))

    -- A step `s → t` with event `e` at `P`: one scan of `s`'s edges.
    evstep? : ∀ s P e t → Dec (s -<[ P ↦ e ]>-> t)
    evstep? s P e t =
      map′ (λ x →
             let (α′ , t′) , mem , px = find (any⁻ hit (edges G s) x)
                 a , b = Equivalence.to T-∧ px
             in α′ , matchEv-sound P e α′ a
              , subst (λ z → s -< α′ >-> z) (eqFin-sound b)
                  (listed⇒step mem))
           (λ { (α′ , eq , gr) →
                any⁺ hit
                  (lose (step⇒listed gr)
                    (Equivalence.from T-∧
                      (matchEv-refl P e α′ eq , eqFin-refl t))) })
           (T? (Data.List.any hit (edges G s)))
      where
        hit : Edge n → Bool
        hit (α′ , t′) = matchEv P e α′ ∧ eqFin t′ t

    -- The same, for a receive of `Q`'s process (`Foreign`).
    evstepᴿ? : ∀ s Q R e t → Dec (s -<[ Q ∣ R ↦ e ]>-> t)
    evstepᴿ? s Q R e t =
      map′ (λ (x : Any.Any
                     (λ e′ → T (matchEv R e (proj₁ e′))
                             × T (eqFin (proj₂ e′) t) × Foreign Q (proj₁ e′))
                     (edges G s)) →
             let (α′ , t′) , mem , a , b , fr = find x
             in α′ , matchEv-sound R e α′ a
              , subst (λ z → s -< α′ >-> z) (eqFin-sound b)
                  (listed⇒step mem)
              , fr)
           (λ { (α′ , eq , gr , fr) →
                lose (step⇒listed gr)
                  (matchEv-refl R e α′ eq , eqFin-refl t , fr) })
           (Any.any?
              (λ e′ → T? (matchEv R e (proj₁ e′))
                      ×-dec T? (eqFin (proj₂ e′) t)
                      ×-dec Foreign? Q (proj₁ e′))
              (edges G s))

    Steps : Behav → Set
    Steps s = ∃[ β ] ∃[ u ] s -< β >-> u

    steps? : ∀ s → Dec (Steps s)
    steps? s = from (edges G s) listed⇒step step⇒listed
      where
        from : (es : List (Edge n))
             → (∀ {α u} → (α , u) ∈L es → s -< α >-> u)
             → (∀ {α u} → s -< α >-> u → (α , u) ∈L es)
             → Dec (Steps s)
        from []            _   back = no λ { (_ , _ , gr) → case (back gr) }
          where case : ∀ {e} → e ∈L [] → ⊥
                case ()
        from ((β , u) ∷ _) fwd _    = yes (β , u , fwd (here refl))

    -- The decider gets the membership proof (`WaitDec` needs it).
    all-edges? :
      ∀ {ℓ}{B : Edge n → Set ℓ}(es : List (Edge n))
      → (∀ {e} → e ∈L es → Dec (B e))
      → Dec (∀ {e} → e ∈L es → B e)
    all-edges? [] _ = yes λ ()
    all-edges? (e ∷ es) B? with B? (here refl) | all-edges? es (B? ∘ there)
    ... | yes b | yes bs = yes λ { (here refl) → b ; (there m) → bs m }
    ... | no ¬b | _      = no λ all → ¬b (all (here refl))
    ... | _     | no ¬bs = no λ all → ¬bs (all ∘ there)

    all-out? :
      ∀ u {B : Action → Behav → Set} → (∀ α t → Dec (B α t))
      → Dec (∀ α t → u -< α >-> t → B α t)
    all-out? u B? =
      map′ (λ all α t gr → all (step⇒listed gr))
           (λ all {e} mem → all (proj₁ e) (proj₂ e) (listed⇒step mem))
           (all-edges? (edges G u) λ {e} _ → B? (proj₁ e) (proj₂ e))

    active⇒? : ∀ P s → Dec (Active P s)
    active⇒? P s with active? G P s
    ... | yes any =
      let (α , u) , mem , px = anyActive→∈ G (edges G s) any
      in yes (α , u , listed⇒step mem , px)
    ... | no ¬any =
      no λ { (_ , _ , gr , px) → ¬any (∈α-lift G (step⇒listed gr) px) }

    idle : ∀ {P s} → ¬ Active P s → P not-active-in s
    idle {P} ¬act {α} gr = ¬∈αˢ→∉αˢ {P} {α} (λ px → ¬act (_ , _ , gr , px))

    -- ══════════════════════════════════════════════════════════════════
    --  Reachability, as rows of reachable states
    -- ══════════════════════════════════════════════════════════════════

    -- Idle walks: `PathVia` filtered by "`P` is not active here".
    ok : PartSet → Behav → Bool
    ok P s = ⌊ ¬? (active? G P s) ⌋

    -- Over any filter that agrees with `ok P` (in practice: its table).
    path⇒walk :
      ∀ {P}{ok′ : Behav → Bool} → (∀ s → ok′ s ≡ ok P s)
      → ∀ {s t k} → PathVia G ok′ s t k → Star (_⇝[ P ]_) s t
    path⇒walk ok≡ path/nil = ε
    path⇒walk {P} ok≡ (path/cons oks gr rest) =
      (idle (λ { (_ , _ , gr′ , px) →
                 toWitness (subst T (ok≡ _) oks)
                   (∈α-lift G (step⇒listed gr′) px) })
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
              in ∉αˢ→¬∈αˢ {P} {α} (na (listed⇒step mem)) px))
           gr p

    -- `¬P`-labelled runs: plain reachability in the graph without `P`'s edges.
    G¬ : PartSet → Graph
    G¬ P = graph n (V.map (filter (λ e → P ∉αˢ? proj₁ e)) (outgoing G))

    edge¬⇒ :
      ∀ {P s α t} → Step (G¬ P) s α t → s -< α >-> t × P ∉αˢ α
    edge¬⇒ {P} {s} gr
      with ∈-filter⁻ (λ e → P ∉αˢ? proj₁ e)
             (subst (_ ∈L_) (VecP.lookup-map s _ (outgoing G))
                (step⇒listed gr))
    ... | mem , P∉α = listed⇒step mem , P∉α

    ⇒edge¬ :
      ∀ {P s α t} → s -< α >-> t → P ∉αˢ α → Step (G¬ P) s α t
    ⇒edge¬ {P} {s} gr P∉α =
      listed⇒step
        (subst (_ ∈L_) (sym (VecP.lookup-map s _ (outgoing G)))
          (∈-filter⁺ (λ e → P ∉αˢ? proj₁ e) (step⇒listed gr) P∉α))

    path⇒run : ∀ {P s t k} → PathVia (G¬ P) (λ _ → true) s t k → s -[¬ P ]->* t
    path⇒run path/nil = skip/refl
    path⇒run (path/cons _ gr rest) =
      let gr′ , P∉α = edge¬⇒ gr in tr¬/step gr′ P∉α (path⇒run rest)

    run⇒path :
      ∀ {P s t αs} → s -[ αs ]-> t → All (P ∉αˢ_) αs
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

    record Env (P : PartSet) : Set where
      field
        walk?   : ∀ s t → Dec (Star (_⇝[ P ]_) s t)
        unskip? : ∀ s t → Dec (s -[¬ P ]->* t)
        act?    : ∀ s → Dec (Active P s)
        inT?    : ∀ s → Dec (P ∈T s)
        moves?  : ∀ s → Dec (Steps s)
        bisim?  : ∀ s t → Dec (s ~ t)

    -- Tables are arguments, so each is computed once.
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

    -- A table of rows, COMPUTED by `reachFix` and specified by `reachVia`.
    rows : (H : Graph)(ok′ : Fin (size H) → Bool) → Vec (Vec Bool (size H)) (size H)
    rows H ok′ = V.tabulate (reachFix H ok′)

    rows≡ : ∀ (H : Graph) ok′ s → lookup (rows H ok′) s ≡ reachVia H ok′ s
    rows≡ H ok′ s = trans (VecP.lookup∘tabulate _ s) (reachFix≡ H ok′ s)

    env : ∀ P → Env P
    -- The idle filter is tabulated first, and the idle rows read the table.
    env P = with-oks (V.tabulate (ok P)) (λ s → VecP.lookup∘tabulate _ s)
      where
        with-oks : (oks : Vec Bool n) → (∀ s → lookup oks s ≡ ok P s) → Env P
        with-oks oks oks≡ =
          mkEnv P oks oks≡
            (rows G (lookup oks))       (rows≡ G (lookup oks))
            (rows (G¬ P) (λ _ → true)) (rows≡ (G¬ P) (λ _ → true))
            (approximation G) refl
            (rows G (λ _ → true))       (rows≡ G (λ _ → true))

    -- ══════════════════════════════════════════════════════════════════
    --  Guardedness
    -- ══════════════════════════════════════════════════════════════════

    guarded? : (Pr : Proc γ δ) → Dec (MessageGuarded Pr)
    guarded? (_ ⇒ _ ! _ < _ >∙ _) = yes mg/send
    guarded? (_ ⇐ _ ？· _)        = yes mg/recv
    guarded? (ifp _ then A else B) =
      map′ (λ (a , b) → mg/if a b) (λ { (mg/if a b) → a , b })
           (guarded? A ×-dec guarded? B)
    guarded? ∅       = no λ ()
    guarded? (v _)   = no λ ()
    guarded? (rec _) = no λ ()

    -- ══════════════════════════════════════════════════════════════════
    --  Probes
    -- ══════════════════════════════════════════════════════════════════

    -- The largest nonempty `𝒯 ⊆ 𝒮` where `Pr` is typed.
    record Found (Γ : Vec Sort γ)(P : PartSet)(Pr : Proc γ δ)(𝒮 : States δ)
      : Set₁ where
      field
        𝒯     : States δ
        𝒯?    : Decidable 𝒯
        sub   : 𝒯 ⊆ 𝒮
        typed : Γ ⊢a P ◂ Pr ∶ 𝒯
        max   : ∀ {𝒰} → Γ ⊢a P ◂ Pr ∶ 𝒰 → 𝒰 ∩ 𝒮 ⊆ 𝒯
        some  : Satisfiable 𝒯

    data Probe (Γ : Vec Sort γ)(P : PartSet)(Pr : Proc γ δ)(𝒮 : States δ)
      : Set₁ where
      found : Found Γ P Pr 𝒮 → Probe Γ P Pr 𝒮
      none  : (∀ {𝒰} → Γ ⊢a P ◂ Pr ∶ 𝒰 → ¬ Satisfiable (𝒰 ∩ 𝒮)) → Probe Γ P Pr 𝒮

    -- What a probe found, as a set (empty for `none`).
    hit : ∀ {Γ : Vec Sort γ}{P}{Pr : Proc γ δ}{𝒮} → Probe Γ P Pr 𝒮 → States δ
    hit (found T) = Found.𝒯 T
    hit (none _)  = λ _ → ⊥

    hit? : ∀ {Γ : Vec Sort γ}{P}{Pr : Proc γ δ}{𝒮}(r : Probe Γ P Pr 𝒮) → Decidable (hit r)
    hit? (found T) = Found.𝒯? T
    hit? (none _)  = λ _ → no λ ()

    from-hit :
      ∀ {Γ : Vec Sort γ}{P}{Pr : Proc γ δ}{𝒮 X}(r : Probe Γ P Pr 𝒮)
      → X ⊆ hit r → Satisfiable X → Γ ⊢a P ◂ Pr ∶ X
    from-hit (found T) sub _       = alg/mono sub (Found.typed T)
    from-hit (none _)  sub (_ , x) = ⊥-elim (sub x)

    into-hit :
      ∀ {Γ : Vec Sort γ}{P}{Pr : Proc γ δ}{𝒮}(r : Probe Γ P Pr 𝒮)
      → ∀ {𝒰} → Γ ⊢a P ◂ Pr ∶ 𝒰 → 𝒰 ∩ 𝒮 ⊆ hit r
    into-hit (found T) d     = Found.max T d
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

    module Probing (P : PartSet)(E : Env P) where

      open Env E

      -- ── Deciding `Wait` ──
      --
      -- A walk with a visited set, read up to `~`.  A revisit where
      -- `P ∉T` gives a loop that refutes every tree.

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
        ...     | yes (α , _ , gr , px) =
          no λ w → let _ , _ , _ , na , _ = stuck {V} ¬l ¬cyc w
                   in ∉αˢ→¬∈αˢ {P} {α} (na gr) px
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
                            (inv/step {V} inv (¬l , idle ¬act , _ , listed⇒step mem))
                            (rs (shrink V s ¬vs)))
        ...           | yes all =
          yes (wv/step (idle ¬act) gr₀ λ gr →
                waitV/mono (vis/mark→ V s) (all (step⇒listed gr)))
        ...           | no ¬all =
          no λ w → let _ , _ , _ , _ , k = stuck {V} ¬l ¬cyc w
                   in ¬all λ mem → waitV/mono (vis/mark← V s) (k (listed⇒step mem))

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
      leaf w = waitFind (waitV/walk w)

      -- ── The sets the rules mention ──

      PostBy? :
        ∀ {step}{X : States δ}
        → (∀ s t → Dec (step s t)) → Decidable X → Decidable (PostBy step X)
      -- Cheaper test first: edge test, set lookup, reachability row.
      PostBy? step? X? (ws , t) =
        map′ (λ (s , gr , x) → s , x , gr) (λ (s , x , gr) → s , gr , x)
          (FinP.any? (λ s → step? s t ×-dec X? (ws , s)))

      Front? : {X : States δ} → Decidable X → Decidable (Front P X)
      -- Idle-reachability rows are built only for states in `X`.
      Front? X? (ws , u) =
        map′ (λ (a , r) → r , a) (λ (r , a) → a , r)
          (act? u ×-dec FinP.any? (λ s → X? (ws , s) ×-dec walk? s u))

      Focus? : ∀ X s → Dec (Focus P X s)
      Focus? X s =
        map′ (λ all tr gr own → all _ tr _ _ gr own)
             (λ f u tr α t gr own → f tr gr own)
             (FinP.all? λ u → unskip? s u →-dec
                all-out? u (λ α t → (P ∈αˢ? α) →-dec (X ∈α? α)))

      Dom? : ∀ R e → Decidable (Dom {δ = δ} P R e)
      Dom? R e (_ , s) =
        Focus? R s ×-dec
        map′ (λ x →
               let (α , t) , mem , b = find (any⁻ bit (edges G s) x)
               in t , α , matchEv-sound R e α b , listed⇒step mem)
             (λ { (t , α , eq , gr) →
                  any⁺ bit (lose (step⇒listed gr) (matchEv-refl R e α eq)) })
             (T? (Data.List.any bit (edges G s)))
        where
          bit : Edge n → Bool
          bit (α , _) = matchEv R e α

      -- `α` is a receive by `R` from `Q`, of arity `suc I`.
      OffersAct : Part → Part → ℕ → Action → Set
      OffersAct R Q I α =
        Σ[ j ∈ Fin (suc I) ] ∃[ U ] ev α R ≡ just ((？ Q) # j < U >)

      -- … and a receive of `P`'s process: sent from outside `P`.
      OffersActᴾ : Part → Part → ℕ → Action → Set
      OffersActᴾ R Q I α = OffersAct R Q I α × Foreign P α

      offersAct? : ∀ R Q I α → Dec (OffersAct R Q I α)
      offersAct? R Q I α with ev α R
      ... | nothing          = no λ { (_ , _ , ()) }
      ... | just ((! _) # _) = no λ { (_ , _ , ()) }
      ... | just ((？ Q′) # (_<_> {I′} j U)) with Q′ ≟Fin Q | I′ Nat.≟ I
      ...   | yes refl | yes refl = yes (j , U , refl)
      ...   | no Q′≢Q  | _        = no λ { (_ , _ , refl) → Q′≢Q refl }
      ...   | _        | no I′≢I  = no λ { (_ , _ , refl) → I′≢I refl }

      -- One scan of `s`'s edges, not one per label, sort and target.
      Offers? : ∀ Q R I → Decidable (Offers {δ = δ} P Q R I)
      Offers? Q R I (_ , s) =
        Focus? R s ×-dec
        map′ (λ (x : Any.Any (λ e → OffersActᴾ R Q I (proj₁ e)) (edges G s)) →
               let (α , t) , mem , (j , U , eq) , fr = find x
               in j , U , t , α , eq , listed⇒step mem , fr)
             (λ { (j , U , t , α , eq , gr , fr) →
                  lose (step⇒listed gr) ((j , U , eq) , fr) })
             (Any.any?
                (λ e → offersAct? R Q I (proj₁ e) ×-dec Foreign? P (proj₁ e))
                (edges G s))

      Ended? : Decidable (Ended {δ = δ} P)
      Ended? (_ , s) = ¬? (inT? s)

      Unskip? : {X : States δ} → Decidable X → Decidable (Unskip P X)
      -- Cheaper test first: bisimilarity, run row, then the entry set.
      Unskip? X? (ws , s) =
        map′ (λ (a , (s′ , e , r) , x) → a , x , s′ , r , e)
             (λ (a , x , s′ , r , e) → a , (s′ , e , r) , x)
          (FinP.any? (λ a →
             FinP.any? (λ s′ → bisim? s′ s ×-dec unskip? a s′)
               ×-dec X? (ws , a)))

      Var? : (X : Fin δ) → Decidable (Var X)
      Var? X (ws , s) = bisim? (lookup ws X) s

      Diag? : {X : States δ} → Decidable X → Decidable (Diag X)
      Diag? X? (W ∷ ws , s) = X? (ws , W) ×-dec bisim? W s

      -- Out of the frontier of `𝒮`, by a step with event `e` at `R`.
      After : Part → Event → States δ → States δ
      After R e 𝒮 = Post R e (Front P 𝒮)

      After? : ∀ R e {𝒮 : States δ} → Decidable 𝒮 → Decidable (After R e 𝒮)
      After? R e 𝒮? = PostBy? (λ s → evstep? s R e) (memo (Front? 𝒮?))

      -- A receive: by a step sent from outside `P`.
      Afterᴿ : Part → Event → States δ → States δ
      Afterᴿ R e 𝒮 = Postᴿ P R e (Front P 𝒮)

      Afterᴿ? :
        ∀ R e {𝒮 : States δ} → Decidable 𝒮 → Decidable (Afterᴿ R e 𝒮)
      Afterᴿ? R e 𝒮? = PostBy? (λ s → evstepᴿ? s P R e) (memo (Front? 𝒮?))

      -- The states an idle walk from `𝒮` reaches, up to `~`.
      Reached : States δ → States δ
      Reached 𝒮 (ws , u) =
        ∃[ t ] u ~ t × ∃[ s ] (ws , s) ∈ 𝒮 × Star (_⇝[ P ]_) s t

      Reached? : {𝒮 : States δ} → Decidable 𝒮 → Decidable (Reached 𝒮)
      Reached? 𝒮? (ws , u) =
        FinP.any? λ t →
          bisim? u t ×-dec FinP.any? λ s → 𝒮? (ws , s) ×-dec walk? s t

      -- The states whose `¬P` run ends in `R`.
      Back : States δ → States δ
      Back R (ws , a) = ∃[ u ] a -[¬ P ]->* u × (ws , u) ∈ R

      Back? : {R : States δ} → Decidable R → Decidable (Back R)
      Back? R? (ws , a) = FinP.any? λ u → unskip? a u ×-dec R? (ws , u)

      -- A `rec`: every state whose `¬P` run ends in `Reached 𝒮` (`a/rec`'s
      -- `Unskip` ends up to `~`).
      Past : States δ → States δ
      Past 𝒮 = Back (Reached 𝒮)

      -- `Reached` is tabulated once, as an argument.
      Past? : {𝒮 : States δ} → Decidable 𝒮 → Decidable (Past 𝒮)
      Past? 𝒮? = Back? (memo (Reached? 𝒮?))

      -- ── The cases ──

      module _ {Γ : Vec Sort γ}{𝒮 : States δ}(𝒮? : Decidable 𝒮) where

        send-case :
          ∀ {Q Qs I}{i : Fin (suc I)}{E S}{Pr : Proc γ δ}
          → Q ∈ˢ P
          → Γ ⊢e E ∶ S
          → (dom? : Decidable (Dom {δ = δ} P Q ((! Qs) # i < S >)))   -- a TABLE
          → Probe Γ P Pr (After Q ((! Qs) # i < S >) 𝒮)
          → Probe Γ P (Q ⇒ Qs ! i < E >∙ Pr) 𝒮
        send-case {Q = Q}{Qs}{i = i}{E}{S}{Pr} Q∈ etd dom? r =
          finish 𝒯 𝒯? proj₁ typed max
          where
            e = (! Qs) # i < S >

            𝒯 : States _
            𝒯 (ws , s) =
              (ws , s) ∈ 𝒮 × (ws , s) ∈ Ready dom?
              × (∀ u t → Star (_⇝[ P ]_) s u → u -<[ Q ↦ e ]>-> t
                       → (ws , t) ∈ hit r)

            𝒯? : Decidable 𝒯
            -- Scans each reachable `u`'s edges, not every `(u , t)`; the
            -- event test is one bit (`matchEv`).
            𝒯? (ws , s) =
              𝒮? (ws , s) ×-dec Ready? dom? (ws , s)
              ×-dec map′ (λ { all u t run (α′ , eq , gr) →
                              all u run α′ t gr (matchEv-refl Q e α′ eq) })
                         (λ all u run α′ t gr b →
                            all u t run (α′ , matchEv-sound Q e α′ b , gr))
                      (FinP.all? λ u → walk? s u →-dec
                         all-out? u (λ α′ t →
                           T? (matchEv Q e α′) →-dec hit? r (ws , t)))

            typed : Satisfiable 𝒯 → Γ ⊢a P ◂ Q ⇒ Qs ! i < E >∙ Pr ∶ 𝒯
            typed ((ws , s) , x∈) =
              a/send Q∈ etd
                (λ {x} x∈′ → ready→ {L? = dom?}{x} (proj₁ (proj₂ x∈′)))
                (from-hit r
                   (λ { {ws′ , t} (u , ((s′ , s∈ , run) , _) , gr) →
                        proj₂ (proj₂ s∈) u t run gr })
                   (let u , (_ , t , (α , eq , g)) , run =
                          leaf {L = Dom P Q e}{ws}{s}
                            (ready→ {L? = dom?}{ws , s} (proj₁ (proj₂ x∈)))
                    in (ws , t) , u
                     , ((s , x∈ , run) , (α , t , g , (_ , Q∈ , _ , eq)))
                     , (α , eq , g)))

            max : ∀ {𝒰} → Γ ⊢a P ◂ Q ⇒ Qs ! i < E >∙ Pr ∶ 𝒰 → 𝒰 ∩ 𝒮 ⊆ 𝒯
            max (a/send _ etd′ rdy td) {ws , s} (x∈𝒰 , x∈𝒮)
              with ⊢e-unique etd′ etd
            ... | refl =
              x∈𝒮 , →ready {L? = dom?}{ws , s} (rdy {ws , s} x∈𝒰) ,
              λ { u t run (α , eq , g) →
                  into-hit r td
                    ( (u , ((s , x∈𝒰 , run) , (α , t , g , (_ , Q∈ , _ , eq)))
                         , (α , eq , g))
                    , (u , ((s , x∈𝒮 , run) , (α , t , g , (_ , Q∈ , _ , eq)))
                         , (α , eq , g)) ) }

        -- `res` is a TABLE of the branch probes, one per `(j , U)`.
        recv-case :
          ∀ {Q R I}{Br : Vec (Proc (suc γ) δ) (suc I)}
          → R ∈ˢ P
          → (offers? : Decidable (Offers {δ = δ} P Q R I))   -- a TABLE
          → AllFin (suc I) (λ j → Sorted λ U →
              Probe (U ∷ Γ) P (lookup Br j) (Afterᴿ R ((？ Q) # j < U >) 𝒮))
          → Probe Γ P (R ⇐ Q ？· Br) 𝒮
        recv-case {Q = Q}{R}{I}{Br} R∈ offers? tbl =
          finish 𝒯 𝒯? proj₁ typed max
          where
            e : Fin (suc I) → Sort → Event
            e j U = (？ Q) # j < U >

            res : ∀ j U → Probe (U ∷ Γ) P (lookup Br j) (Afterᴿ R (e j U) 𝒮)
            res j U = lookupSort (lookupAll tbl j) U

            𝒯 : States _
            𝒯 (ws , s) =
              (ws , s) ∈ 𝒮 × (ws , s) ∈ Ready offers?
              × (∀ j U u t → Star (_⇝[ P ]_) s u → u -<[ P ∣ R ↦ e j U ]>-> t
                           → (ws , t) ∈ hit (res j U))

            𝒯? : Decidable 𝒯
            -- Scans each reachable `u`'s edges, not every `(u , t)`.
            𝒯? (ws , s) =
              𝒮? (ws , s) ×-dec Ready? offers? (ws , s)
              ×-dec map′ (λ { all j U u t run (α′ , eq , gr , fr) →
                              all u run α′ t gr j U
                                (matchEv-refl R (e j U) α′ eq , fr) })
                         (λ all u run α′ t gr j U (b , fr) →
                            all j U u t run
                              (α′ , matchEv-sound R (e j U) α′ b , gr , fr))
                      (FinP.all? λ u → walk? s u →-dec
                         all-out? u (λ α′ t → FinP.all? λ j → all-sort? λ U →
                           (T? (matchEv R (e j U) α′) ×-dec Foreign? P α′)
                             →-dec hit? (res j U) (ws , t)))

            typed : Satisfiable 𝒯 → Γ ⊢a P ◂ R ⇐ Q ？· Br ∶ 𝒯
            typed _ =
              a/recv R∈
                (λ {x} x∈ → ready→ {L? = offers?}{x} (proj₁ (proj₂ x∈)))
                λ {j}{U} sat →
                  from-hit (res j U)
                    (λ { {ws , t} (u , ((s , s∈ , run) , _) , gr) →
                         proj₂ (proj₂ s∈) j U u t run gr })
                    sat

            max : ∀ {𝒰} → Γ ⊢a P ◂ R ⇐ Q ？· Br ∶ 𝒰 → 𝒰 ∩ 𝒮 ⊆ 𝒯
            max (a/recv _ rdy conts) {ws , s} (x∈𝒰 , x∈𝒮) =
              x∈𝒮 , →ready {L? = offers?}{ws , s} (rdy {ws , s} x∈𝒰) ,
              λ { j U u t run (α , eq , g , fr) →
                  let y∈𝒰 = u , ((s , x∈𝒰 , run)
                                  , (α , t , g , (_ , R∈ , _ , eq)))
                              , (α , eq , g , fr)
                      y∈C = u , ((s , x∈𝒮 , run)
                                  , (α , t , g , (_ , R∈ , _ , eq)))
                              , (α , eq , g , fr)
                  in into-hit (res j U) (conts (_ , y∈𝒰)) (y∈𝒰 , y∈C) }

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
            sub (found T) = Found.sub T
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
                  (λ { {t} ((a , a∈′ , u , tr , u~t) , run) →
                       let past = u , tr , t , u~t , s , x∈𝒮 , run
                       in a , (past , λ s′ a~s′ →
                                into-hit r td ((a∈′ , a~s′) , (past , a~s′)))
                          , u , tr , u~t })
                  (waitV/walk (rdy {ws , s} x∈𝒰)))

      -- ── The recursion ──
      --
      -- Every set handed on is `memo`ised AT THE CALL, i.e. as an argument.

      mutual

        probe :
          ∀ {γ δ}(Γ : Vec Sort γ)(Pr : Proc γ δ)(𝒮 : States δ)
          → Decidable 𝒮 → Probe Γ P Pr 𝒮

        probe Γ (Q ⇒ Qs ! i < E >∙ Pr) 𝒮 𝒮?
          with Q ∈ˢ? P | any-sort? (checkExpression Γ E)
        ... | no Q∉ | _ = none λ { (a/send Q∈ _ _ _) _ → Q∉ Q∈ }
        ... | _ | no ¬e = none λ { (a/send _ etd _ _) _ → ¬e (_ , etd) }
        ... | yes Q∈ | yes (S , etd) =
          send-case 𝒮? Q∈ etd (memo (Dom? Q ((! Qs) # i < S >)))
            (probe Γ Pr (After Q ((! Qs) # i < S >) 𝒮)
               (memo (After? Q ((! Qs) # i < S >) 𝒮?)))

        probe Γ (R ⇐ Q ？· Br) 𝒮 𝒮?
          with R ∈ˢ? P
        ... | no R∉ = none λ { (a/recv R∈ _ _) _ → R∉ R∈ }
        ... | yes R∈ =
          recv-case 𝒮? R∈ (memo (Offers? Q R _))
            (tabulateAll λ j → tabulateSort λ U →
              branch Br j (U ∷ Γ) (Afterᴿ R ((？ Q) # j < U >) 𝒮)
                (memo (Afterᴿ? R ((？ Q) # j < U >) 𝒮?)))

        probe Γ (ifp E then A else B) 𝒮 𝒮?
          with checkExpression Γ E s/bool
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
    --  Typed at a state
    -- ══════════════════════════════════════════════════════════════════

    -- Only singletons are asked about (`tc?`), and a singleton is never
    -- empty, so the probe always has a state to start from.
    at : State δ → States δ
    at x = x ≡_

    at? : (x : State δ) → Decidable (at x)
    at? x = ≡-dec (VecP.≡-dec FinP._≟_) FinP._≟_ x

    alg? :
      ∀ {γ δ}
        (Γ : Vec Sort γ)
        (P : PartSet)
        (Pr : Proc γ δ)
        (x : State δ)
      → Dec (Γ ⊢a P ◂ Pr ∶ at x)
    alg? Γ P Pr x = decide (memo (at? x))
      where
        decide : Decidable (at x) → Dec (Γ ⊢a P ◂ Pr ∶ at x)
        decide 𝒮? = answer (Probing.probe P (env P) Γ Pr (at x) 𝒮?)
          where
            answer : Probe Γ P Pr (at x) → Dec (Γ ⊢a P ◂ Pr ∶ at x)
            answer r with ⊆? 𝒮? (hit? r)
            ... | yes sub = yes (from-hit r sub (x , refl))
            ... | no ¬sub = no λ d → ¬sub λ x∈ → into-hit r d (x∈ , x∈)
