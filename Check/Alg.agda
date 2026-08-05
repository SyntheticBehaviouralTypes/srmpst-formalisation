{-# OPTIONS --guardedness #-}

-- Deciding the *algorithmic* judgment `_&_⊢a_∶_` (TODO.md, "Deciding the
-- algorithmic judgment ⊢a").  `Check/Decide.agda` decides the declarative
-- `_&_⊢p_∶_` directly and pays for it: `t/skip`/`t/unskip` may wrap any
-- process, so a `no` has to rule out every state the derivation could have
-- been anchored at.  `⊢a` has one constructor per process form and the
-- anchors survive only inside the `⊢blocked` leaves, so the anchor is never
-- in question.  `Dec (⊢p)` then falls out of `alg/typing`/`norm` in four
-- lines (Step 4) with no bespoke completeness argument.
--
-- Deliberately a NEW file rather than more code inside `Check/Decide.agda`:
-- that file has open interaction metas, so Agda writes no interface for it
-- and every edit re-checks it from source.  What this file needs from it is
-- `size/proc`, `remaining`/`mark`/`mark-decreases` and the `×-Lex` measure,
-- which `Check/Decide.agda`'s own "Refactor TODO" already says belong in a
-- module of their own; they are carried here, and TODO.md Step 5 removes
-- the originals along with the rest of the corpse.
--
-- ══════════════════════════════════════════════════════════════════════
--  Step 0 — inventory
-- ══════════════════════════════════════════════════════════════════════
--
-- Already available, used unchanged:
--
--   `Check/Core.agda`, `GraphChecker`
--     messageGuarded?  na?  bisim?~
--     findStep                          — a step with a *fully known* action
--     findRecv / matchRecv? / MatchRecv — an edge `P ⟶ Q # j < U >` for
--                                         *some* `j`, `U`
--     checkExpression                   — `Γ ⊢e E ∶ S` in checking mode
--   `Definitions/Graph/Reachability.agda`
--     reachVia?   ∈T?   PathVia
--   `Definitions/Typing/Algorithmic.agda`
--     the judgment itself, and `alg/typing` (soundness half of Step 4)
--   `Definitions/Typing/Norm.agda`
--     `norm` (completeness half of Step 4)
--
-- Gaps, all filled below:
--
--   reach¬P?     `Dec (a -[¬ P ]->* b)`.  `reachVia?` decides reachability
--                *in a graph*, so the `¬P` restriction is materialised as a
--                graph (`restrict`) and paths translated back and forth.
--                (Restored from the block `Check/Decide.agda` carries
--                commented out.)
--   reachBisim?  `Dec (∃[ H ] a -[¬ P ]->* H × H ~ b)` — `blocked/var`
--                verbatim, with the *known* state `a = lu Δ X` on the left.
--                One reachability row plus one `~` test per candidate; no
--                search over anchors.
--   anyBisim?    `Dec (∃[ X ] lu Ξ X ~ t)` — `skip/cycle`'s first premise.
--   findSendStep `findStep` with the label `i` fixed but the sort `U` still
--                to be read off the graph: `blocked/send` names its label,
--                `blocked/recv` quantifies over it.
--   size/lookup  `size/proc (lu Br j) ≤ size/branches Br`, so the
--                per-branch recursion of `blocked/recv` has a measure.
--   _≺₃_         a *three*-component measure — see "Measure" below.

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
  renaming (_≟_ to _≟Fin_; zero to fzero; suc to fsuc)
import Data.Fin.Properties as FinP
open import Data.List using (List; []; _∷_; filter)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as MemP
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
import Data.Nat.Properties as Nat
open import Data.Product
  using (_×_; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Lex.Strict
  using (×-Lex; ×-wellFounded)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec
  using (Vec; []; _∷_; lookup; countᵇ; _[_]≔_; replicate)
  renaming (map to vmap)
import Data.Vec.Properties as VecP
open import Function using (_∘_)
open import Induction.WellFounded using (WellFounded)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (map′; _×-dec_)

open import Definitions.Behav using (BTheory; WellBehaved)
open import Definitions.Expr
open import Check.Core
import Definitions.Typing as Typing
import Definitions.Typing.Algorithmic
import Definitions.Typing.Norm

module Check.Alg (N : ℕ) where

  open Processes N using (module GraphChecker)
  open import Definitions.Graph.Core N
    renaming (_-<_>->_ to GStep)
  open import Definitions.Graph.Reachability N
    using (PathVia; path/nil; path/cons; reachVia?; ∈T?)

  module AlgCheck
    (G : Graph)
    (wb : WellBehaved (graphTheory G))
    where

    open Typing.MPST wb
    open GraphChecker G wb
      using ( messageGuarded?; matchRecv?; MatchRecv
            ; findStep; findRecv; RecvWitness
            ; na?; bisim?~ )

    module A = Definitions.Typing.Algorithmic {N} {graphTheory G} wb
    open A
      using ( _&_⊢a_∶_; _&_⊢blocked_∶_
            ; a/skip; a/if; a/end
            ; blocked/send; blocked/recv; blocked/var; blocked/rec
            ; alg/typing )

    module NM = Definitions.Typing.Norm {N} {graphTheory G} wb

    private
      variable
        γ δ ξ : ℕ

    -- ══════════════════════════════════════════════════════════════════
    --  `¬P`-reachability, via `reachVia?` on the `P`-free restriction
    -- ══════════════════════════════════════════════════════════════════

    restrict : Part → Graph
    restrict P =
      graph (size G) (vmap (filter (λ e → P ∉α? proj₁ e)) (outgoing G))

    redges≡ :
      ∀ P s
      → edges (restrict P) s ≡ filter (λ e → P ∉α? proj₁ e) (edges G s)
    redges≡ P s = VecP.lookup-map s _ (outgoing G)

    rstep⇒ :
      ∀ {P s α t}
      → GStep {restrict P} s α t
      → (s -< α >-> t) × P ∉α α
    rstep⇒ {P} {s} {α} {t} gr
      with MemP.∈-filter⁻ (λ e → P ∉α? proj₁ e)
             (subst ((α , t) ∈_) (redges≡ P s)
               (step⇒listed {restrict P} gr))
    ... | mem , P∉α = listed⇒step {G = G} mem , P∉α

    rstep⇐ :
      ∀ {P s α t}
      → s -< α >-> t
      → P ∉α α
      → GStep {restrict P} s α t
    rstep⇐ {P} {s} {α} {t} gr P∉α =
      listed⇒step {G = restrict P}
        (subst ((α , t) ∈_) (sym (redges≡ P s))
          (MemP.∈-filter⁺ (λ e → P ∉α? proj₁ e)
            (step⇒listed {G = G} gr) P∉α))

    path→tr :
      ∀ {P a b n}
      → PathVia (restrict P) (λ _ → true) a b n
      → a -[¬ P ]->* b
    path→tr path/nil = skip/refl
    path→tr (path/cons _ gr rest) =
      let gr′ , P∉α = rstep⇒ gr
      in tr¬/step gr′ P∉α (path→tr rest)

    tr→path :
      ∀ {P a b}
      → a -[¬ P ]->* b
      → ∃[ n ] PathVia (restrict P) (λ _ → true) a b n
    tr→path ([] , tr/refl , []) = zero , path/nil
    tr→path (_ ∷ αs , tr/step gr tr , P∉α ∷ ps)
      with tr→path (αs , tr , ps)
    ... | n , rest = suc n , path/cons _ (rstep⇐ gr P∉α) rest

    reach¬P? : ∀ P a b → Dec (a -[¬ P ]->* b)
    reach¬P? P a b =
      map′ (λ { (_ , p) → path→tr p }) tr→path
        (reachVia? (restrict P) (λ _ → true) a b)

    -- `blocked/var` verbatim: the source is `lu Δ X`, i.e. *known*, so this
    -- is one reachability query per candidate `H` followed by one `~` test
    -- — not a search over anchors.  (That is exactly why the rule is
    -- oriented reach-then-`~`.)
    reachBisim? :
      ∀ P (a s : State G) → Dec (∃[ H ] (a -[¬ P ]->* H) × (H ~ s))
    reachBisim? P a s =
      FinP.any? (λ H → reach¬P? P a H ×-dec bisim?~ H s)

    -- `skip/cycle`'s premise.  Note this is `~`, not literal membership:
    -- the search's own `visited` bit-vector tracks literal revisits (for
    -- termination), whereas closing a tree is allowed up to `~`.
    anyBisim? :
      ∀ {ξ} (Ξ : Vec (State G) ξ) (t : State G)
      → Dec (∃[ X ] lookup Ξ X ~ t)
    anyBisim? [] t = no λ { (() , _) }
    anyBisim? (u ∷ Ξ) t with bisim?~ u t
    ... | yes u~t = yes (fzero , u~t)
    ... | no ¬u~t with anyBisim? Ξ t
    ...   | yes (X , u~t) = yes (fsuc X , u~t)
    ...   | no ¬rest =
      no λ { (fzero , u~t) → ¬u~t u~t
           ; (fsuc X , u~t) → ¬rest (X , u~t) }

    -- ══════════════════════════════════════════════════════════════════
    --  Finding a send edge: the label is given, the sort is not
    -- ══════════════════════════════════════════════════════════════════

    MatchSend : Part → Part → (I : ℕ) → Fin (suc I) → Action → Set
    MatchSend P Q I i α =
      Σ[ U ∈ Sort ] α ≡ (P ⟶ Q # i < U >)

    matchSend? :
      ∀ P Q I (i : Fin (suc I)) α → Dec (MatchSend P Q I i α)
    matchSend? P Q I i ((R ⟶ S) # (_<_> {nchoices = J} j U))
      with R ≟Fin P | S ≟Fin Q | J Nat.≟ I
    ... | yes refl | yes refl | yes refl with j ≟Fin i
    ...   | yes refl = yes (U , refl)
    ...   | no j≢i = no λ { (_ , refl) → j≢i refl }
    matchSend? P Q I i ((R ⟶ S) # (_<_> {nchoices = J} j U))
      | no R≢P | _ | _ = no λ { (_ , refl) → R≢P refl }
    matchSend? P Q I i ((R ⟶ S) # (_<_> {nchoices = J} j U))
      | _ | no S≢Q | _ = no λ { (_ , refl) → S≢Q refl }
    matchSend? P Q I i ((R ⟶ S) # (_<_> {nchoices = J} j U))
      | _ | _ | no J≢I = no λ { (_ , refl) → J≢I refl }

    SendWitness :
      Part → Part → (I : ℕ) → Fin (suc I) → List (Edge (size G)) → Set
    SendWitness P Q I i xs =
      Σ[ U ∈ Sort ] Σ[ t ∈ State G ] ((P ⟶ Q # i < U >) , t) ∈ xs

    findSend :
      ∀ P Q I (i : Fin (suc I)) (xs : List (Edge (size G)))
      → Dec (SendWitness P Q I i xs)
    findSend P Q I i [] = no λ { (_ , _ , ()) }
    findSend P Q I i ((α , t) ∷ xs) with matchSend? P Q I i α
    ... | yes (U , refl) = yes (U , t , Any.here refl)
    ... | no ¬match with findSend P Q I i xs
    ...   | yes (U , u , member) = yes (U , u , Any.there member)
    ...   | no ¬rest =
      no λ { (U , _ , Any.here px) → ¬match (U , sym (cong proj₁ px))
           ; (U , u , Any.there m) → ¬rest (U , u , m) }

    findSendStep :
      ∀ (s : State G) P Q I (i : Fin (suc I))
      → Dec (Σ[ U ∈ Sort ] Σ[ t ∈ State G ] s -< P ⟶ Q # i < U > >-> t)
    findSendStep s P Q I i with findSend P Q I i (edges G s)
    ... | yes (U , t , mem) = yes (U , t , listed⇒step {G = G} mem)
    ... | no ¬found =
      no λ { (U , t , gr) → ¬found (U , t , step⇒listed {G = G} gr) }

    -- ══════════════════════════════════════════════════════════════════
    --  Measure  (carried from `Check/Decide.agda`, plus a third component)
    -- ══════════════════════════════════════════════════════════════════

    size/proc : ∀ {γ δ} → Proc γ δ → ℕ
    size/branches : ∀ {γ δ I} → Vec (Proc γ δ) I → ℕ

    size/proc (_ ! _ < _ >∙ Pr)        = suc (size/proc Pr)
    size/proc (Σ _ ？[ _ ]· Br)        = suc (size/branches Br)
    size/proc (ifp _ then Pr else Pr′) = suc (size/proc Pr + size/proc Pr′)
    size/proc (rec Pr)                 = suc (size/proc Pr)
    size/proc (v _)                    = 0
    size/proc ∅                        = 0

    size/branches []         = 0
    size/branches (Pr ∷ Prs) = size/proc Pr + size/branches Prs

    size/lookup :
      ∀ {γ δ I} (Br : Vec (Proc γ δ) I) (j : Fin I)
      → size/proc (lookup Br j) ≤ size/branches Br
    size/lookup (Pr ∷ Br) fzero = Nat.m≤m+n _ _
    size/lookup (Pr ∷ Br) (fsuc j) =
      Nat.≤-trans (size/lookup Br j) (Nat.m≤n+m _ _)

    remaining : Vec Bool (size G) → ℕ
    remaining marks = size G ∸ countᵇ (λ b → b) marks

    mark : State G → Vec Bool (size G) → Vec Bool (size G)
    mark r marks = marks [ r ]≔ true

    private
      count-update-true :
        ∀ {n} (marks : Vec Bool n) (r : Fin n) → lookup marks r ≡ false
        → countᵇ (λ b → b) (marks [ r ]≔ true) ≡ suc (countᵇ (λ b → b) marks)
      count-update-true (false ∷ marks) fzero refl = refl
      count-update-true (true ∷ marks) (fsuc r) eq =
        cong suc (count-update-true marks r eq)
      count-update-true (false ∷ marks) (fsuc r) eq =
        count-update-true marks r eq

      count-lt-n :
        ∀ {n} (marks : Vec Bool n) (r : Fin n) → lookup marks r ≡ false
        → countᵇ (λ b → b) marks < n
      count-lt-n (false ∷ marks) fzero refl = s≤s (count≤n marks)
        where
        count≤n : ∀ {n} (marks : Vec Bool n) → countᵇ (λ b → b) marks ≤ n
        count≤n [] = z≤n
        count≤n (true ∷ marks) = s≤s (count≤n marks)
        count≤n (false ∷ marks) = Nat.m≤n⇒m≤1+n (count≤n marks)
      count-lt-n (true ∷ marks) (fsuc r) eq =
        s≤s (count-lt-n marks r eq)
      count-lt-n (false ∷ marks) (fsuc r) eq =
        Nat.m≤n⇒m≤1+n (count-lt-n marks r eq)

      count-replicate-false :
        ∀ n → countᵇ (λ b → b) (replicate n false) ≡ 0
      count-replicate-false zero = refl
      count-replicate-false (suc n) = count-replicate-false n

    mark-decreases :
      ∀ (marks : Vec Bool (size G)) (r : State G) → lookup marks r ≡ false
      → remaining (mark r marks) < remaining marks
    mark-decreases marks r eq
      rewrite count-update-true marks r eq =
      Nat.∸-monoʳ-< (Nat.n<1+n _) (count-lt-n marks r eq)

    empty : Vec Bool (size G)
    empty = replicate (size G) false

    remaining-empty : remaining empty ≡ size G
    remaining-empty = cong (size G ∸_) (count-replicate-false (size G))

    lookup-empty : ∀ r → lookup empty r ≡ false
    lookup-empty r = VecP.lookup-replicate r false

    -- The four components, largest first:
    --
    --   1. `size/proc Pr`   — strictly drops under an action, into an `if`
    --                         branch, and into a `rec` body.  Every call
    --                         that changes the process decreases it.
    --   2. the *regime*     — 1 while the search is in the `P ∈T` region,
    --                         0 in the `¬ P ∈T` region.  The region is
    --                         closed under successors, so the search only
    --                         ever crosses 1 → 0, never back; crossing
    --                         lets the visited set be reset (see
    --                         `treeA?`/`treeB?` below).
    --   3. `remaining v`    — strictly drops on every `skip/step`, because
    --                         the current state is marked before recursing.
    --   4. the *phase*      — which of the mutually recursive functions we
    --                         are in.  Nothing about the algorithm needs
    --                         it; it is there so that *every* call in the
    --                         group strictly decreases the `Acc` argument.
    --                         Handing an unchanged `ac` on to the next
    --                         function is what defeats Agda's termination
    --                         checker here: reconstructing `acc rs` (which
    --                         is also all `ac@(acc rs)` gives you) reads as
    --                         a constructor application, not as the
    --                         original argument, so a cycle whose only
    --                         decrease sits in a *different* function can
    --                         no longer be composed.  With a phase there
    --                         are no `=` edges left to compose: the three
    --                         list recursions (`treeAs?`/`treeBs?`/
    --                         `recvConts?`) pass `ac` untouched and shrink
    --                         their list instead, and every other call
    --                         passes `rs …`.
    Measure : Set
    Measure = ℕ × ℕ × ℕ × ℕ

    _≺_ : Measure → Measure → Set
    _≺_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_))

    ≺-wellFounded : WellFounded _≺_
    ≺-wellFounded =
      ×-wellFounded <-wellFounded
        (×-wellFounded <-wellFounded
          (×-wellFounded <-wellFounded <-wellFounded))

    private
      ≺proc :
        ∀ {a a′ b b′ c c′ d d′} → a < a′ → (a , b , c , d) ≺ (a′ , b′ , c′ , d′)
      ≺proc lt = inj₁ lt

      ≺regime :
        ∀ {a b b′ c c′ d d′} → b < b′ → (a , b , c , d) ≺ (a , b′ , c′ , d′)
      ≺regime lt = inj₂ (refl , inj₁ lt)

      ≺visit :
        ∀ {a b c c′ d d′} → c < c′ → (a , b , c , d) ≺ (a , b , c′ , d′)
      ≺visit lt = inj₂ (refl , inj₂ (refl , inj₁ lt))

      ≺phase :
        ∀ {a b c d d′} → d < d′ → (a , b , c , d) ≺ (a , b , c , d′)
      ≺phase lt = inj₂ (refl , inj₂ (refl , inj₂ (refl , lt)))

      0<1 : 0 < 1
      0<1 = s≤s z≤n
      1<2 : 1 < 2
      1<2 = s≤s (s≤s z≤n)
      2<3 : 2 < 3
      2<3 = s≤s (s≤s (s≤s z≤n))
      2<4 : 2 < 4
      2<4 = s≤s (s≤s (s≤s z≤n))
      3<4 : 3 < 4
      3<4 = s≤s (s≤s (s≤s (s≤s z≤n)))
      4<6 : 4 < 6
      4<6 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
      5<6 : 5 < 6
      5<6 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

    mark-mono :
      ∀ (bv : Vec Bool (size G)) (t u : State G)
      → T (lookup bv u) → T (lookup (mark t bv) u)
    mark-mono bv t u u∈v with u ≟Fin t
    ... | yes refl = subst T (sym (VecP.lookup∘update t bv true)) tt
    ... | no u≢t = subst T (sym (VecP.lookup∘update′ u≢t bv true)) u∈v

    mark-here : ∀ (bv : Vec Bool (size G)) (t : State G) → T (lookup (mark t bv) t)
    mark-here bv t = subst T (sym (VecP.lookup∘update t bv true)) tt

    mark-there :
      ∀ {bv : Vec Bool (size G)} {t u : State G}
      → u ≢ t → T (lookup (mark t bv) u) → T (lookup bv u)
    mark-there {bv} u≢t u∈ = subst T (VecP.lookup∘update′ u≢t bv true) u∈

    -- ══════════════════════════════════════════════════════════════════
    --  Is there *any* outgoing edge?  (`skip/step`'s `gr` premise)
    -- ══════════════════════════════════════════════════════════════════

    anyStep? : ∀ (s : State G) → Dec (∃[ α ] ∃[ u ] s -< α >-> u)
    anyStep? s = go (edges G s) refl
      where
      ¬∈[] : ∀ {A : Set} {x : A} → x ∈ [] → ⊥
      ¬∈[] ()

      go :
        (es : List (Edge (size G))) → edges G s ≡ es
        → Dec (∃[ α ] ∃[ u ] s -< α >-> u)
      go [] eq =
        no λ { (α , u , gr) →
                 ¬∈[] (subst ((α , u) ∈_) eq (step⇒listed {G = G} gr)) }
      go ((α , u) ∷ es) eq =
        yes (α , u ,
             listed⇒step {G = G}
               (subst ((α , u) ∈_) (sym eq) (Any.here refl)))

    -- ══════════════════════════════════════════════════════════════════
    --  Shapes the search returns
    -- ══════════════════════════════════════════════════════════════════

    Tree :
      ∀ {γ δ ξ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (Ξ : Vec (State G) ξ)
        (P : Part) (Pr : Proc γ δ) (s : State G) → Set
    Tree Γ Δ Ξ P Pr s = (Γ & Δ ⊢blocked_∶_) & Ξ ⊢skip P ◂ Pr ∶ s

    -- ── the `¬ P ∈T` regime: why a *table* is needed there and nowhere ──
    --
    -- The region `¬ P ∈T s` is closed under successors (`in/later`), and
    -- inside it `skip/cycle` is unusable (it demands `P ∈T`).  So a tree
    -- there is a finite, entirely `skip/main`-terminated object, and — the
    -- point — it does not depend on `Ξ` at all.  Which is just as well,
    -- because that is also the one place where the search cannot answer a
    -- revisit positively: in the `P ∈T` regime a literal revisit closes the
    -- tree with `skip/cycle`, here it must fail, and refuting it needs the
    -- whole exploration, not the current path.
    --
    -- `Justified bv r` is the failure operator's step at `r`, read off the
    -- three constructors: no leaf here, no cycle available here, and the
    -- `skip/step` premise is unavailable *or* one successor is itself in
    -- `bv`.  A `bv` closed under it is a post-fixed point of failure, hence
    -- contained in the complement of "has a tree" — and that containment is
    -- proved by plain structural recursion on the tree (`failed⇒¬tree`),
    -- with no fixed-point machinery.
    --
    -- `FailedFrom stack bv` weakens this to allow *deferred* entries: the
    -- states currently on the DFS stack are marked before their own
    -- justification exists (that is what makes the measure decrease), and
    -- each is discharged by its own frame as the recursion unwinds.  At the
    -- top the stack is `empty`, so `FailedFrom empty bv` is closure proper.
    Justified :
      ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
        (P : Part) (Pr : Proc γ δ)
      → Vec Bool (size G) → State G → Set
    Justified Γ Δ P Pr bv r =
      (¬ P ∈T r)
      × (¬ (Γ & Δ ⊢blocked P ◂ Pr ∶ r))
      × ( (¬ (P not-active-in r))
        ⊎ (¬ (∃[ α ] ∃[ u ] r -< α >-> u))
        ⊎ (∃[ α ] ∃[ u ] (r -< α >-> u) × T (lookup bv u)) )

    FailedFrom :
      ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
        (P : Part) (Pr : Proc γ δ)
      → Vec Bool (size G) → Vec Bool (size G) → Set
    FailedFrom Γ Δ P Pr stack bv =
      ∀ r → T (lookup bv r) → T (lookup stack r) ⊎ Justified Γ Δ P Pr bv r

    just-mono :
      ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {P : Part} {Pr : Proc γ δ} {bv : Vec Bool (size G)}
        (t : State G) {r : State G}
      → Justified Γ Δ P Pr bv r → Justified Γ Δ P Pr (mark t bv) r
    just-mono t (¬inT , ¬bl , inj₁ x) = ¬inT , ¬bl , inj₁ x
    just-mono t (¬inT , ¬bl , inj₂ (inj₁ x)) = ¬inT , ¬bl , inj₂ (inj₁ x)
    just-mono {bv = bv} t (¬inT , ¬bl , inj₂ (inj₂ (α , u , gr , u∈v))) =
      ¬inT , ¬bl , inj₂ (inj₂ (α , u , gr , mark-mono bv t u u∈v))

    failed⇒¬tree :
      ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
        {P : Part} {Pr : Proc γ δ} {bv : Vec Bool (size G)}
      → FailedFrom Γ Δ P Pr empty bv
      → ∀ {r} → T (lookup bv r)
      → ∀ {ξ} {Ξ : Vec (State G) ξ}
      → ¬ Tree Γ Δ Ξ P Pr r
    failed⇒¬tree {bv = bv} ff {r} r∈v (skip/main bl) with ff r r∈v
    ... | inj₁ r∈∅ = ⊥-elim (subst T (lookup-empty r) r∈∅)
    ... | inj₂ (_ , ¬bl , _) = ¬bl bl
    failed⇒¬tree {bv = bv} ff {r} r∈v (skip/cycle eq inT) with ff r r∈v
    ... | inj₁ r∈∅ = ⊥-elim (subst T (lookup-empty r) r∈∅)
    ... | inj₂ (¬inT , _ , _) = ¬inT inT
    failed⇒¬tree {bv = bv} ff {r} r∈v (skip/step gr na ktd) with ff r r∈v
    ... | inj₁ r∈∅ = ⊥-elim (subst T (lookup-empty r) r∈∅)
    ... | inj₂ (_ , _ , inj₁ ¬na) = ¬na na
    ... | inj₂ (_ , _ , inj₂ (inj₁ ¬st)) = ¬st (_ , _ , gr)
    ... | inj₂ (_ , _ , inj₂ (inj₂ (α , u , gr′ , u∈v))) =
      failed⇒¬tree {bv = bv} ff u∈v (ktd gr′)

    TreeB :
      ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
        (P : Part) (Pr : Proc γ δ)
        (s : State G) (stack : Vec Bool (size G)) → Set
    TreeB Γ Δ P Pr s stack =
      (∀ {ξ} (Ξ : Vec (State G) ξ) → Tree Γ Δ Ξ P Pr s)
      ⊎ (Σ[ bv ∈ Vec Bool (size G) ]
           T (lookup bv s) × FailedFrom Γ Δ P Pr stack bv)

    TreeBs :
      ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
        (P : Part) (Pr : Proc γ δ)
        (es : List (Edge (size G))) (stack : Vec Bool (size G)) → Set
    TreeBs Γ Δ P Pr es stack =
      All (λ e → ∀ {ξ} (Ξ : Vec (State G) ξ) → Tree Γ Δ Ξ P Pr (proj₂ e)) es
      ⊎ (Σ[ bv ∈ Vec Bool (size G) ] Σ[ α ∈ Action ] Σ[ u ∈ State G ]
           ((α , u) ∈ es) × T (lookup bv u) × FailedFrom Γ Δ P Pr stack bv)

    -- `visited` is the DFS path; `Ξ` is the same set as a vector.  Keeping
    -- the correspondence explicit is what lets the `P ∈T` search treat a
    -- literal revisit as `skip/cycle` without a separate case.
    Covers :
      ∀ {ξ} (Ξ : Vec (State G) ξ) (visited : Vec Bool (size G)) → Set
    Covers Ξ visited =
      ∀ r → T (lookup visited r) → ∃[ X ] lookup Ξ X ≡ r

    covers-empty : Covers [] empty
    covers-empty r r∈ = ⊥-elim (subst T (lookup-empty r) r∈)

    covers-∷ :
      ∀ {ξ} {Ξ : Vec (State G) ξ} {visited} (s : State G)
      → Covers Ξ visited → Covers (s ∷ Ξ) (mark s visited)
    covers-∷ {visited = visited} s cov r r∈ with r ≟Fin s
    ... | yes refl = fzero , refl
    ... | no r≢s with cov r (mark-there {bv = visited} {t = s} r≢s r∈)
    ...   | X , eq = fsuc X , eq

    -- ══════════════════════════════════════════════════════════════════
    --  Continuations of a `blocked/recv`, one per outgoing edge
    -- ══════════════════════════════════════════════════════════════════

    RecvCont :
      ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
        (Q P : Part) (I : ℕ) (Br : Vec (Proc (suc γ) δ) (suc I))
      → Edge (size G) → Set
    RecvCont Γ Δ Q P I Br e =
      ∀ {j : Fin (suc I)} {U}
      → proj₁ e ≡ (Q ⟶ P # j < U >)
      → (U ∷ Γ) & Δ ⊢a P ◂ lookup Br j ∶ proj₂ e

    -- ══════════════════════════════════════════════════════════════════
    --  The checker
    -- ══════════════════════════════════════════════════════════════════

    mutual

      -- Step 3.  Syntax-directed on `Pr`, except that `a/skip` is available
      -- for *every* process form: for `∅` and `ifp` there is no `⊢blocked`
      -- constructor, so such a tree can only be closed by `skip/cycle`
      -- throughout — degenerate, but a legal `⊢a` derivation, so a `no`
      -- has to rule it out too.                                 [phase 6]
      alg? :
        ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
          (P : Part) (Pr : Proc γ δ) (s : State G)
        → Acc _≺_ (size/proc Pr , 1 , remaining empty , 6)
        → Dec (Γ & Δ ⊢a P ◂ Pr ∶ s)

      --                                                          [phase 5]
      ifPrems? :
        ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (P : Part)
          (E : Exp γ) (Prl Prr : Proc γ δ) (s : State G)
        → Acc _≺_ (suc (size/proc Prl + size/proc Prr) , 1 , remaining empty , 5)
        → Dec ((Γ ⊢e E ∶ s/bool)
               × (Γ & Δ ⊢a P ◂ Prl ∶ s)
               × (Γ & Δ ⊢a P ◂ Prr ∶ s))

      -- Step 1.  All four leaf forms, at a FIXED state.  Only
      -- `blocked/rec` searches, and only over anchors.           [phase 2]
      blocked? :
        ∀ {γ δ m₁ m₂} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
          (P : Part) (Pr : Proc γ δ) (s : State G)
        → Acc _≺_ (size/proc Pr , m₁ , m₂ , 2)
        → Dec (Γ & Δ ⊢blocked P ◂ Pr ∶ s)

      --                                                          [phase 1]
      recvConts? :
        ∀ {γ δ m₁ m₂ I} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
          (Q P : Part) (Br : Vec (Proc (suc γ) δ) (suc I))
          (es : List (Edge (size G)))
        → Acc _≺_ (suc (size/branches Br) , m₁ , m₂ , 1)
        → Dec (All (RecvCont Γ Δ Q P I Br) es)

      -- Step 2.  The forward search, split by regime.            [phase 4]
      tree? :
        ∀ {γ δ ξ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (Ξ : Vec (State G) ξ)
          (P : Part) (Pr : Proc γ δ) (s : State G)
          (visited : Vec Bool (size G))
        → Covers Ξ visited
        → Acc _≺_ (size/proc Pr , 1 , remaining visited , 4)
        → Dec (Tree Γ Δ Ξ P Pr s)

      --                                                          [phase 3]
      treeA? :
        ∀ {γ δ ξ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (Ξ : Vec (State G) ξ)
          (P : Part) (Pr : Proc γ δ) (s : State G)
        → P ∈T s
        → (visited : Vec Bool (size G))
        → Covers Ξ visited
        → Acc _≺_ (size/proc Pr , 1 , remaining visited , 3)
        → Dec (Tree Γ Δ Ξ P Pr s)

      --                                                          [phase 6]
      treeAs? :
        ∀ {γ δ ξ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ) (Ξ : Vec (State G) ξ)
          (P : Part) (Pr : Proc γ δ) (es : List (Edge (size G)))
          (visited : Vec Bool (size G))
        → Covers Ξ visited
        → Acc _≺_ (size/proc Pr , 1 , remaining visited , 6)
        → Dec (All (λ e → Tree Γ Δ Ξ P Pr (proj₂ e)) es)

      --                                                          [phase 4]
      treeB? :
        ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
          (P : Part) (Pr : Proc γ δ) (s : State G)
        → ¬ P ∈T s
        → (stack : Vec Bool (size G))
        → Acc _≺_ (size/proc Pr , 0 , remaining stack , 4)
        → TreeB Γ Δ P Pr s stack

      --                                                          [phase 6]
      treeBs? :
        ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
          (P : Part) (Pr : Proc γ δ) (es : List (Edge (size G)))
        → (∀ {e} → e ∈ es → ¬ P ∈T proj₂ e)
        → (stack : Vec Bool (size G))
        → Acc _≺_ (size/proc Pr , 0 , remaining stack , 6)
        → TreeBs Γ Δ P Pr es stack

      -- ── alg? ────────────────────────────────────────────────────────

      alg? Γ Δ P ∅ s (acc rs) with ∈T? G P s
      ... | no P∉s = yes (a/end P∉s)
      ... | yes P∈s
        with tree? Γ Δ [] P ∅ s empty covers-empty (rs (≺phase 4<6))
      ...   | yes std = yes (a/skip std)
      ...   | no ¬std =
        no λ { (a/skip std) → ¬std std
             ; (a/end done) → done P∈s }

      alg? Γ Δ P (ifp E then Prl else Prr) s (acc rs)
        with ifPrems? Γ Δ P E Prl Prr s (rs (≺phase 5<6))
      ... | yes (etd , ttd , ftd) = yes (a/if etd ttd ftd)
      ... | no ¬prems
        with tree? Γ Δ [] P (ifp E then Prl else Prr) s empty covers-empty
               (rs (≺phase 4<6))
      ...   | yes std = yes (a/skip std)
      ...   | no ¬std =
        no λ { (a/skip std) → ¬std std
             ; (a/if etd ttd ftd) → ¬prems (etd , ttd , ftd) }

      alg? Γ Δ P (Q ! i < E >∙ Pr) s (acc rs)
        with tree? Γ Δ [] P (Q ! i < E >∙ Pr) s empty covers-empty
               (rs (≺phase 4<6))
      ... | yes std = yes (a/skip std)
      ... | no ¬std = no λ { (a/skip std) → ¬std std }

      alg? Γ Δ P (Σ Q ？[ S ]· Br) s (acc rs)
        with tree? Γ Δ [] P (Σ Q ？[ S ]· Br) s empty covers-empty
               (rs (≺phase 4<6))
      ... | yes std = yes (a/skip std)
      ... | no ¬std = no λ { (a/skip std) → ¬std std }

      alg? Γ Δ P (rec Pr) s (acc rs)
        with tree? Γ Δ [] P (rec Pr) s empty covers-empty (rs (≺phase 4<6))
      ... | yes std = yes (a/skip std)
      ... | no ¬std = no λ { (a/skip std) → ¬std std }

      alg? Γ Δ P (v X) s (acc rs)
        with tree? Γ Δ [] P (v X) s empty covers-empty (rs (≺phase 4<6))
      ... | yes std = yes (a/skip std)
      ... | no ¬std = no λ { (a/skip std) → ¬std std }

      ifPrems? Γ Δ P E Prl Prr s (acc rs) with checkExpression Γ E s/bool
      ... | no ¬etd = no λ { (etd , _ , _) → ¬etd etd }
      ... | yes etd
        with alg? Γ Δ P Prl s (rs (≺proc (s≤s (Nat.m≤m+n _ _))))
      ...   | no ¬ttd = no λ { (_ , ttd , _) → ¬ttd ttd }
      ...   | yes ttd
        with alg? Γ Δ P Prr s (rs (≺proc (s≤s (Nat.m≤n+m _ _))))
      ...     | no ¬ftd = no λ { (_ , _ , ftd) → ¬ftd ftd }
      ...     | yes ftd = yes (etd , ttd , ftd)

      -- ── blocked? ────────────────────────────────────────────────────

      blocked? Γ Δ P ∅ s ac = no λ ()
      blocked? Γ Δ P (ifp _ then _ else _) s ac = no λ ()

      blocked? Γ Δ P (v X) s ac with reachBisim? P (lookup Δ X) s
      ... | yes (H , tr , H~s) = yes (blocked/var tr H~s)
      ... | no ¬f = no λ { (blocked/var tr H~s) → ¬f (_ , tr , H~s) }

      blocked? Γ Δ P (Q ! i < E >∙ Pr) s (acc rs)
        with findSendStep s P Q _ i
      ... | no ¬f = no λ { (blocked/send gr etd td) → ¬f (_ , _ , gr) }
      ... | yes (U , t , gr) with checkExpression Γ E U
      ...   | no ¬wt =
        no λ { (blocked/send gr′ etd td) →
                 ¬wt (subst (Γ ⊢e E ∶_) (step-sort-deterministic gr′ gr) etd) }
      ...   | yes etd
        with alg? Γ Δ P Pr t (rs (≺proc (Nat.n<1+n _)))
      ...     | yes td = yes (blocked/send gr etd td)
      ...     | no ¬td =
        no λ { (blocked/send {G′ = G′} gr′ etd′ td′) →
                 ¬td (subst (λ z → Γ & Δ ⊢a P ◂ Pr ∶ z)
                        (step-deterministic
                          (subst (λ z → s -< P ⟶ Q # i < z > >-> G′)
                            (step-sort-deterministic gr′ gr) gr′)
                          gr)
                        td′) }

      blocked? Γ Δ P (Σ Q ？[ S ]· Br) s (acc rs)
        with findRecv Q P _ (edges G s)
      ... | no ¬f =
        no λ { (blocked/recv gr conts) →
                 ¬f (_ , _ , _ , step⇒listed {G = G} gr) }
      ... | yes (j₀ , U₀ , t₀ , mem₀)
        with recvConts? Γ Δ Q P Br (edges G s) (rs (≺phase 1<2))
      ...   | yes conts =
        yes (blocked/recv (listed⇒step {G = G} mem₀)
              (λ gr′ → All.lookup conts (step⇒listed {G = G} gr′) refl))
      ...   | no ¬conts =
        no λ { (blocked/recv gr conts) →
                 ¬conts
                   (All.tabulate
                     (λ { {α , t} mem {j} {U} eq →
                            conts (subst (λ z → s -< z >-> t) eq
                                     (listed⇒step {G = G} mem)) })) }

      -- The one genuine search, and it is bounded and local: a finite list
      -- of candidate anchors `W`, each with a decidable `¬P`-reachability
      -- query and a body decision at a strictly smaller `size/proc`.  Do
      -- NOT try to pick a canonical `W` — that is the anchor-moving idea,
      -- and it is refuted (`Stale/PushRecDerivations.agda.stale`, `Ex6`).
      blocked? Γ Δ P (rec Pr) s (acc rs) with messageGuarded? Pr
      ... | no ¬mg = no λ { (blocked/rec tr mg td) → ¬mg mg }
      ... | yes mg
        with FinP.any?
               (λ W → reach¬P? P W s
                      ×-dec alg? Γ (W ∷ Δ) P Pr W (rs (≺proc (Nat.n<1+n _))))
      ...   | yes (W , tr , td) = yes (blocked/rec tr mg td)
      ...   | no ¬anchor =
        no λ { (blocked/rec tr mg′ td) → ¬anchor (_ , tr , td) }

      -- The tail is decided *first* so that the recursive call can pass
      -- `ac` untouched; only the head's `alg?` consumes the `Acc`.
      recvConts? Γ Δ Q P Br [] ac = yes []
      recvConts? {I = I} Γ Δ Q P Br ((α , t) ∷ es) ac
        with recvConts? Γ Δ Q P Br es ac
      ... | no ¬rest = no λ { (_ ∷ rest) → ¬rest rest }
      ... | yes rest with matchRecv? Q P I α
      ...   | no ¬m = yes ((λ {j} {U} eq → ⊥-elim (¬m (j , U , eq))) ∷ rest)
      ...   | yes (j , U , refl) with ac
      ...     | acc rs
        with alg? (U ∷ Γ) Δ P (lookup Br j) t
               (rs (≺proc (s≤s (size/lookup Br j))))
      ...       | no ¬td = no λ { (h ∷ _) → ¬td (h refl) }
      ...       | yes td = yes ((λ { refl → td }) ∷ rest)

      -- ── the forward search ──────────────────────────────────────────

      tree? Γ Δ Ξ P Pr s visited cov (acc rs) with ∈T? G P s
      ... | yes p∈T =
        treeA? Γ Δ Ξ P Pr s p∈T visited cov (rs (≺phase 3<4))
      ... | no ¬p∈T
        with treeB? Γ Δ P Pr s ¬p∈T empty (rs (≺regime 0<1))
      ...   | inj₁ f = yes (f Ξ)
      ...   | inj₂ (bv , s∈bv , ff) = no (failed⇒¬tree {bv = bv} ff s∈bv)

      treeA? Γ Δ Ξ P Pr s p∈T visited cov (acc rs)
        with blocked? Γ Δ P Pr s (rs (≺phase 2<3))
      ... | yes bl = yes (skip/main bl)
      ... | no ¬bl with anyBisim? Ξ s
      ...   | yes (X , eq) = yes (skip/cycle eq p∈T)
      ...   | no ¬cyc with lookup visited s in eqv
      ...     | true =
        ⊥-elim (¬cyc (let X , eq = cov s (subst T (sym eqv) tt)
                      in X , subst (λ z → z ~ s) (sym eq) ~refl))
      ...     | false with na? P s
      ...       | no ¬na =
        no λ { (skip/main bl) → ¬bl bl
             ; (skip/step gr na ktd) → ¬na na
             ; (skip/cycle eq inT) → ¬cyc (_ , eq) }
      ...       | yes na with anyStep? s
      ...         | no ¬st =
        no λ { (skip/main bl) → ¬bl bl
             ; (skip/step gr na′ ktd) → ¬st (_ , _ , gr)
             ; (skip/cycle eq inT) → ¬cyc (_ , eq) }
      ...         | yes (α , u , gr)
        with treeAs? Γ Δ (s ∷ Ξ) P Pr (edges G s) (mark s visited)
               (covers-∷ {visited = visited} s cov)
               (rs (≺visit (mark-decreases visited s eqv)))
      ...           | yes subs =
        yes (skip/step gr na
              (λ gr′ → All.lookup subs (step⇒listed {G = G} gr′)))
      ...           | no ¬subs =
        no λ { (skip/main bl) → ¬bl bl
             ; (skip/step gr₁ na₁ ktd) →
                 ¬subs (All.tabulate
                         (λ { {α₁ , t₁} mem → ktd (listed⇒step {G = G} mem) }))
             ; (skip/cycle eq inT) → ¬cyc (_ , eq) }

      treeAs? Γ Δ Ξ P Pr [] visited cov ac = yes []
      treeAs? Γ Δ Ξ P Pr ((α , t) ∷ es) visited cov ac
        with treeAs? Γ Δ Ξ P Pr es visited cov ac
      ... | no ¬rest = no λ { (_ ∷ rest) → ¬rest rest }
      ... | yes rest with ac
      ...   | acc rs with tree? Γ Δ Ξ P Pr t visited cov (rs (≺phase 4<6))
      ...     | no ¬th = no λ { (th ∷ _) → ¬th th }
      ...     | yes th = yes (th ∷ rest)

      treeB? Γ Δ P Pr s ¬p∈T stack (acc rs) with lookup stack s in eqv
      ... | true = inj₂ (stack , subst T (sym eqv) tt , λ r r∈ → inj₁ r∈)
      ... | false with blocked? Γ Δ P Pr s (rs (≺phase 2<4))
      ...   | yes bl = inj₁ (λ Ξ → skip/main bl)
      ...   | no ¬bl with na? P s
      ...     | no ¬na = inj₂ (mark s stack , mark-here stack s , ff)
        where
        ff : FailedFrom Γ Δ P Pr stack (mark s stack)
        ff r r∈ with r ≟Fin s
        ... | yes refl = inj₂ (¬p∈T , ¬bl , inj₁ ¬na)
        ... | no r≢s = inj₁ (mark-there {bv = stack} {t = s} r≢s r∈)
      ...     | yes na with anyStep? s
      ...       | no ¬st = inj₂ (mark s stack , mark-here stack s , ff)
        where
        ff : FailedFrom Γ Δ P Pr stack (mark s stack)
        ff r r∈ with r ≟Fin s
        ... | yes refl = inj₂ (¬p∈T , ¬bl , inj₂ (inj₁ ¬st))
        ... | no r≢s = inj₁ (mark-there {bv = stack} {t = s} r≢s r∈)
      ...       | yes (α , u , gr)
        with treeBs? Γ Δ P Pr (edges G s)
               (λ mem p∈T → ¬p∈T (in/later (listed⇒step {G = G} mem) p∈T))
               (mark s stack)
               (rs (≺visit (mark-decreases stack s eqv)))
      ...         | inj₁ subs =
        inj₁ (λ Ξ → skip/step gr na
                      (λ gr′ →
                        All.lookup subs (step⇒listed {G = G} gr′) (s ∷ Ξ)))
      ...         | inj₂ (bv , β , w , mem , w∈bv , ff₀) =
        inj₂ (mark s bv , mark-here bv s , ff)
        where
        ff : FailedFrom Γ Δ P Pr stack (mark s bv)
        ff r r∈ with r ≟Fin s
        ... | yes refl =
          inj₂ (¬p∈T , ¬bl ,
                inj₂ (inj₂ (β , w , listed⇒step {G = G} mem ,
                            mark-mono bv s w w∈bv)))
        ... | no r≢s with ff₀ r (mark-there {bv = bv} {t = s} r≢s r∈)
        ...   | inj₁ r∈stack =
          inj₁ (mark-there {bv = stack} {t = s} r≢s r∈stack)
        ...   | inj₂ just = inj₂ (just-mono {bv = bv} s just)

      treeBs? Γ Δ P Pr [] nx stack ac = inj₁ []
      treeBs? Γ Δ P Pr ((α , u) ∷ es) nx stack ac with ac
      ... | acc rs with treeB? Γ Δ P Pr u (nx (Any.here refl)) stack
                          (rs (≺phase 4<6))
      ...   | inj₂ (bv , u∈bv , ff) =
        inj₂ (bv , α , u , Any.here refl , u∈bv , ff)
      ...   | inj₁ tu
        with treeBs? Γ Δ P Pr es (λ mem → nx (Any.there mem)) stack ac
      ...     | inj₁ rest = inj₁ (tu ∷ rest)
      ...     | inj₂ (bv , β , w , mem , w∈bv , ff) =
        inj₂ (bv , β , w , Any.there mem , w∈bv , ff)

    -- ══════════════════════════════════════════════════════════════════
    --  Step 4 — `Dec (⊢p)`, for free
    -- ══════════════════════════════════════════════════════════════════
    --
    -- `alg/typing` is soundness and `norm` is completeness, both already
    -- proved and hole-free.  There is deliberately no bespoke completeness
    -- argument for `⊢p` here — that is what this whole plan was for.

    alg :
      ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
        (P : Part) (Pr : Proc γ δ) (s : State G)
      → Dec (Γ & Δ ⊢a P ◂ Pr ∶ s)
    alg Γ Δ P Pr s = alg? Γ Δ P Pr s (≺-wellFounded _)

    tc? :
      ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
        (P : Part) (Pr : Proc γ δ) (s : State G)
      → Dec (Γ & Δ ⊢p P ◂ Pr ∶ s)
    tc? Γ Δ P Pr s =
      map′ alg/typing (λ td → NM.norm td skip/refl) (alg Γ Δ P Pr s)

    tcSession? : (M : Session) (s : State G) → Dec (⊢s M ∶ s)
    tcSession? M s = FinP.all? (λ P → tc? [] [] P (M [ P ]s) s)
