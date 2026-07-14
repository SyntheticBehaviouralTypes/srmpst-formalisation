{-# OPTIONS --guardedness #-}

open import Data.Bool using (Bool; true; false; not; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
  renaming (_≟_ to _≟Fin_)
import Data.Fin as F
import Data.Fin.Properties as Fin
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any as Any
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
import Data.Nat.Properties as Nat
open import Data.Product
  using (_×_; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_; lookup; tabulate)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (T?; ⌊_⌋; toWitness; fromWitness)

open import Definitions.Behav using (BTheory; WellBehaved)
open import Definitions.Expr
import Definitions.Common
import Definitions.Proc
import Definitions.Typing as Typing

module Definitions.TypeChecker where

  TypedExpression :
    ∀ {γ} → Vec Sort γ → Exp γ → Set
  TypedExpression Γ E =
    Σ[ S ∈ Sort ] Γ ⊢e E ∶ S

  valueTyped :
    ∀ V → ⊢v V ∶ sort/value V
  valueTyped (v/bool _) = tv/bool
  valueTyped (v/nat _) = tv/nat
  valueTyped v/unit = tv/unit

  inferExpression :
    ∀ {γ} (Γ : Vec Sort γ) (E : Exp γ)
    → Dec (TypedExpression Γ E)
  inferExpression Γ (val V) =
    yes (sort/value V , te/val (valueTyped V))
  inferExpression Γ (minus1 E) with inferExpression Γ E
  ... | yes (s/nat , td) = yes (s/nat , te/minus1 td)
  ... | yes (s/bool , bd) =
    no λ { (_ , te/minus1 td) → s/nat≢s/bool (⊢e-unique td bd) }
  ... | yes (s/unit , ud) =
    no λ { (_ , te/minus1 td) → s/nat≢s/unit (⊢e-unique td ud) }
  ... | no ¬E = no λ { (_ , te/minus1 td) → ¬E (s/nat , td) }
  inferExpression Γ (is-zero E) with inferExpression Γ E
  ... | yes (s/nat , td) = yes (s/bool , te/is-zero td)
  ... | yes (s/bool , bd) =
    no λ { (_ , te/is-zero td) → s/nat≢s/bool (⊢e-unique td bd) }
  ... | yes (s/unit , ud) =
    no λ { (_ , te/is-zero td) → s/nat≢s/unit (⊢e-unique td ud) }
  ... | no ¬E = no λ { (_ , te/is-zero td) → ¬E (s/nat , td) }
  inferExpression Γ (var x) =
    yes (lookup Γ x , te/var)

  module Processes (N : ℕ) where

    module Common = Definitions.Common N
    module Syntax = Definitions.Proc N

    open import LTS.Algebra N
      using (RootedGraph; underlying; initial)
    open import LTS.Action N
    open import LTS.Bisimulation N
    open import LTS.Core N
    open import LTS.Decision N using (wellBehaved?)
    open import LTS.Reachability N
      using ( ∈T?; reachVia?; reachVia-sound
            ; PathVia; path/nil; path/cons; pathVia-snoc
            ; PathViaP; pathP/nil; pathP/cons; pathViaP-snoc
            ; pathViaP→pathVia; pathVia→pathViaP; pathViaP-map
            ; wt; Incl; wt/mono; wt/strict; wt-bound; wt-full
            ; ≡true→T; T→≡true )

    module GraphChecker
      (G : Graph)
      (wb : WellBehaved (graphTheory G))
      where

      private
        module T = Typing.MPST wb

      open T

      mutual
        processFuel : ∀ {γ δ} → Proc γ δ → ℕ
        processFuel (_ ! _ < _ >∙ Pr) = suc (processFuel Pr)
        processFuel (Σ _ ？[ _ ]· Br) = suc (branchesFuel Br)
        processFuel (ifp _ then Pr else Pr′) =
          suc (processFuel Pr + processFuel Pr′)
        processFuel (rec Pr) = suc (processFuel Pr)
        processFuel (v _) = 1
        processFuel ∅ = 1

        branchesFuel :
          ∀ {γ δ I} → Vec (Proc γ δ) I → ℕ
        branchesFuel [] = 0
        branchesFuel (Pr ∷ Br) =
          processFuel Pr + branchesFuel Br

      messageGuarded? :
        ∀ {γ δ} (Pr : Proc γ δ)
        → Dec (MessageGuarded Pr)
      messageGuarded? (_ ! _ < _ >∙ _) = yes mg/send
      messageGuarded? (Σ _ ？[ _ ]· _) = yes mg/recv
      messageGuarded? (ifp _ then Pr else Pr′)
        with messageGuarded? Pr | messageGuarded? Pr′
      ... | yes guarded | yes guarded′ =
        yes (mg/if guarded guarded′)
      ... | no ¬guarded | _ =
        no λ { (mg/if guarded _) → ¬guarded guarded }
      ... | yes _ | no ¬guarded′ =
        no λ { (mg/if _ guarded′) → ¬guarded′ guarded′ }
      messageGuarded? (rec _) = no λ ()
      messageGuarded? (v _) = no λ ()
      messageGuarded? ∅ = no λ ()

      MatchRecv : Part → Part → ℕ → Action → Set
      MatchRecv P Q I α =
        Σ[ j ∈ Fin (suc I) ]
        Σ[ U ∈ Sort ]
          α ≡ (P ⟶ Q # j < U >)

      matchRecv? :
        ∀ P Q I α → Dec (MatchRecv P Q I α)
      matchRecv? P Q I
        ((R ⟶ S) # (_<_> {nchoices = J} j U))
        with R ≟Fin P | S ≟Fin Q | J Nat.≟ I
      ... | yes refl | yes refl | yes refl =
        yes (j , U , refl)
      ... | no R≢P | _ | _ =
        no λ { (_ , _ , refl) → R≢P refl }
      ... | _ | no S≢Q | _ =
        no λ { (_ , _ , refl) → S≢Q refl }
      ... | _ | _ | no J≢I =
        no λ { (_ , _ , refl) → J≢I refl }

      ActionAt : Action → List (Edge (size G)) → Set
      ActionAt α xs =
        Σ[ t ∈ State G ] (α , t) ∈ xs

      findAction :
        (α : Action) (xs : List (Edge (size G)))
        → Dec (ActionAt α xs)
      findAction α [] = no λ { (_ , ()) }
      findAction α ((β , t) ∷ xs) with β ≟Action α
      ... | yes refl = yes (t , Any.here refl)
      ... | no β≢α with findAction α xs
      ...   | yes (u , member) = yes (u , Any.there member)
      ...   | no ¬rest =
        no λ { (_ , Any.here px) → β≢α (sym (cong proj₁ px))
             ; (u , Any.there m) → ¬rest (u , m) }

      findStep :
        ∀ s α
        → Dec
            (Σ[ t ∈ State G ]
              BTheory._-<_>->_ (graphTheory G) s α t)
      findStep s α with findAction α (edges G s)
      ... | yes (t , member) =
        yes (t , listed⇒step {G = G} member)
      ... | no ¬found =
        no λ { (t , gr) → ¬found (t , step⇒listed {G = G} gr) }

      RecvWitness :
        Part → Part → ℕ → List (Edge (size G)) → Set
      RecvWitness P Q I xs =
        Σ[ j ∈ Fin (suc I) ]
        Σ[ U ∈ Sort ]
        Σ[ t ∈ State G ]
          ((P ⟶ Q # j < U >) , t) ∈ xs

      findRecv :
        (P Q : Part) (I : ℕ) (xs : List (Edge (size G)))
        → Dec (RecvWitness P Q I xs)
      findRecv P Q I [] = no λ { (_ , _ , _ , ()) }
      findRecv P Q I ((α , t) ∷ xs)
        with matchRecv? P Q I α
      ... | yes (j , U , refl) =
        yes (j , U , t , Any.here refl)
      ... | no ¬match with findRecv P Q I xs
      ...   | yes (j , U , u , member) =
        yes (j , U , u , Any.there member)
      ...   | no ¬rest =
        no λ { (j , U , _ , Any.here px) →
                 ¬match (j , U , sym (cong proj₁ px))
             ; (j , U , u , Any.there m) →
                 ¬rest (j , U , u , m) }

      CheckFunction : Set
      CheckFunction =
        ∀ {γ δ}
        → (Γ : Vec Sort γ)
        → (Δ : Vec (State G) δ)
        → (P : Part)
        → (Pr : Proc γ δ)
        → (s : State G)
        → Maybe (Γ & Δ ⊢p P ◂ Pr ∶ s)

      RecvAt :
        ∀ {γ δ I}
        → Vec Sort γ
        → Vec (State G) δ
        → (P Q : Part)
        → Vec (Proc (suc γ) δ) (suc I)
        → Edge (size G)
        → Set
      RecvAt Γ Δ P Q Br (α , t) =
        ∀ {j U}
        → α ≡ (P ⟶ Q # j < U >)
        → (U ∷ Γ) & Δ ⊢p Q ◂ lookup Br j ∶ t

      checkContinuation :
        ∀ {γ δ I}
        → CheckFunction
        → (Γ : Vec Sort γ)
        → (Δ : Vec (State G) δ)
        → (P Q : Part)
        → (Br : Vec (Proc (suc γ) δ) (suc I))
        → (edge : Edge (size G))
        → Maybe (RecvAt Γ Δ P Q Br edge)
      checkContinuation recur Γ Δ P Q Br (α , t)
        with matchRecv? P Q _ α
      ... | no noMatch =
        just λ { {j} {U} eq →
          ⊥-elim (noMatch (j , U , eq)) }
      ... | yes (j , U , refl) with
        recur (U ∷ Γ) Δ Q (lookup Br j) t
      ...   | just td = just λ { refl → td }
      ...   | nothing = nothing

      checkContinuations :
        ∀ {γ δ I}
        → CheckFunction
        → (Γ : Vec Sort γ)
        → (Δ : Vec (State G) δ)
        → (P Q : Part)
        → (Br : Vec (Proc (suc γ) δ) (suc I))
        → (xs : List (Edge (size G)))
        → Maybe (All.All (RecvAt Γ Δ P Q Br) xs)
      checkContinuations recur Γ Δ P Q Br [] =
        just All.[]
      checkContinuations recur Γ Δ P Q Br
        (edge ∷ xs)
        with checkContinuation recur Γ Δ P Q Br edge
        | checkContinuations recur Γ Δ P Q Br xs
      ... | just checked | just rest =
        just (checked All.∷ rest)
      ... | _ | _ = nothing

      checkDirect : CheckFunction → CheckFunction
      checkDirect recur Γ Δ P
        (Q ! i < E >∙ Pr) s
        with inferExpression Γ E
      ... | no _ = nothing
      ... | yes (S , etd) with
        findStep s (P ⟶ Q # i < S >)
      ...   | no _ = nothing
      ...   | yes (t , gr) with
        recur Γ Δ P Pr t
      ...     | just td = just (t/send gr etd td)
      ...     | nothing = nothing
      checkDirect recur Γ Δ Q
        (Σ P ？[ S ]· Br) s
        with findRecv P Q _ (edges G s)
        | checkContinuations
            recur Γ Δ P Q Br (edges G s)
      ... | no _ | _ = nothing
      ... | _ | nothing = nothing
      ... | yes (_ , _ , _ , selected) | just checked =
        just
          (t/recv
            (listed⇒step {G = G} selected)
            (λ gr →
              All.lookup checked (step⇒listed {G = G} gr) refl))
      checkDirect recur Γ Δ P
        (ifp E then Pr else Pr′) s
        with inferExpression Γ E
        | recur Γ Δ P Pr s
        | recur Γ Δ P Pr′ s
      ... | yes (s/bool , etd) | just td | just td′ =
        just (t/if etd td td′)
      ... | _ | _ | _ = nothing
      checkDirect recur Γ Δ P (rec Pr) s
        with messageGuarded? Pr
        | recur Γ (s ∷ Δ) P Pr s
      ... | yes guarded | just td = just (t/rec guarded td)
      ... | _ | _ = nothing
      checkDirect recur Γ Δ P (v X) s
        with T? (bisim? G (lookup Δ X) s)
      ... | yes related =
        just (t/var (sound (bisimulationCorrect G) related))
      ... | no _ = nothing
      checkDirect recur Γ Δ P ∅ s
        with ∈T? G P s
      ... | no P∉T = just (t/end P∉T)
      ... | yes _ = nothing

      Incoming :
        Part
        → State G
        → List (Edge (size G))
        → Set
      Incoming P s xs =
        Σ[ α ∈ Action ] ((α , s) ∈ xs × P ∉α α)

      findIncoming :
        (P : Part)
        → (s : State G)
        → (xs : List (Edge (size G)))
        → Dec (Incoming P s xs)
      findIncoming P s [] = no λ { (_ , () , _) }
      findIncoming P s ((α , t) ∷ xs)
        with t ≟Fin s | _∉α?_ P α
      ... | yes refl | yes P∉α =
        yes (α , Any.here refl , P∉α)
      ... | no t≢s | _ with findIncoming P s xs
      ...   | yes (β , member , P∉β) =
        yes (β , Any.there member , P∉β)
      ...   | no ¬rest =
        no λ { (β , Any.here px , _) → t≢s (sym (cong proj₂ px))
             ; (β , Any.there m , P∉β) → ¬rest (β , m , P∉β) }
      findIncoming P s ((α , t) ∷ xs)
        | yes refl | no ¬P∉α with findIncoming P s xs
      ...   | yes (β , member , P∉β) =
        yes (β , Any.there member , P∉β)
      ...   | no ¬rest =
        no λ { (β , Any.here px , P∉β) →
                 ¬P∉α (subst (P ∉α_) (cong proj₁ px) P∉β)
             ; (β , Any.there m , P∉β) → ¬rest (β , m , P∉β) }

      checkPredecessor :
        ∀ {γ δ}
        → CheckFunction
        → (Γ : Vec Sort γ)
        → (Δ : Vec (State G) δ)
        → (P : Part)
        → (Pr : Proc γ δ)
        → (s r : State G)
        → Maybe (Γ & Δ ⊢p P ◂ Pr ∶ s)
      checkPredecessor recur Γ Δ P Pr s r
        with findIncoming P s (edges G r)
      ... | no _ = nothing
      ... | yes (_ , member , P∉α) with recur Γ Δ P Pr r
      ...   | nothing = nothing
      ...   | just td =
        just
          (t/unskip
            (skip/one (listed⇒step {G = G} member) P∉α)
            td)

      checkPredecessors :
        ∀ {γ δ n}
        → CheckFunction
        → (Γ : Vec Sort γ)
        → (Δ : Vec (State G) δ)
        → (P : Part)
        → (Pr : Proc γ δ)
        → (s : State G)
        → Vec (State G) n
        → Maybe (Γ & Δ ⊢p P ◂ Pr ∶ s)
      checkPredecessors recur Γ Δ P Pr s [] = nothing
      checkPredecessors recur Γ Δ P Pr s (r ∷ rs)
        with checkPredecessor recur Γ Δ P Pr s r
        | checkPredecessors recur Γ Δ P Pr s rs
      ... | just td | _ = just td
      ... | nothing | result = result

      InactiveAt : Part → State G → Set
      InactiveAt P s =
        All.All (λ edge → P ∉α proj₁ edge) (edges G s)

      inactiveAt? :
        (P : Part) (s : State G) → Dec (InactiveAt P s)
      inactiveAt? P s =
        All.all?
          (λ edge → _∉α?_ P (proj₁ edge))
          (edges G s)

      -- ════════════════════════════════════════════════════════════════
      --  Semantic characterization of `⊢skip[ prod ]`  (§3.1, §3.3)
      --
      --  A `prod` skip tree rooted at `s` (visited vector `[]`) exists iff
      --  every state reachable from `s` while staying outside the leaf set
      --  `L` (the directly-typable states) is P-inactive and can itself
      --  reach an `L`-state.  This is decidable via the graph reachability
      --  fixed point (`reachVia?`).  Deciding it replaces the fuelled
      --  `checkSkip`/`checkSkipStep` search; the constructor direction
      --  (Theorem B) turns a positive decision into a derivation.
      -- ════════════════════════════════════════════════════════════════

      private
        _×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
        yes a ×-dec yes b = yes (a , b)
        no ¬a ×-dec _     = no λ { (a , _) → ¬a a }
        _     ×-dec no ¬b = no λ { (_ , b) → ¬b b }

        _→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
        yes _ →-dec yes b = yes (λ _ → b)
        yes a →-dec no ¬b = no λ f → ¬b (f a)
        no ¬a →-dec _     = yes λ a → ⊥-elim (¬a a)

        _⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
        yes a ⊎-dec _     = yes (inj₁ a)
        no _  ⊎-dec yes b = yes (inj₂ b)
        no ¬a ⊎-dec no ¬b = no λ { (inj₁ a) → ¬a a ; (inj₂ b) → ¬b b }

        ¬?_ : ∀ {A : Set} → Dec A → Dec (¬ A)
        ¬? (yes a) = no λ ¬a → ¬a a
        ¬? (no ¬a) = yes ¬a

        false≢true : false ≢ true
        false≢true ()

      -- `P not-active-in t` (abstract form) decided through `InactiveAt`.
      na? : ∀ P t → Dec (P not-active-in t)
      na? P t with inactiveAt? P t
      ... | yes inact =
        yes λ gr → All.lookup inact (step⇒listed {G = G} gr)
      ... | no ¬inact =
        no λ na → ¬inact (All.tabulate λ mem → na (listed⇒step {G = G} mem))

      -- ── Predicate-form semantic skip (§3.1) ──
      --
      --  These are phrased over a *bare* predicate `L : State G → Set` (no
      --  decidability assumed), so `SemSkipP L P s` can be a premise of the
      --  algorithmic judgment `Alg` (§4), whose leaf set `L = Alg k` is not yet
      --  known to be decidable when `Alg (suc k)` is formed.  The paths avoid
      --  `L` via the predicate filter `PathViaP` rather than a Bool mark.
      --  `SkipSem` (below) supplies the decision and the constructor, bridging
      --  to the Bool reachability fixed point through `L?`.

      NLP : (State G → Set) → State G → State G → Set
      NLP L s t = PathViaP G (λ u → ¬ L u) s t × ¬ L t

      ReachLP : (State G → Set) → State G → Set
      ReachLP L t = ∃[ ℓ ] (∃[ n ] PathVia G (λ _ → true) t ℓ n) × L ℓ

      SemSkipP : (State G → Set) → Part → State G → Set
      SemSkipP L P s =
        ∀ t → NLP L s t → (P not-active-in t) × ReachLP L t

      -- ── Deciding `SemSkipP` (§3.3) ──
      --
      --  Needs only the leaf predicate and its decision (no leaf *witnesses*),
      --  so it can be run with `L = Alg k` before soundness is available (§4).
      module SkipDecide
        (L : State G → Set)
        (L? : ∀ t → Dec (L t))
        (P : Part)
        where

        ∉L : State G → Bool
        ∉L t = not ⌊ L? t ⌋

        -- ── the Bool mark and the predicate filter agree ──
        ¬L→T∉L : ∀ {t} → ¬ L t → T (∉L t)
        ¬L→T∉L {t} ¬Lt with L? t
        ... | yes Lt = ⊥-elim (¬Lt Lt)
        ... | no  _  = tt

        T∉L→¬L : ∀ {t} → T (∉L t) → ¬ L t
        T∉L→¬L {t} with L? t
        ... | no ¬Lt = λ _ → ¬Lt
        ... | yes _  = λ h → ⊥-elim h

        -- decide the predicate-filtered reachability via the Bool fixed point
        pathViaP? : ∀ s t → Dec (PathViaP G (λ u → ¬ L u) s t)
        pathViaP? s t with reachVia? G ∉L s t
        ... | yes (_ , pv) = yes (pathVia→pathViaP G (λ _ → T∉L→¬L) pv)
        ... | no ¬pv = no λ pvp → ¬pv (pathViaP→pathVia G (λ _ → ¬L→T∉L) pvp)

        NL? : ∀ s t → Dec (NLP L s t)
        NL? s t = pathViaP? s t ×-dec (¬? (L? t))

        ReachL? : ∀ t → Dec (ReachLP L t)
        ReachL? t =
          Fin.any? (λ ℓ → reachVia? G (λ _ → true) t ℓ ×-dec L? ℓ)

        semSkip? : ∀ s → Dec (SemSkipP L P s)
        semSkip? s =
          Fin.all? (λ t → NL? s t →-dec (na? P t ×-dec ReachL? t))

      module SkipSem
        {γ δ}
        (Γ : Vec Sort γ)
        (Δ : Vec (State G) δ)
        (P : Part)
        (Pr : Proc γ δ)
        (L : State G → Set)
        (L? : ∀ t → Dec (L t))
        (leaf : ∀ t → L t → Γ & Δ ⊢p P ◂ Pr ∶ t)
        where

        -- states reachable from `s` by a path that stays outside `L`
        NL : State G → State G → Set
        NL = NLP L

        -- some `L`-state is reachable from `t`
        ReachL : State G → Set
        ReachL = ReachLP L

        SemSkip : State G → Set
        SemSkip = SemSkipP L P

        -- ── Theorem B (§3.4): a positive `SemSkip s` yields a `prod` tree ──

        -- membership in the visited vector, with the witnessing index
        memberV? : ∀ {ξ} (w : State G) (Ξ : Vec (State G) ξ)
          → Dec (∃[ X ] lookup Ξ X ≡ w)
        memberV? w [] = no λ { (() , _) }
        memberV? w (x ∷ Ξ) with w ≟Fin x
        ... | yes refl = yes (F.zero , refl)
        ... | no w≢x with memberV? w Ξ
        ...   | yes (X , eq) = yes (F.suc X , eq)
        ...   | no ¬mem =
          no λ { (F.zero , eq) → w≢x (sym eq)
               ; (F.suc X , eq) → ¬mem (X , eq) }

        -- the set of visited states as a Bool vector (the termination measure)
        mark : ∀ {ξ} → Vec (State G) ξ → Vec Bool (size G)
        mark Ξ = tabulate (λ x → ⌊ memberV? x Ξ ⌋)

        mark-lookup : ∀ {ξ} (Ξ : Vec (State G) ξ) x
          → lookup (mark Ξ) x ≡ ⌊ memberV? x Ξ ⌋
        mark-lookup Ξ x = VecP.lookup∘tabulate _ x

        mem→marked : ∀ {ξ} {Ξ : Vec (State G) ξ} {x}
          → (∃[ X ] lookup Ξ X ≡ x) → lookup (mark Ξ) x ≡ true
        mem→marked {Ξ = Ξ} {x} m =
          trans (mark-lookup Ξ x) (T→≡true (fromWitness m))

        marked→mem : ∀ {ξ} {Ξ : Vec (State G) ξ} {x}
          → lookup (mark Ξ) x ≡ true → ∃[ X ] lookup Ξ X ≡ x
        marked→mem {Ξ = Ξ} {x} p =
          toWitness (≡true→T (trans (sym (mark-lookup Ξ x)) p))

        unmarked : ∀ {ξ} {Ξ : Vec (State G) ξ} {x}
          → ¬ (∃[ X ] lookup Ξ X ≡ x) → lookup (mark Ξ) x ≡ false
        unmarked {Ξ = Ξ} {x} ¬m with memberV? x Ξ | mark-lookup Ξ x
        ... | yes m | _  = ⊥-elim (¬m m)
        ... | no  _ | eq = eq

        mark-mono : ∀ {ξ} (w : State G) (Ξ : Vec (State G) ξ)
          → Incl (mark Ξ) (mark (w ∷ Ξ))
        mark-mono w Ξ i Ti =
          ≡true→T
            (mem→marked {Ξ = w ∷ Ξ} {x = i}
              (cons (marked→mem {Ξ = Ξ} {x = i} (T→≡true Ti))))
          where cons : (∃[ X ] lookup Ξ X ≡ i)
                     → ∃[ X′ ] lookup (w ∷ Ξ) X′ ≡ i
                cons (X , eq) = F.suc X , eq

        mark-push : ∀ {ξ} {w : State G} {Ξ : Vec (State G) ξ}
          → ¬ (∃[ X ] lookup Ξ X ≡ w)
          → suc (wt (mark Ξ)) ≤ wt (mark (w ∷ Ξ))
        mark-push {w = w} {Ξ} w∉ =
          wt/strict {left = mark Ξ} {right = mark (w ∷ Ξ)}
            (mark-mono w Ξ) neq
          where neq : mark Ξ ≢ mark (w ∷ Ξ)
                neq e = false≢true
                  (trans (sym (unmarked {Ξ = Ξ} {x = w} w∉))
                    (trans (cong (λ z → lookup z w) e)
                           (mem→marked {Ξ = w ∷ Ξ} {x = w} (F.zero , refl))))

        -- extend an NL-certificate through one edge to a non-L successor
        extNL : ∀ {s t β u} → NL s t
          → BTheory._-<_>->_ (graphTheory G) t β u → ¬ L u → NL s u
        extNL (path , ¬Lt) gr ¬Lu =
          pathViaP-snoc G path ¬Lt gr , ¬Lu

        module _ (s : State G) (sem : SemSkip s) where

          build : (outer : ℕ) → ∀ {ξ} (Ξ : Vec (State G) ξ) (t : State G)
                → size G ≤ wt (mark (t ∷ Ξ)) + outer
                → NL s t
                → (ℓ : State G) → ∀ {n} → PathVia G (λ _ → true) t ℓ n → L ℓ
                → Γ & Δ & Ξ ⊢skip[ prod ] P ◂ Pr ∶ t
          build outer Ξ t inv nlt ℓ path Lℓ with L? t
          ... | yes Lt = skip/main (leaf t Lt)
          ... | no ¬Lt with path
          ...   | path/nil = ⊥-elim (¬Lt Lℓ)
          ...   | path/cons {u = u*} _ gr rest =
                  skip/step gr (proj₁ (sem t nlt)) ktd prod-gr
            where
              invStep : size G ≤ wt (mark (u* ∷ t ∷ Ξ)) + outer
              invStep =
                Nat.≤-trans inv
                  (Nat.+-monoˡ-≤ outer
                    (wt/mono {left = mark (t ∷ Ξ)} {right = mark (u* ∷ t ∷ Ξ)}
                      (mark-mono u* (t ∷ Ξ))))

              ktd : ∀ {G″ β} → BTheory._-<_>->_ (graphTheory G) t β G″
                  → ∃[ m ] Γ & Δ & (t ∷ Ξ) ⊢skip[ m ] P ◂ Pr ∶ G″
              ktd {G″} gr′ with L? G″
              ... | yes LG″ = prod , skip/main (leaf G″ LG″)
              ... | no ¬LG″ with G″ ≟Fin u*
              ...   | yes refl =
                      prod ,
                      build outer (t ∷ Ξ) u* invStep (extNL nlt gr ¬LG″) ℓ rest Lℓ
              ...   | no _ with memberV? G″ (t ∷ Ξ)
              ...     | yes (X , eqX) =
                        nonprod ,
                        skip/cycle {X = X} (subst (lookup (t ∷ Ξ) X ~_) eqX ~refl)
              ...     | no G″∉ = fresh outer inv
                where
                  fullEq : size G ≤ wt (mark (t ∷ Ξ)) + zero
                         → wt (mark (t ∷ Ξ)) ≡ size G
                  fullEq iz =
                    Nat.≤-antisym (wt-bound (mark (t ∷ Ξ)))
                      (subst (size G ≤_) (Nat.+-identityʳ _) iz)

                  fresh : ∀ o → size G ≤ wt (mark (t ∷ Ξ)) + o
                        → ∃[ m ] Γ & Δ & (t ∷ Ξ) ⊢skip[ m ] P ◂ Pr ∶ G″
                  fresh zero iz =
                    ⊥-elim (G″∉ (marked→mem {Ξ = t ∷ Ξ} {x = G″}
                                   (wt-full {v = mark (t ∷ Ξ)} (fullEq iz) G″)))
                  fresh (suc o) is =
                    let nlG″ = extNL nlt gr′ ¬LG″
                        rl = proj₂ (sem G″ nlG″)
                        invFresh : size G ≤ wt (mark (G″ ∷ t ∷ Ξ)) + o
                        invFresh =
                          Nat.≤-trans
                            (subst (size G ≤_) (Nat.+-suc _ o) is)
                            (Nat.+-monoˡ-≤ o (mark-push {w = G″} {Ξ = t ∷ Ξ} G″∉))
                    in prod ,
                       build o (t ∷ Ξ) G″ invFresh nlG″
                         (proj₁ rl) (proj₂ (proj₁ (proj₂ rl))) (proj₂ (proj₂ rl))

              prod-gr : proj₁ (ktd gr) ≡ prod
              prod-gr with L? u*
              ... | yes _ = refl
              ... | no _ with u* ≟Fin u*
              ...   | yes refl = refl
              ...   | no ¬p = ⊥-elim (¬p refl)

          theoremB : Γ & Δ & [] ⊢skip[ prod ] P ◂ Pr ∶ s
          theoremB with L? s
          ... | yes Ls = skip/main (leaf s Ls)
          ... | no ¬Ls =
            let nlt : NL s s
                nlt = pathP/nil , ¬Ls
                rl = proj₂ (sem s nlt)
            in build (size G) [] s
                 (Nat.m≤n+m (size G) (wt (mark (s ∷ [])))) nlt
                 (proj₁ rl) (proj₂ (proj₁ (proj₂ rl))) (proj₂ (proj₂ rl))

      -- Extract the witness from a successful `recur` call.
      fromT : ∀ {A : Set} (m : Maybe A) → T (is-just m) → A
      fromT (just x) _ = x
      fromT nothing ()

      -- The skip closure is now a genuine decision procedure.  The leaf set
      -- `L t` is "`recur` types `t` directly"; it is decidable because `recur`
      -- returns a `Maybe`.  `semSkip?` decides the finite-graph reachability
      -- characterisation `SemSkip s`, and `theoremB` turns a positive answer
      -- into a `prod` skip tree — including the cyclic `skip/cycle` case.
      checkClosureSkip : CheckFunction → CheckFunction
      checkClosureSkip recur Γ Δ P Pr s = go (SkipDecide.semSkip? L L? P s)
        where
          L : State G → Set
          L t = T (is-just (recur Γ Δ P Pr t))

          L? : ∀ t → Dec (L t)
          L? t = T? (is-just (recur Γ Δ P Pr t))

          leaf : ∀ t → L t → Γ & Δ ⊢p P ◂ Pr ∶ t
          leaf t lt = fromT (recur Γ Δ P Pr t) lt

          open SkipSem Γ Δ P Pr L L? leaf

          go : Dec (SemSkipP L P s)
             → Maybe (Γ & Δ ⊢p P ◂ Pr ∶ s)
          go (yes sem) = just (t/skip (theoremB s sem))
          go (no _) = nothing

      checkClosure : CheckFunction → CheckFunction
      checkClosure recur Γ Δ P Pr s
        with checkPredecessors recur Γ Δ P Pr s (states G)
      ... | just td = just td
      ... | nothing = checkClosureSkip recur Γ Δ P Pr s

      checkWithFuel : ℕ → CheckFunction
      checkWithFuel 0 Γ Δ P Pr s = nothing
      checkWithFuel (suc fuel) Γ Δ P Pr s
        with checkDirect (checkWithFuel fuel) Γ Δ P Pr s
      ... | just td = just td
      ... | nothing =
        checkClosure (checkWithFuel fuel) Γ Δ P Pr s

      check : CheckFunction
      check Γ Δ P Pr =
        checkWithFuel
          (suc (size G) * processFuel Pr)
          Γ Δ P Pr

      -- ════════════════════════════════════════════════════════════════
      --  §4: the bounded algorithmic judgment `Alg`
      --
      --  `Alg k` mirrors the fuelled checker as a *proposition* so that fuel
      --  exhaustion is an honest refutation (`Alg 0 = ⊥`) rather than an
      --  inconclusive `nothing`.  It is a recursive *function* on the fuel,
      --  not a datatype: the skip premise `SemSkipP (Alg k)` filters paths by
      --  `¬ Alg k`, which violates strict positivity for a datatype but is
      --  fine for a function whose recursion is on the fuel.
      --
      --    Alg (suc k) = Direct (Alg k)          -- syntax-directed rule
      --                ⊎ (one unskip STEP to a predecessor typed by Alg k)
      --                ⊎ SemSkipP (Alg k)         -- a skip round (§3)
      --
      --  `checkWithFuelD` decides it exactly and `alg-sound` maps it back to
      --  the declarative judgment.
      -- ════════════════════════════════════════════════════════════════

      Pred : Set₁
      Pred = ∀ {γ δ} → Vec Sort γ → Vec (State G) δ
           → Part → Proc γ δ → State G → Set

      -- decide `~` on states via the bisimulation checker
      bisim?~ : ∀ x y → Dec (BTheory._~_ (graphTheory G) x y)
      bisim?~ x y with T? (bisim? G x y)
      ... | yes b = yes (sound (bisimulationCorrect G) b)
      ... | no ¬b = no λ r → ¬b (complete (bisimulationCorrect G) r)

      -- receive continuation, with the leaf predicate `L` at each branch
      RecvAtL :
        Pred → ∀ {γ δ I}
        → Vec Sort γ → Vec (State G) δ
        → (P Q : Part) → Vec (Proc (suc γ) δ) (suc I)
        → Edge (size G) → Set
      RecvAtL L Γ Δ P Q Br (α , t) =
        ∀ {j U} → α ≡ (P ⟶ Q # j < U >) → L (U ∷ Γ) Δ Q (lookup Br j) t

      -- the syntax-directed layer, parameterised by the leaf predicate `L`
      Direct : Pred → Pred
      Direct L Γ Δ P (Q ! i < E >∙ Pr) s =
        Σ[ S ∈ Sort ] Σ[ t ∈ State G ]
          (Γ ⊢e E ∶ S)
          × BTheory._-<_>->_ (graphTheory G) s (P ⟶ Q # i < S >) t
          × L Γ Δ P Pr t
      Direct L Γ Δ Q (Σ_？[_]·_ P {I = I} S Br) s =
        RecvWitness P Q I (edges G s)
        × All.All (RecvAtL L Γ Δ P Q Br) (edges G s)
      Direct L Γ Δ P (ifp E then Pr else Pr′) s =
        (Γ ⊢e E ∶ s/bool) × L Γ Δ P Pr s × L Γ Δ P Pr′ s
      Direct L Γ Δ P (rec Pr) s =
        MessageGuarded Pr × L Γ (s ∷ Δ) P Pr s
      Direct L Γ Δ P (v X) s =
        BTheory._~_ (graphTheory G) (lookup Δ X) s
      Direct L Γ Δ P ∅ s = ¬ P ∈T s

      -- deciding a single receive continuation
      recvAtL? :
        (L : Pred)
        → (recur : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
                    (P : Part) (Pr : Proc γ δ) (s : State G)
                    → Dec (L Γ Δ P Pr s))
        → ∀ {γ δ I} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
            (P Q : Part) (Br : Vec (Proc (suc γ) δ) (suc I)) (e : Edge (size G))
        → Dec (RecvAtL L Γ Δ P Q Br e)
      recvAtL? L recur Γ Δ P Q Br (α , t) with matchRecv? P Q _ α
      ... | no noMatch =
        yes λ { {j} {U} eq → ⊥-elim (noMatch (j , U , eq)) }
      ... | yes (j , U , refl) with recur (U ∷ Γ) Δ Q (lookup Br j) t
      ...   | yes a = yes λ { refl → a }
      ...   | no ¬a = no λ f → ¬a (f refl)

      -- deciding the syntax-directed layer, with full refutations
      direct? :
        (L : Pred)
        → (recur : ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
                    (P : Part) (Pr : Proc γ δ) (s : State G)
                    → Dec (L Γ Δ P Pr s))
        → ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
            (P : Part) (Pr : Proc γ δ) (s : State G)
        → Dec (Direct L Γ Δ P Pr s)
      direct? L recur Γ Δ P (Q ! i < E >∙ Pr) s
        with inferExpression Γ E
      ... | no ¬E = no λ { (S , _ , etd , _ , _) → ¬E (S , etd) }
      ... | yes (S , etd) with findStep s (P ⟶ Q # i < S >)
      ...   | no ¬st =
        no λ { (_ , t , etd′ , gr , _) →
          ¬st (t , subst
                     (λ σ → BTheory._-<_>->_ (graphTheory G) s
                              (P ⟶ Q # i < σ >) t)
                     (⊢e-unique etd′ etd) gr) }
      ...   | yes (t , gr) with recur Γ Δ P Pr t
      ...     | yes a = yes (S , t , etd , gr , a)
      ...     | no ¬a =
        no λ { (_ , t′ , etd′ , gr′ , a′) →
          ¬a (subst (λ u → L Γ Δ P Pr u)
                (step-deterministic
                  (subst
                    (λ σ → BTheory._-<_>->_ (graphTheory G) s
                             (P ⟶ Q # i < σ >) t′)
                    (⊢e-unique etd′ etd) gr′)
                  gr)
                a′) }
      direct? L recur Γ Δ Q (Σ_？[_]·_ P {I = I} S Br) s
        with findRecv P Q I (edges G s)
        | All.all? (recvAtL? L recur Γ Δ P Q Br) (edges G s)
      ... | no ¬rw | _ = no λ { (rw , _) → ¬rw rw }
      ... | yes _ | no ¬all = no λ { (_ , all) → ¬all all }
      ... | yes rw | yes all = yes (rw , all)
      direct? L recur Γ Δ P (ifp E then Pr else Pr′) s
        with inferExpression Γ E
        | recur Γ Δ P Pr s
        | recur Γ Δ P Pr′ s
      ... | yes (s/bool , etd) | yes a | yes a′ = yes (etd , a , a′)
      ... | yes (s/bool , _) | no ¬a | _ =
        no λ { (_ , a , _) → ¬a a }
      ... | yes (s/bool , _) | yes _ | no ¬a′ =
        no λ { (_ , _ , a′) → ¬a′ a′ }
      ... | yes (s/nat , etd) | _ | _ =
        no λ { (etd′ , _ , _) → s/nat≢s/bool (⊢e-unique etd etd′) }
      ... | yes (s/unit , etd) | _ | _ =
        no λ { (etd′ , _ , _) → s/unit≢s/bool (⊢e-unique etd etd′) }
      ... | no ¬E | _ | _ =
        no λ { (etd′ , _ , _) → ¬E (s/bool , etd′) }
      direct? L recur Γ Δ P (rec Pr) s
        with messageGuarded? Pr | recur Γ (s ∷ Δ) P Pr s
      ... | yes mg | yes a = yes (mg , a)
      ... | no ¬mg | _ = no λ { (mg , _) → ¬mg mg }
      ... | yes _ | no ¬a = no λ { (_ , a) → ¬a a }
      direct? L recur Γ Δ P (v X) s = bisim?~ (lookup Δ X) s
      direct? L recur Γ Δ P ∅ s = ¬? (∈T? G P s)

      -- soundness of the syntax-directed layer
      direct-sound :
        (L : Pred)
        → (leafSound : ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
                        {P} {Pr : Proc γ δ} {s}
                      → L Γ Δ P Pr s → Γ & Δ ⊢p P ◂ Pr ∶ s)
        → ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
            (P : Part) (Pr : Proc γ δ) (s : State G)
        → Direct L Γ Δ P Pr s → Γ & Δ ⊢p P ◂ Pr ∶ s
      direct-sound L ls Γ Δ P (Q ! i < E >∙ Pr) s (S , t , etd , gr , a) =
        t/send gr etd (ls a)
      direct-sound L ls Γ Δ Q (Σ_？[_]·_ P {I = I} S Br) s
        ((j , U , t , member) , all) =
        t/recv (listed⇒step {G = G} member)
               (λ gr′ → ls (All.lookup all (step⇒listed {G = G} gr′) refl))
      direct-sound L ls Γ Δ P (ifp E then Pr else Pr′) s (etd , a , a′) =
        t/if etd (ls a) (ls a′)
      direct-sound L ls Γ Δ P (rec Pr) s (mg , a) = t/rec mg (ls a)
      direct-sound L ls Γ Δ P (v X) s eq = t/var eq
      direct-sound L ls Γ Δ P ∅ s ¬in = t/end ¬in

      -- ── the judgment, its decision, and its soundness ──

      Alg : ℕ → Pred
      checkWithFuelD :
        ∀ k {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
          (P : Part) (Pr : Proc γ δ) (s : State G)
        → Dec (Alg k Γ Δ P Pr s)
      alg-sound :
        ∀ k {γ δ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
          {P} {Pr : Proc γ δ} {s}
        → Alg k Γ Δ P Pr s → Γ & Δ ⊢p P ◂ Pr ∶ s

      Alg zero    Γ Δ P Pr s = ⊥
      Alg (suc k) Γ Δ P Pr s =
          Direct (Alg k) Γ Δ P Pr s
        ⊎ (Σ[ r ∈ State G ] Incoming P s (edges G r) × Alg k Γ Δ P Pr r)
        ⊎ SemSkipP (Alg k Γ Δ P Pr) P s

      checkWithFuelD zero Γ Δ P Pr s = no λ ()
      checkWithFuelD (suc k) Γ Δ P Pr s =
        direct? (Alg k) (checkWithFuelD k) Γ Δ P Pr s
          ⊎-dec
            ( Fin.any? (λ r → findIncoming P s (edges G r)
                                ×-dec checkWithFuelD k Γ Δ P Pr r)
              ⊎-dec
              SkipDecide.semSkip?
                (Alg k Γ Δ P Pr) (checkWithFuelD k Γ Δ P Pr) P s )

      alg-sound zero ()
      alg-sound (suc k) {Γ = Γ} {Δ} {P} {Pr} {s} (inj₁ d) =
        direct-sound (Alg k) (alg-sound k) Γ Δ P Pr s d
      alg-sound (suc k) (inj₂ (inj₁ (r , (α , member , P∉α) , a))) =
        t/unskip (skip/one (listed⇒step {G = G} member) P∉α) (alg-sound k a)
      alg-sound (suc k) {Γ = Γ} {Δ} {P} {Pr} {s} (inj₂ (inj₂ sem)) =
        t/skip
          (SkipSem.theoremB Γ Δ P Pr
            (Alg k Γ Δ P Pr) (checkWithFuelD k Γ Δ P Pr) (λ _ → alg-sound k)
            s sem)

      -- ── Monotonicity in the fuel (§4; used by completeness §6) ──

      -- `Direct` is covariant in its leaf predicate (all `L`-occurrences are
      -- positive).
      direct-mono :
        {L L′ : Pred}
        → (mp : ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
                  {P} {Pr : Proc γ δ} {s}
              → L Γ Δ P Pr s → L′ Γ Δ P Pr s)
        → ∀ {γ δ} (Γ : Vec Sort γ) (Δ : Vec (State G) δ)
            (P : Part) (Pr : Proc γ δ) (s : State G)
        → Direct L Γ Δ P Pr s → Direct L′ Γ Δ P Pr s
      direct-mono mp Γ Δ P (Q ! i < E >∙ Pr) s (S , t , etd , gr , a) =
        S , t , etd , gr , mp a
      direct-mono mp Γ Δ Q (Σ_？[_]·_ P {I = I} S Br) s (rw , all) =
        rw , All.map (λ f {j} {U} eq → mp (f eq)) all
      direct-mono mp Γ Δ P (ifp E then Pr else Pr′) s (etd , a , a′) =
        etd , mp a , mp a′
      direct-mono mp Γ Δ P (rec Pr) s (mg , a) = mg , mp a
      direct-mono mp Γ Δ P (v X) s eq = eq
      direct-mono mp Γ Δ P ∅ s ¬in = ¬in

      -- `SemSkipP` is monotone (§3.2, S2): a bigger leaf set is easier to
      -- reach and harder to avoid.
      reachLP-mono :
        {L L′ : State G → Set} → (∀ {u} → L u → L′ u)
        → ∀ {t} → ReachLP L t → ReachLP L′ t
      reachLP-mono mp (ℓ , path , Lℓ) = ℓ , path , mp Lℓ

      semSkipP-mono :
        {L L′ : State G → Set} → (∀ {u} → L u → L′ u)
        → ∀ {P s} → SemSkipP L P s → SemSkipP L′ P s
      semSkipP-mono mp sem t (pvp′ , ¬L′t) =
        let na×r = sem t
                     ( pathViaP-map G (λ _ ¬L′u Lu → ¬L′u (mp Lu)) pvp′
                     , λ Lt → ¬L′t (mp Lt) )
        in proj₁ na×r , reachLP-mono mp (proj₂ na×r)

      alg-mono :
        ∀ {k k′} → k ≤ k′
        → ∀ {γ δ} {Γ : Vec Sort γ} {Δ : Vec (State G) δ}
            {P} {Pr : Proc γ δ} {s}
        → Alg k Γ Δ P Pr s → Alg k′ Γ Δ P Pr s
      alg-mono z≤n ()
      alg-mono (s≤s le) {Γ = Γ} {Δ} {P} {Pr} {s} (inj₁ d) =
        inj₁ (direct-mono (alg-mono le) Γ Δ P Pr s d)
      alg-mono (s≤s le) (inj₂ (inj₁ (r , inc , a))) =
        inj₂ (inj₁ (r , inc , alg-mono le a))
      alg-mono (s≤s le) (inj₂ (inj₂ sem)) =
        inj₂ (inj₂ (semSkipP-mono (alg-mono le) sem))

      -- Success is a declarative derivation. Until skip/cycle is synthesised,
      -- `nothing` is inconclusive rather than evidence of non-typability.

      checkClosed :
        ∀ {γ}
        → (Γ : Vec Sort γ)
        → (P : Part)
        → (Pr : Proc γ 0)
        → (s : State G)
        → Maybe (Γ & [] ⊢p P ◂ Pr ∶ s)
      checkClosed Γ P Pr = check Γ [] P Pr

      checkSession :
        (M : Session)
        → (s : State G)
        → Maybe (⊢s M ∶ s)
      checkSession M s =
        allParticipants λ P →
          checkClosed [] P (M [ P ]s) s
        where
          allParticipants :
            ∀ {n} {A : Fin n → Set}
            → (∀ i → Maybe (A i))
            → Maybe (∀ i → A i)
          allParticipants {n = 0} checked =
            just λ ()
          allParticipants {n = suc n} checked
            with checked F.zero
            | allParticipants (λ i → checked (F.suc i))
          ... | just at-zero | just at-suc =
            just λ where
              F.zero → at-zero
              (F.suc i) → at-suc i
          ... | _ | _ = nothing

    ProcessTyping :
      (G : Graph)
      → WellBehaved (graphTheory G)
      → ∀ {γ}
      → Vec Sort γ
      → Common.Part
      → Syntax.Proc γ 0
      → State G
      → Set
    ProcessTyping G wb Γ P Pr s =
      let module T = Typing.MPST wb
      in T._&_⊢p_∶_ Γ [] (Syntax._◂_ P Pr) s

    record CheckedProcess
      (G : Graph)
      {γ : ℕ}
      (Γ : Vec Sort γ)
      (P : Common.Part)
      (Pr : Syntax.Proc γ 0)
      (s : State G)
      : Set₁
      where
      constructor checkedProcess
      field
        wellBehaved : WellBehaved (graphTheory G)
        derivation  : ProcessTyping G wellBehaved Γ P Pr s

    checkProcess :
      ∀ {γ}
      → (G : Graph)
      → (Γ : Vec Sort γ)
      → (P : Common.Part)
      → (Pr : Syntax.Proc γ 0)
      → (s : State G)
      → Maybe (CheckedProcess G Γ P Pr s)
    checkProcess G Γ P Pr s with wellBehaved? G
    ... | no _ = nothing
    ... | yes wb with GraphChecker.checkClosed G wb Γ P Pr s
    ...   | just td = just (checkedProcess wb td)
    ...   | nothing = nothing

    checkRootedProcess :
      ∀ {γ}
      → (R : RootedGraph)
      → (Γ : Vec Sort γ)
      → (P : Common.Part)
      → (Pr : Syntax.Proc γ 0)
      → Maybe
          (CheckedProcess
            (underlying R) Γ P Pr (initial R))
    checkRootedProcess R Γ P Pr =
      checkProcess (underlying R) Γ P Pr (initial R)

    SessionTyping :
      (G : Graph)
      → WellBehaved (graphTheory G)
      → Syntax.Session
      → State G
      → Set
    SessionTyping G wb M s =
      let module T = Typing.MPST wb
      in T.⊢s_∶_ M s

    record CheckedSession
      (G : Graph)
      (M : Syntax.Session)
      (s : State G)
      : Set₁
      where
      constructor checkedSession
      field
        wellBehaved : WellBehaved (graphTheory G)
        derivation  : SessionTyping G wellBehaved M s

    checkSession :
      (G : Graph)
      → (M : Syntax.Session)
      → (s : State G)
      → Maybe (CheckedSession G M s)
    checkSession G M s with wellBehaved? G
    ... | no _ = nothing
    ... | yes wb with GraphChecker.checkSession G wb M s
    ...   | just td = just (checkedSession wb td)
    ...   | nothing = nothing

    checkRootedSession :
      (R : RootedGraph)
      → (M : Syntax.Session)
      → Maybe (CheckedSession (underlying R) M (initial R))
    checkRootedSession R M =
      checkSession (underlying R) M (initial R)
