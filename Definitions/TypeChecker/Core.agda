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
open import Relation.Nullary.Decidable
  using (T?; ⌊_⌋; toWitness; fromWitness; _×-dec_; _⊎-dec_; _→-dec_; ¬?)

open import Definitions.Behav using (BTheory; WellBehaved)
open import Definitions.Expr
import Definitions.Common
import Definitions.Proc
import Definitions.Typing as Typing

module Definitions.TypeChecker.Core where

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

        -- `semSkip?` evaluates the leaf decider `L?` (typically an expensive
        -- recursive checker) exactly once per state, into a Bool table that
        -- every reachability sweep below consults by `lookup`.  The table is
        -- passed as a *bound argument* (`go okv`): Agda's evaluator shares
        -- argument thunks, so the single `tabulate` is forced once — whereas
        -- a module-level definition would be re-unfolded (hence the whole
        -- table re-computed) at every one of the O(size³) filter evaluations
        -- inside `reachVia?`.  `L?` is only ever re-run to extract a witness
        -- on a success path (`L?v`).
        semSkip? : ∀ s → Dec (SemSkipP L P s)
        semSkip? s =
          go (tabulate (λ t → not ⌊ L? t ⌋))
             (λ t → VecP.lookup∘tabulate (λ u → not ⌊ L? u ⌋) t)
          where
          go : (okv : Vec Bool (size G))
             → (eqv : ∀ t → lookup okv t ≡ not ⌊ L? t ⌋)
             → Dec (SemSkipP L P s)
          go okv eqv =
            Fin.all? (λ t → NL?′ t →-dec (na? P t ×-dec ReachL?′ t))
            where
            ok : State G → Bool
            ok t = lookup okv t

            -- ── the table and the predicate filter agree ──
            ¬L→Tok : ∀ {t} → ¬ L t → T (ok t)
            ¬L→Tok {t} ¬Lt with L? t | eqv t
            ... | yes Lt | _  = ⊥-elim (¬Lt Lt)
            ... | no  _  | eq = subst T (sym eq) tt

            Tok→¬L : ∀ {t} → T (ok t) → ¬ L t
            Tok→¬L {t} h with L? t | eqv t
            ... | yes _  | eq = ⊥-elim (subst T eq h)
            ... | no ¬Lt | _  = λ Lt → ¬Lt Lt

            ¬Tok→L : ∀ {t} → ¬ T (ok t) → L t
            ¬Tok→L {t} ¬∉ with L? t | eqv t
            ... | yes Lt | _  = Lt
            ... | no  _  | eq = ⊥-elim (¬∉ (subst T (sym eq) tt))

            -- decisions of `L`/`¬ L` through the table
            ¬L?v : ∀ t → Dec (¬ L t)
            ¬L?v t with T? (ok t)
            ... | yes ∉ = yes (Tok→¬L ∉)
            ... | no ¬∉ = no λ ¬Lt → ¬∉ (¬L→Tok ¬Lt)

            L?v : ∀ t → Dec (L t)
            L?v t with T? (ok t)
            ... | yes ∉ = no (Tok→¬L ∉)
            ... | no ¬∉ = yes (¬Tok→L ¬∉)

            -- decide the predicate-filtered reachability via the Bool
            -- fixed point over the shared table
            pathViaP?′ : ∀ a b → Dec (PathViaP G (λ u → ¬ L u) a b)
            pathViaP?′ a b with reachVia? G ok a b
            ... | yes (_ , pv) = yes (pathVia→pathViaP G (λ _ → Tok→¬L) pv)
            ... | no ¬pv =
              no λ pvp → ¬pv (pathViaP→pathVia G (λ _ → ¬L→Tok) pvp)

            NL?′ : ∀ t → Dec (NLP L s t)
            NL?′ t = pathViaP?′ s t ×-dec ¬L?v t

            ReachL?′ : ∀ t → Dec (ReachLP L t)
            ReachL?′ t =
              Fin.any? (λ ℓ → reachVia? G (λ _ → true) t ℓ ×-dec L?v ℓ)

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

      -- decide `~` on states via the bisimulation checker
      bisim?~ : ∀ x y → Dec (BTheory._~_ (graphTheory G) x y)
      bisim?~ x y with T? (bisim? G x y)
      ... | yes b = yes (sound (bisimulationCorrect G) b)
      ... | no ¬b = no λ r → ¬b (complete (bisimulationCorrect G) r)

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

    SessionTyping :
      (G : Graph)
      → WellBehaved (graphTheory G)
      → Syntax.Session
      → State G
      → Set
    SessionTyping G wb M s =
      let module T = Typing.MPST wb
      in T.⊢s_∶_ M s
