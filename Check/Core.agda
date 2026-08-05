{-# OPTIONS --guardedness #-}

open import Data.Fin using (Fin)
  renaming (_≟_ to _≟Fin_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any as Any
open import Data.Nat using (ℕ; suc)
import Data.Nat.Properties as Nat
open import Data.Product
  using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; ≢-sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable
  using (T?)

open import Definitions.Behav using (BTheory; WellBehaved)
open import Definitions.Expr
import Definitions.Common
import Definitions.Proc
import Definitions.Typing as Typing

module Check.Core where

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

  -- Checking mode: decide `Γ ⊢e E ∶ S` for a *given* `S` directly, instead
  -- of inferring `E`'s sort and having the caller cross-check it against
  -- `S` itself (which is all `inferExpression` alone would let a caller
  -- do). Built on `inferExpression` — no new traversal of `E`, just one
  -- extra sort comparison at the end via the existing disequality lemmas.
  checkExpression :
    ∀ {γ} (Γ : Vec Sort γ) (E : Exp γ) (S : Sort)
    → Dec (Γ ⊢e E ∶ S)
  checkExpression Γ E S with inferExpression Γ E
  ... | no ¬wt =
    no λ etd → ¬wt (S , etd)
  ... | yes (s/bool , etd) with S
  ...   | s/bool = yes etd
  ...   | s/nat  = no λ etd′ → s/nat≢s/bool  (⊢e-unique etd′ etd)
  ...   | s/unit = no λ etd′ → s/unit≢s/bool (⊢e-unique etd′ etd)
  checkExpression Γ E S | yes (s/nat , etd) with S
  ...   | s/bool = no λ etd′ → ≢-sym s/nat≢s/bool (⊢e-unique etd′ etd)
  ...   | s/nat  = yes etd
  ...   | s/unit = no λ etd′ → ≢-sym s/nat≢s/unit (⊢e-unique etd′ etd)
  checkExpression Γ E S | yes (s/unit , etd) with S
  ...   | s/bool = no λ etd′ → ≢-sym s/unit≢s/bool (⊢e-unique etd′ etd)
  ...   | s/nat  = no λ etd′ → s/nat≢s/unit (⊢e-unique etd′ etd)
  ...   | s/unit = yes etd

  module Processes (N : ℕ) where

    module Common = Definitions.Common N
    module Syntax = Definitions.Proc N

    open import Definitions.Graph.Algebra N
      using (RootedGraph; underlying; initial)
    open import Definitions.Graph.Action N
    open import Definitions.Graph.Bisimulation N
    open import Definitions.Graph.Core N
    open import Definitions.Graph.Decision N using (wellBehaved?)

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

      -- `P not-active-in t` (abstract form) decided through `InactiveAt`.
      na? : ∀ P t → Dec (P not-active-in t)
      na? P t with inactiveAt? P t
      ... | yes inact =
        yes λ gr → All.lookup inact (step⇒listed {G = G} gr)
      ... | no ¬inact =
        no λ na → ¬inact (All.tabulate λ mem → na (listed⇒step {G = G} mem))

      -- decide `~` on states via the bisimulation checker
      bisim?~ : ∀ x y → Dec (BTheory._~_ (graphTheory G) x y)
      bisim?~ x y with T? (bisim? G x y)
      ... | yes b = yes (sound (bisimulationCorrect G) b)
      ... | no ¬b = no λ r → ¬b (complete (bisimulationCorrect G) r)

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
