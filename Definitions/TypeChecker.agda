{-# OPTIONS --guardedness #-}

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
  renaming (_≟_ to _≟Fin_)
import Data.Fin as F
import Data.Fin.Properties as Fin
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any as Any
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _*_)
import Data.Nat.Properties as Nat
open import Data.Product
  using (_×_; Σ-syntax; _,_; proj₁)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (T?)

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
    → Maybe (TypedExpression Γ E)
  inferExpression Γ (val V) =
    just (sort/value V , te/val (valueTyped V))
  inferExpression Γ (minus1 E) with inferExpression Γ E
  ... | just (s/nat , td) = just (s/nat , te/minus1 td)
  ... | just (s/bool , _) = nothing
  ... | just (s/unit , _) = nothing
  ... | nothing = nothing
  inferExpression Γ (is-zero E) with inferExpression Γ E
  ... | just (s/nat , td) = just (s/bool , te/is-zero td)
  ... | just (s/bool , _) = nothing
  ... | just (s/unit , _) = nothing
  ... | nothing = nothing
  inferExpression Γ (var x) =
    just (lookup Γ x , te/var)

  module Processes (N : ℕ) where

    module Common = Definitions.Common N
    module Syntax = Definitions.Proc N

    open import LTS.Algebra N
      using (RootedGraph; underlying; initial)
    open import LTS.Action N
    open import LTS.Bisimulation N
    open import LTS.Core N
    open import LTS.Decision N using (wellBehaved?)

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
        → Maybe (MessageGuarded Pr)
      messageGuarded? (_ ! _ < _ >∙ _) = just mg/send
      messageGuarded? (Σ _ ？[ _ ]· _) = just mg/recv
      messageGuarded? (ifp _ then Pr else Pr′)
        with messageGuarded? Pr | messageGuarded? Pr′
      ... | just guarded | just guarded′ =
        just (mg/if guarded guarded′)
      ... | _ | _ = nothing
      messageGuarded? (rec _) = nothing
      messageGuarded? (v _) = nothing
      messageGuarded? ∅ = nothing

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
        → Maybe (ActionAt α xs)
      findAction α [] = nothing
      findAction α ((β , t) ∷ xs) with β ≟Action α
      ... | yes refl = just (t , Any.here refl)
      ... | no _ with findAction α xs
      ...   | just (u , member) = just (u , Any.there member)
      ...   | nothing = nothing

      findStep :
        ∀ s α
        → Maybe
            (Σ[ t ∈ State G ]
              BTheory._-<_>->_ (graphTheory G) s α t)
      findStep s α with findAction α (edges G s)
      ... | just (t , member) =
        just (t , listed⇒step {G = G} member)
      ... | nothing = nothing

      RecvWitness :
        Part → Part → ℕ → List (Edge (size G)) → Set
      RecvWitness P Q I xs =
        Σ[ j ∈ Fin (suc I) ]
        Σ[ U ∈ Sort ]
        Σ[ t ∈ State G ]
          ((P ⟶ Q # j < U >) , t) ∈ xs

      findRecv :
        (P Q : Part) (I : ℕ) (xs : List (Edge (size G)))
        → Maybe (RecvWitness P Q I xs)
      findRecv P Q I [] = nothing
      findRecv P Q I ((α , t) ∷ xs)
        with matchRecv? P Q I α
      ... | yes (j , U , refl) =
        just (j , U , t , Any.here refl)
      ... | no _ with findRecv P Q I xs
      ...   | just (j , U , u , member) =
        just (j , U , u , Any.there member)
      ...   | nothing = nothing

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

      GloballyInactive : Part → Set
      GloballyInactive P =
        ∀ s → All.All (λ edge → P ∉α proj₁ edge) (edges G s)

      -- Global inactivity is stronger than absence from one reachable cone.
      -- It keeps terminal checking independent of reachability computation.
      globallyInactive? :
        (P : Part) → Dec (GloballyInactive P)
      globallyInactive? P =
        Fin.all? λ s →
          All.all?
            (λ edge → _∉α?_ P (proj₁ edge))
            (edges G s)

      inactive⇒notIn :
        ∀ {P} → GloballyInactive P → ∀ {s} → ¬ P ∈T s
      inactive⇒notIn inactive {s} (in/α gr P∈α) =
        ∉c→¬∈c
          (All.lookup (inactive s) (step⇒listed {G = G} gr))
          P∈α
      inactive⇒notIn inactive (in/later _ later) =
        inactive⇒notIn inactive later

      checkDirect : CheckFunction → CheckFunction
      checkDirect recur Γ Δ P
        (Q ! i < E >∙ Pr) s
        with inferExpression Γ E
      ... | nothing = nothing
      ... | just (S , etd) with
        findStep s (P ⟶ Q # i < S >)
      ...   | nothing = nothing
      ...   | just (t , gr) with
        recur Γ Δ P Pr t
      ...     | just td = just (t/send gr etd td)
      ...     | nothing = nothing
      checkDirect recur Γ Δ Q
        (Σ P ？[ S ]· Br) s
        with findRecv P Q _ (edges G s)
        | checkContinuations
            recur Γ Δ P Q Br (edges G s)
      ... | nothing | _ = nothing
      ... | _ | nothing = nothing
      ... | just (_ , _ , _ , selected) | just checked =
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
      ... | just (s/bool , etd) | just td | just td′ =
        just (t/if etd td td′)
      ... | _ | _ | _ = nothing
      checkDirect recur Γ Δ P (rec Pr) s
        with messageGuarded? Pr
        | recur Γ (s ∷ Δ) P Pr s
      ... | just guarded | just td = just (t/rec guarded td)
      ... | _ | _ = nothing
      checkDirect recur Γ Δ P (v X) s
        with T? (bisim? G (lookup Δ X) s)
      ... | yes related =
        just (t/var (sound (bisimulationCorrect G) related))
      ... | no _ = nothing
      checkDirect recur Γ Δ P ∅ s
        with globallyInactive? P
      ... | yes inactive = just (t/end (inactive⇒notIn inactive))
      ... | no _ = nothing

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
        → Maybe (Incoming P s xs)
      findIncoming P s [] = nothing
      findIncoming P s ((α , t) ∷ xs)
        with t ≟Fin s | _∉α?_ P α
      ... | yes refl | yes P∉α =
        just (α , Any.here refl , P∉α)
      ... | _ | _ with findIncoming P s xs
      ...   | just (α , member , P∉α) =
        just (α , Any.there member , P∉α)
      ...   | nothing = nothing

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
      ... | nothing = nothing
      ... | just (_ , member , P∉α) with recur Γ Δ P Pr r
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

      allMaybe :
        ∀ {A : Set} {F : A → Set}
        → (∀ x → Maybe (F x))
        → (xs : List A)
        → Maybe (All.All F xs)
      allMaybe check [] = just All.[]
      allMaybe check (x ∷ xs)
        with check x | allMaybe check xs
      ... | just px | just pxs = just (px All.∷ pxs)
      ... | _ | _ = nothing

      first :
        ∀ {A : Set} (xs : List A)
        → Maybe (Σ[ x ∈ A ] x ∈ xs)
      first [] = nothing
      first (x ∷ xs) = just (x , Any.here refl)

      InactiveAt : Part → State G → Set
      InactiveAt P s =
        All.All (λ edge → P ∉α proj₁ edge) (edges G s)

      inactiveAt? :
        (P : Part) (s : State G) → Dec (InactiveAt P s)
      inactiveAt? P s =
        All.all?
          (λ edge → _∉α?_ P (proj₁ edge))
          (edges G s)

      checkSkipStep :
        ∀ {γ δ ξ}
        → (Γ : Vec Sort γ)
        → (Δ : Vec (State G) δ)
        → (Ξ : Vec (State G) ξ)
        → (P : Part)
        → (Pr : Proc γ δ)
        → (s : State G)
        → (∀ t →
            Maybe
              (Γ & Δ & s ∷ Ξ
                ⊢skip[ prod ] P ◂ Pr ∶ t))
        → Maybe
            (Γ & Δ & Ξ ⊢skip[ prod ] P ◂ Pr ∶ s)
      checkSkipStep Γ Δ Ξ P Pr s next
        with first (edges G s)
        | inactiveAt? P s
        | allMaybe
            (λ where (_ , t) → next t)
            (edges G s)
      ... | just (_ , selected) | yes inactive | just checked =
        just
          (skip/step
            (listed⇒step {G = G} selected)
            (λ gr →
              All.lookup
                inactive
                (step⇒listed {G = G} gr))
            (λ gr →
              prod ,
              All.lookup
                checked
                (step⇒listed {G = G} gr))
            refl)
      ... | _ | _ | _ = nothing

      -- Cyclic skip proofs additionally require synthesising nonprod leaves.
      -- This checker currently constructs finite productive skip trees only.
      checkSkip :
        ∀ {γ δ ξ}
        → ℕ
        → CheckFunction
        → (Γ : Vec Sort γ)
        → (Δ : Vec (State G) δ)
        → (Ξ : Vec (State G) ξ)
        → (P : Part)
        → (Pr : Proc γ δ)
        → (s : State G)
        → Maybe
            (Γ & Δ & Ξ ⊢skip[ prod ] P ◂ Pr ∶ s)
      checkSkip 0 recur Γ Δ Ξ P Pr s = nothing
      checkSkip (suc fuel) recur Γ Δ Ξ P Pr s
        with recur Γ Δ P Pr s
      ... | just td = just (skip/main td)
      ... | nothing =
        checkSkipStep Γ Δ Ξ P Pr s λ t →
          checkSkip fuel recur Γ Δ (s ∷ Ξ) P Pr t

      checkClosure : CheckFunction → CheckFunction
      checkClosure recur Γ Δ P Pr s
        with checkPredecessors recur Γ Δ P Pr s (states G)
      ... | just td = just td
      ... | nothing with
        checkSkip (suc (size G)) recur Γ Δ [] P Pr s
      ...   | just std = just (t/skip std)
      ...   | nothing = nothing

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
