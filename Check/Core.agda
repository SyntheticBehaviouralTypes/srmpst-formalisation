{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Vec using (Vec; []; lookup)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)

open import Definitions.Behav using (WellBehaved)
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

  -- Checking mode: decide `Γ ⊢e E ∶ S` for a *given* `S` directly, by
  -- recursion on `E`.
  checkValue : ∀ V S → Dec (⊢v V ∶ S)
  checkValue (v/bool _) s/bool = yes tv/bool
  checkValue (v/bool _) s/nat  = no λ ()
  checkValue (v/bool _) s/unit = no λ ()
  checkValue (v/nat _)  s/bool = no λ ()
  checkValue (v/nat _)  s/nat  = yes tv/nat
  checkValue (v/nat _)  s/unit = no λ ()
  checkValue v/unit     s/bool = no λ ()
  checkValue v/unit     s/nat  = no λ ()
  checkValue v/unit     s/unit = yes tv/unit

  checkExpression :
    ∀ {γ} (Γ : Vec Sort γ) (E : Exp γ) (S : Sort)
    → Dec (Γ ⊢e E ∶ S)
  checkExpression Γ (val V) S =
    map′ te/val (λ { (te/val tv) → tv }) (checkValue V S)
  checkExpression Γ (minus1 E) s/nat =
    map′ te/minus1 (λ { (te/minus1 e) → e }) (checkExpression Γ E s/nat)
  checkExpression Γ (minus1 E) s/bool = no λ ()
  checkExpression Γ (minus1 E) s/unit = no λ ()
  checkExpression Γ (is-zero E) s/bool =
    map′ te/is-zero (λ { (te/is-zero e) → e }) (checkExpression Γ E s/nat)
  checkExpression Γ (is-zero E) s/nat  = no λ ()
  checkExpression Γ (is-zero E) s/unit = no λ ()
  checkExpression Γ (var x) S with lookup Γ x ≟Sort S
  ... | yes refl = yes te/var
  ... | no ≢S    = no λ { te/var → ≢S refl }

  module Processes (N : ℕ) where

    module Common = Definitions.Common N
    module Syntax = Definitions.Proc N

    open import Definitions.Graph.Core N using (Graph; State; graphTheory)

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
