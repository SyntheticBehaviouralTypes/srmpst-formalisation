{-# OPTIONS --guardedness #-}

open import Data.Vec using (Vec; lookup)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)

open import Definitions.Expr

module Check.Core where

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
