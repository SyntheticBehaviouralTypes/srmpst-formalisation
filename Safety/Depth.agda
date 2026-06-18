{-# OPTIONS --guardedness #-}

-- A measure on processes that τ steps decrease.

open import Data.Nat using (ℕ; _<_; _⊔_; s≤s; suc)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤n⊔o; m≤n⇒m≤o⊔n)
open import Data.Fin using (zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Safety.Depth (N : ℕ) where

  open import Definitions.Proc N
  open Subst

  τ-depth/proc :
    ∀ {γ δ}
    → Proc γ δ
    → ℕ
  τ-depth/proc (_ ⇒ _ ! _ < _ >∙ _) =
    0
  τ-depth/proc (_ ⇐ _ ？· _) =
    0
  τ-depth/proc (ifp _ then Pr else Pr′) =
    suc (τ-depth/proc Pr ⊔ τ-depth/proc Pr′)
  τ-depth/proc (rec Pr) =
    suc (τ-depth/proc Pr)
  τ-depth/proc (v _) =
    0
  τ-depth/proc ∅ =
    0

  τ-depth/message-subst :
    ∀ {γ δ X}
      {Pr  : Proc γ (suc δ)}
      {Pr′ : Proc γ δ}
    → MessageGuarded Pr
    → τ-depth/proc ([ Pr′ / X ]pr Pr) ≡ τ-depth/proc Pr
  τ-depth/message-subst mg/send =
    refl
  τ-depth/message-subst mg/recv =
    refl
  τ-depth/message-subst {X = X} {Pr′ = Pr′} (mg/if mg₁ mg₂)
    rewrite τ-depth/message-subst {X = X} {Pr′ = Pr′} mg₁
          | τ-depth/message-subst {X = X} {Pr′ = Pr′} mg₂ =
    refl

  τ-depth/if-then :
    ∀ {γ δ E}
      {Pr Pr′ : Proc γ δ}
    → τ-depth/proc Pr < τ-depth/proc (ifp E then Pr else Pr′)
  τ-depth/if-then =
    s≤s (m≤n⇒m≤n⊔o _ ≤-refl)

  τ-depth/if-else :
    ∀ {γ δ E}
      {Pr Pr′ : Proc γ δ}
    → τ-depth/proc Pr′ < τ-depth/proc (ifp E then Pr else Pr′)
  τ-depth/if-else =
    s≤s (m≤n⇒m≤o⊔n _ ≤-refl)

  τ-depth/unfold<rec :
    ∀ {Pr : Proc 0 1}
    → MessageGuarded Pr
    → τ-depth/proc (unfold/proc Pr) < τ-depth/proc (rec Pr)
  τ-depth/unfold<rec {Pr} guarded
    rewrite τ-depth/message-subst {X = zero} {Pr′ = rec Pr} guarded =
    ≤-refl
