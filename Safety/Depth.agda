{-# OPTIONS --guardedness #-}

-- A measure on processes that τ steps decrease.

open import Data.Nat using (ℕ; _<_; _⊔_; s≤s; suc)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤n⊔o; m≤n⇒m≤o⊔n)
open import Data.Fin using (zero) renaming (suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Definitions.Expr using (Exp; Value; val; weaken/exp)

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
  τ-depth/proc (letp _ in′ Pr) =
    suc (τ-depth/proc Pr)
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
  τ-depth/message-subst {X = X} {Pr′ = Pr′} (mg/let mg)
    rewrite τ-depth/message-subst {X = X} {Pr′ = weaken/proc/exp Pr′ zero} mg =
    refl
  τ-depth/message-subst {X = X} {Pr′ = Pr′} (mg/if mg₁ mg₂)
    rewrite τ-depth/message-subst {X = X} {Pr′ = Pr′} mg₁
          | τ-depth/message-subst {X = X} {Pr′ = Pr′} mg₂ =
    refl

  -- Substituting a value does not change the depth.
  τ-depth/subst-e :
    ∀ {γ δ} {E : Exp γ} {y} (Pr : Proc (suc γ) δ)
    → τ-depth/proc ([ E / y ]e Pr) ≡ τ-depth/proc Pr
  τ-depth/subst-e (_ ⇒ _ ! _ < _ >∙ _) = refl
  τ-depth/subst-e (_ ⇐ _ ？· _) = refl
  τ-depth/subst-e {E = E} {y} (letp _ in′ Pr) =
    cong suc (τ-depth/subst-e {E = weaken/exp E zero} {fsuc y} Pr)
  τ-depth/subst-e {E = E} {y} (ifp _ then Pr else Pr′) =
    cong suc
      (cong₂ _⊔_ (τ-depth/subst-e {E = E} {y} Pr)
                 (τ-depth/subst-e {E = E} {y} Pr′))
  τ-depth/subst-e {E = E} {y} (rec Pr) =
    cong suc (τ-depth/subst-e {E = E} {y} Pr)
  τ-depth/subst-e (v _) = refl
  τ-depth/subst-e ∅ = refl

  τ-depth/let :
    ∀ {E V} {Pr : Proc 1 0}
    → τ-depth/proc ([ val V / zero ]e Pr) < τ-depth/proc (letp E in′ Pr)
  τ-depth/let {V = V} {Pr}
    rewrite τ-depth/subst-e {E = val V} {zero} Pr =
    ≤-refl

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
