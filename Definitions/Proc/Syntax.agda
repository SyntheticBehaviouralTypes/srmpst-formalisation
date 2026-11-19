{-# OPTIONS --guardedness #-}

-- Surface syntax for processes, over `Definitions.Proc`'s constructors:
--
--   rec X · P                    binds `X` (`Utils.Binder`), not `v 0F`;
--   R ⇐ P ？· ⟪ l₁ ↦ P₁          one branch per accepted label, in any
--            ∣ l₂ ⟨ x ⟩ ↦ P₂     order (`Utils.Branch`); `⟨ x ⟩` names
--            ⟫                   the received value (not `var 0F`);
--   letp x ≔ E in′ P             `let x = E in P`: names `E`'s value `x`.
--
-- Open `Definitions.Proc` hiding `rec` and `_⇐_？·_` next to this.

open import Data.Nat using (ℕ; suc; _≤?_)
open import Relation.Nullary.Decidable using (True)

open import Definitions.Expr using (Exp; var)
open import Utils.Branch using (Branches; Closes; _↦_; family)
open import Utils.Binder using (bound)

module Definitions.Proc.Syntax (N : ℕ) where

  open import Definitions.Common N using (Part)
  open import Definitions.Proc N as Core using (Proc; v)

  Rec : ℕ → Set
  Rec δ = ∀ {γ m} {p : True (suc δ ≤? m)} → Proc γ m

  rec : ∀ {γ δ} → (Rec δ → Proc γ (suc δ)) → Proc γ δ
  rec {δ = δ} body = Core.rec (body (λ {γ} {m} {p} → v (bound δ p)))

  -- `rec X · P`, as `rec X.P`; at the level of sends and receives.
  infixr 8 rec
  syntax rec (λ X → P) = rec X · P

  -- The branches of a receive stay branches; `_⇐_？·_` indexes them.
  instance
    closes/recv :
      ∀ {γ δ}
      → Closes ℕ (Proc γ δ) (Branches ℕ (Proc γ δ))
    closes/recv = record { close = λ bs → bs }

  -- `l ⟨ x ⟩ ↦ P`: the branch for label `l`, its value named `x`.
  Val : ℕ → Set
  Val γ = ∀ {m} {p : True (suc γ ≤? m)} → Exp m

  receiving :
    ∀ {γ δ}
    → ℕ → (Val γ → Proc (suc γ) δ) → Branches ℕ (Proc (suc γ) δ)
  receiving {γ = γ} l body = l ↦ body (λ {m} {p} → var (bound γ p))

  infixr 4 receiving
  syntax receiving l (λ x → P) = l ⟨ x ⟩ ↦ P

  -- `letp x ≔ E in′ P`, as `let x = E in P`.
  letting : ∀ {γ δ} → Exp γ → (Val γ → Proc (suc γ) δ) → Proc γ δ
  letting {γ = γ} E body = Core.letp E in′ body (λ {m} {p} → var (bound γ p))

  infixr 8 letting
  syntax letting E (λ x → P) = letp x ≔ E in′ P

  infixr 8 _⇐_？·_

  -- The labels of the branches are the receive's `𝓛`.
  _⇐_？·_ :
    ∀ {γ δ}
    → Part → Part
    → Branches ℕ (Proc (suc γ) δ)
    → Proc γ δ
  R ⇐ P ？· bs = R Core.⇐ P ？· family bs
