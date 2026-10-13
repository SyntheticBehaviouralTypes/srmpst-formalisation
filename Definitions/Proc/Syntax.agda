{-# OPTIONS --guardedness #-}

-- Surface syntax for processes, over `Definitions.Proc`'s constructors:
--
--   rec X · P                    binds `X` (`Utils.Binder`), not `v 0F`;
--   R ⇐ P ？· ⟪ l₁ ↦ P₁          one branch per label of the receive, in
--            ∣ l₂ ⟨ x ⟩ ↦ P₂     any order (`Utils.Branch`); `⟨ x ⟩`
--            ⟫                   names the received value (not `var 0F`).
--
-- Open `Definitions.Proc` hiding `rec` and `_⇐_？·_` next to this.

open import Data.Bool using (T)
open import Data.Fin using (Fin)
open import Data.Maybe using (is-just)
open import Data.Nat using (ℕ; suc; _≤?_)
open import Relation.Nullary.Decidable using (True)

open import Definitions.Expr using (Exp; var)
open import Utils.Branch using (Branches; Closes; _↦_; byLabel; fromJust)
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

  -- The branches of a receive stay branches; `_⇐_？·_` checks them.
  instance
    closes/recv :
      ∀ {n γ δ}
      → Closes (Fin n) (Proc γ δ) (Branches (Fin n) (Proc γ δ))
    closes/recv = record { close = λ bs → bs }

  -- `l ⟨ x ⟩ ↦ P`: the branch for label `l`, its value named `x`.
  Val : ℕ → Set
  Val γ = ∀ {m} {p : True (suc γ ≤? m)} → Exp m

  receiving :
    ∀ {n γ δ}
    → Fin n → (Val γ → Proc (suc γ) δ) → Branches (Fin n) (Proc (suc γ) δ)
  receiving {γ = γ} l body = l ↦ body (λ {m} {p} → var (bound γ p))

  infixr 4 receiving
  syntax receiving l (λ x → P) = l ⟨ x ⟩ ↦ P

  infixr 8 _⇐_？·_

  _⇐_？·_ :
    ∀ {γ δ I}
    → Part → Part
    → (bs : Branches (Fin (suc I)) (Proc (suc γ) δ))
    → {every : T (is-just (byLabel bs))}
    → Proc γ δ
  (R ⇐ P ？· bs) {every} = R Core.⇐ P ？· fromJust (byLabel bs) every
