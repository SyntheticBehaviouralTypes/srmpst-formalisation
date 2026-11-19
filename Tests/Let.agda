{-# OPTIONS --guardedness #-}

-- `let x = e in P` (POPL 2026's ⊢-Let), through the checker.
--
--        A⟶B # 0<nat>
--   s₀ ──────────────────► ended
--
-- `A` names its payload with a `let`; `B` names a test on what it
-- received.  The variable of a `let` has its expression's sort: the
-- controls are rejected because a `let` gives the wrong sort.

module Tests.Let where

open import Definitions.Expr.Syntax
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Nullary.Decidable using (from-yes; from-no)

open import Definitions.Expr using (s/nat; is-zero)
open import Check hiding (base; _∥_; _⨾_)

open import Definitions.Graph.Algebra 2 renaming (var to gvar)
open import Data.Fin.Subset using (⁅_⁆)
open import Definitions.Actions 2
open import Definitions.Proc 2 hiding (rec; _⇐_？·_)
open import Definitions.Proc.Syntax 2
open import Utils.Branch using (⟪_⟫; _↦_; _∣_)

A B : Fin 2
A = 0F
B = 1F

value : ℕ
value = 0

g : OpenGraph 0
g = A ⟶ ⁅ B ⁆ # value < s/nat > ∙ end

wbg : WBGraph {N = 2}
wbg = buildG g {p = tt}

open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_)

check : (M : Over.Session singletons) → Dec (⊢s[ singletons ] M ∶ initial (proj₁ wbg))
check M = typecheckSession wbg singletons M

-- ══════════════════════════════════════════════════════════════════════
--  Accepted
-- ══════════════════════════════════════════════════════════════════════

p/A : Proc 0 0
p/A = letp x ≔ 1 in′ (A ⇒ ⁅ B ⁆ ! value < x >∙ ∅)

p/B : Proc 0 0
p/B =
  B ⇐ A ？· ⟪ value ⟨ x ⟩ ↦ letp y ≔ is-zero x in′ (ifp y then ∅ else ∅) ⟫

well-typed : ⊢s[ singletons ] (p/A v∷ p/B v∷ v[]) ∶ initial (proj₁ wbg)
well-typed = from-yes (check (p/A v∷ p/B v∷ v[]))

-- ══════════════════════════════════════════════════════════════════════
--  Rejected: the `let`'s sort is wrong for its use
-- ══════════════════════════════════════════════════════════════════════

-- `x` is a `bool`; the step sends a `nat`.
p/A′ : Proc 0 0
p/A′ = letp x ≔ true in′ (A ⇒ ⁅ B ⁆ ! value < x >∙ ∅)

wrong-payload : ¬ (⊢s[ singletons ] (p/A′ v∷ p/B v∷ v[]) ∶ initial (proj₁ wbg))
wrong-payload = from-no (check (p/A′ v∷ p/B v∷ v[]))

-- `y` is a `nat`; `if` needs a `bool`.
p/B′ : Proc 0 0
p/B′ = B ⇐ A ？· ⟪ value ⟨ x ⟩ ↦ letp y ≔ x in′ (ifp y then ∅ else ∅) ⟫

wrong-guard : ¬ (⊢s[ singletons ] (p/A v∷ p/B′ v∷ v[]) ∶ initial (proj₁ wbg))
wrong-guard = from-no (check (p/A v∷ p/B′ v∷ v[]))
