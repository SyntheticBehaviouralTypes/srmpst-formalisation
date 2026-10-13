-- Literal expressions: `0`, `1`, … for `val (v/nat n)`, and `true`,
-- `false`, `unit`.  Import this first: it brings `FROMNAT` into scope, so
-- from here on every numeral is overloaded, `ℕ` included (`number/ℕ`).
-- `true`/`false` clash with `Data.Bool`'s; qualify those (`Bool.true`).

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
import Data.Bool as Bool
open import Agda.Builtin.FromNat using (Number)

open import Definitions.Expr using (Exp; val; v/nat; v/bool; v/unit)

module Definitions.Expr.Syntax where

  open import Agda.Builtin.FromNat public using (fromNat)

  instance
    number/ℕ : Number ℕ
    number/ℕ = record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }

    number/exp : ∀ {γ} → Number (Exp γ)
    number/exp = record { Constraint = λ _ → ⊤ ; fromNat = λ n → val (v/nat n) }

    -- discharges both `Constraint`s
    literal : ⊤
    literal = tt

  pattern true  = val (v/bool Bool.true)
  pattern false = val (v/bool Bool.false)
  pattern unit  = val v/unit
