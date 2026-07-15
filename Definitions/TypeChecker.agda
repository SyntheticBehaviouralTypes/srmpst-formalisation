{-# OPTIONS --guardedness #-}

-- Public entry point for the decidable type checker: exactly two functions
-- (`typecheck`, `typecheckSession`), the well-behaved-graph subtype
-- (`WBGraph`) and its smart constructor (`buildG`), and everything needed to
-- call them — no module to instantiate first. The participant count `N` is
-- shared, unqualified, across this whole file via an anonymous parameterised
-- module (`module _ {N} where`); from the outside it surfaces as an ordinary
-- implicit argument on each name below, inferred from the graph passed in,
-- never as a module the caller has to apply.

module Definitions.TypeChecker where

open import Data.Nat using (ℕ)

open import Definitions.TypeChecker.Core public
  using (TypedExpression; valueTyped; inferExpression)

import Definitions.TypeChecker.Complete as Comp

module _ {N : ℕ} where
  open import LTS.Algebra N public
    using (RootedGraph; underlying; initial; OpenGraph)
  open import Definitions.Common N public
    using (Part)
  open import Definitions.Proc N public
    using (Proc; Session)
  open Comp N public
    using (WBGraph; buildG; typecheck; typecheckSession)
