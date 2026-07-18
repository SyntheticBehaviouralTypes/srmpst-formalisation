{-# OPTIONS --guardedness #-}

-- Public entry point for the decidable type checker: the graph-level
-- functions (`typecheck`, `typecheckSession`) with the well-behaved-graph
-- subtype (`WBGraph`) and its smart constructor (`buildG`), and the
-- network-level functions (`typecheckNet`, `typecheckSessionNet`) with the
-- compositional certificate (`WBNet`, written with the same constructor
-- syntax as the `Net` itself) — no module to instantiate first. The
-- participant count `N` is shared, unqualified, across this whole file via
-- an anonymous parameterised module (`module _ {N} where`); from the
-- outside it surfaces as an ordinary implicit argument on each name below,
-- inferred from the graph/net passed in, never as a module the caller has
-- to apply.
--
-- Re-exports at most what lives under `Definitions/TypeChecker/` itself —
-- `RootedGraph`/`Part`/`Proc`/`Session`/etc. belong to `LTS.Algebra`/
-- `Definitions.Common`/`Definitions.Proc` and are not re-exported here;
-- callers needing to name those types import them directly.

module Definitions.TypeChecker where

open import Data.Nat using (ℕ)

open import Definitions.TypeChecker.Core public
  using (TypedExpression; valueTyped; inferExpression)

import Definitions.TypeChecker.Core as Core
import Definitions.TypeChecker.Completeness as Comp
import Definitions.TypeChecker.Network as Net

module _ {N : ℕ} where
  open Core.Processes N public
    using (ProcessTyping; SessionTyping)
  open Comp N public
    using (WBGraph; buildG; wb-of; typecheck; typecheckSession)
  open Net N public
    using ( WBNet; base; _∥_; _⨾_
          ; netWB; wb-net; typecheckNet; typecheckSessionNet )
