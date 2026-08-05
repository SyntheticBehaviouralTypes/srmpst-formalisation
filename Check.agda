{-# OPTIONS --guardedness #-}

-- The decidable type checker's public surface — the replacement for the
-- deleted `Definitions/TypeChecker.agda`, with the same names, so callers
-- change only which module they import.
--
-- As before, the participant count `N` is shared, unqualified, via an
-- anonymous parameterised module (`module _ {N} where`): from the outside
-- every name below carries `N` as an ordinary implicit argument, inferred
-- from the graph or net passed in, never as a module the caller has to
-- apply.
--
-- Re-exports at most what lives under `Check/` itself.  `RootedGraph`/
-- `Part`/`Proc`/`Session` belong to `Definitions.Graph.Algebra`/
-- `Definitions.Common`/`Definitions.Proc`; re-exporting them here would
-- make `Definitions` ambiguous wherever it is opened alongside this
-- module, so callers needing to name them import them directly.

module Check where

open import Data.Nat using (ℕ)

open import Check.Core public
  using (TypedExpression; valueTyped; inferExpression; checkExpression)

import Check.Core as Core
import Check.Graph as Gph
import Check.Network as Net

module _ {N : ℕ} where
  open Core.Processes N public
    using (ProcessTyping; SessionTyping)
  open Gph N public
    using (WBGraph; buildG; wb-of; typecheck; typecheckSession)
  open Net N public
    using ( WBNet; base; _∥_; _⨾_
          ; netWB; wb-net; typecheckNet; typecheckSessionNet )
