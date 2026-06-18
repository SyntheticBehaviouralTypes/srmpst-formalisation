{-# OPTIONS --guardedness #-}

-- The type checker's public surface; `N` is an implicit argument.  Only
-- names defined under `Check/` are re-exported, to avoid ambiguity with
-- `Definitions`.

module Check where

open import Data.Nat using (ℕ)

open import Check.Core public
  using (checkExpression)

import Check.Graph as Gph
import Check.Network as Net

module _ {N : ℕ} where
  open Gph N public
    using (WBGraph; buildG; wb-of; sync-of; typecheck; typecheckSession)
  open Net N public
    using ( WBNet; base; _∥_; _⨾_
          ; netWB; netSync; wb-net; sync-net; typecheckNet; typecheckSessionNet )
