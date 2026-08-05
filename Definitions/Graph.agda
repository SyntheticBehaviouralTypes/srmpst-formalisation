{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)

module Definitions.Graph (N : ℕ) where

  open import Definitions.Graph.Action N public
  open import Definitions.Graph.Core N public
  open import Definitions.Graph.Algebra N public
  open import Definitions.Graph.Reachability N public
  open import Definitions.Graph.Bisimulation N public
  open import Definitions.Graph.WellBehaved N public
  open import Definitions.Graph.Decision N public
