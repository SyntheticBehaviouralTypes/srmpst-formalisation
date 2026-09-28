{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Definitions.Typing

module Safety
  {N : ℕ} {B : BTheory N} (wb : WellBehaved B) (sync : Synchronous B) where

open import Safety.Preservation wb sync public
open import Safety.Progress wb sync public
open import Safety.Termination wb sync public
