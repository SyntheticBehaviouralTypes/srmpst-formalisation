{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Definitions.Typing

module Safety {N : ℕ} {B : BTheory N} (wb : WellBehaved B) where

open import Definitions.Typing.Norm wb public
open import Safety.Preservation wb public
open import Safety.Progress wb public
open import Safety.Termination wb public
