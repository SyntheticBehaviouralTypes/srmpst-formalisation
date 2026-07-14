{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Definitions

module Safety {N : ℕ} {B : BTheory N} (BP : BT-Prop B) where

open import Safety.Head BP public
open import Safety.Preservation BP public
open import Safety.Progress BP public
open import Safety.Termination BP public
