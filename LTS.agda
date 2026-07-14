{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)

module LTS (N : ℕ) where

  open import LTS.Action N public
  open import LTS.Core N public
  open import LTS.Algebra N public
  open import LTS.Reachability N public
  open import LTS.Bisimulation N public
  open import LTS.WellBehaved N public
  open import LTS.Decision N public
