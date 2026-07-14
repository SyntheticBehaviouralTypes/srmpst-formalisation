{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Definitions

module SubstitutionProperties
  {N : ℕ} {B : BTheory N} (BP : BT-Prop B)
  where

open import Safety.Skip BP public
  using
    ( lookup/insert
    ; lookup/weaken-visited
    ; skip/weaken-visited
    ; skip/bisim
    ; transport-arg-ktd
    ; selected-step-mode
    ; td/bisim
    ; skip-leaf/bisim
    ; skip/unfold-cycle
    )
open import Typing.Substitution BP public
