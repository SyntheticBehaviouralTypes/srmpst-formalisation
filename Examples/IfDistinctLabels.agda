{-# OPTIONS --guardedness #-}
open import Data.Empty using (⊥-elim)
open import Data.Bool using (true)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Subset using (Subset ; _∈_ ; inside ; outside)
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup ; here ; there)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Definitions

-- if true then p ? {m1, m2} else p ? {m1, m3}
--
-- typed against the LTS   s0 --p→q:m1--> s1
module Examples.IfDistinctLabels where

  module Behaviour where
    open import Definitions.Common (2)
    open import Definitions.Actions (2)

    p q : Part
    p = zero
    q = suc zero

    -- Labels m1, m2 and m3 (positions 0, 1 and 2), all carrying unit
    S₃ : Vec Sort 3
    S₃ = s/unit ∷ s/unit ∷ s/unit ∷ []

    m1 m2 m3 : Fin 3
    m1 = zero
    m2 = suc zero
    m3 = suc (suc zero)

    data State : Set where
      s0 s1 : State

    -- The only transition: p sends m1 to q
    data LTS : State → Part → Part → {I : ℕ} → Vec Sort (suc I) → Fin (suc I)
             → State → Set where
      p→q/m1 : LTS s0 p q S₃ m1 s1

    Theory : BTheory 2
    Theory .BTheory.Behav = State
    Theory .BTheory._-<_>->_ s (P ⟶ Q # S , i) s′ = LTS s P Q S i s′

    open BTheory Theory

    s1-final : ∀ {α s} → ¬ (s1 -< α >-> s)
    s1-final ()

    -- The LTS is well-behaved
    WB : BT-Prop Theory
    WB .BT-Prop.recv-act-eq p→q/m1 p→q/m1 _ = refl
    WB .BT-Prop.snd≢rcv p→q/m1 ()
    WB .BT-Prop.step-det p→q/m1 p→q/m1 = refl
    WB .BT-Prop.~stepback {G1' = s0} b p→q/m1 = ⊥-elim (s1-final (~R→ b p→q/m1))
    WB .BT-Prop.~stepback {G1' = s1} _ p→q/m1 = s0 , ~refl , p→q/m1
    WB .BT-Prop.diamond p→q/m1 p→q/m1 (ii-≡snd _ q≢q) = ⊥-elim (q≢q refl)
    WB .BT-Prop.diamond p→q/m1 p→q/m1 (ii-disj d) = ⊥-elim (d (inj₁ (∈S refl)))
    WB .BT-Prop.cond-comm _ p→q/m1 _ ()

  open Behaviour
  open MPST WB

  -----------------------------------------------------------------------------
  -- Processes

  -- {m1, m2} and {m1, m3}
  D₁₂ D₁₃ : Subset 3
  D₁₂ = inside ∷ inside  ∷ outside ∷ []
  D₁₃ = inside ∷ outside ∷ inside  ∷ []

  Br : Vec (Proc 1 0) 3
  Br = ∅ ∷ ∅ ∷ ∅ ∷ []

  P/p : Proc 0 0
  P/p = q ! (2 , m1) < val v/unit >∙ ∅

  P/q : Proc 0 0
  P/q = ifp val (v/bool true)
          then (Σ p ？[ S₃ ∣ D₁₂ ]· Br)
          else (Σ p ？[ S₃ ∣ D₁₃ ]· Br)

  M : Session
  M = P/p ∷ P/q ∷ []

  -----------------------------------------------------------------------------
  -- Typing

  ∉s1 : ∀ {P} → ¬ (P ∈T s1)
  ∉s1 (in/α st _) = s1-final st
  ∉s1 (in/later st _) = s1-final st

  offers : ∀ {D : Subset 3} → m1 ∈ D
    → ∀ {i s′} → s0 -< p ⟶ q # S₃ , i >-> s′ → i ∈ D
  offers m1∈D p→q/m1 = m1∈D

  conts : ∀ {i s′} → s0 -< p ⟶ q # S₃ , i >-> s′
    → (α/sort (p ⟶ q # S₃ , i) ∷ []) & [] / s′ ↑ q ⊢p< ng > lookup Br i
  conts p→q/m1 = t/end ∉s1

  ⊢P/p : [] & [] / s0 ↑ p ⊢p< ng > P/p
  ⊢P/p = t/send p→q/m1 (te/val tv/unit) (t/end ∉s1)

  ⊢P/q : [] & [] / s0 ↑ q ⊢p< ng > P/q
  ⊢P/q = t/if (te/val tv/bool)
              (t/recv∣ R[ p→q/m1 ] (offers here) conts)
              (t/recv∣ R[ p→q/m1 ] (offers here) conts)

  ⊢M : ⊢s M ∶ s0
  ⊢M zero = ⊢P/p
  ⊢M (suc zero) = ⊢P/q

  -----------------------------------------------------------------------------
  -- Semantics: p ? {m1, m2} refuses m3

  M₃ : Session
  M₃ = (q ! (2 , m3) < val v/unit >∙ ∅)
     ∷ (Σ p ？[ S₃ ∣ D₁₂ ]· Br)
     ∷ []

  no-m3 : ∀ {M′} → ¬ (M₃ [ just (p ⟶ q # S₃ , m3) ]⇒ M′)
  no-m3 (s/comm _ _ _ _ (there here) (there (there ())))
