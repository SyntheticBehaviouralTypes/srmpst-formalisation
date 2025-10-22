{-# OPTIONS --guardedness #-}
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Vec hiding (_++_)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Utils
open import Definitions
open import Relation.Nullary.Decidable
  using (True ; False ; toWitnessFalse ; fromWitnessFalse ; fromWitness ; toWitness)

module Examples.CounterExamples where
  open import Examples.SimpleGT (3)
  A : Part
  A = zero

  B : Part
  B = suc zero

  C : Part
  C = suc (suc zero)

  round : Global 0 mg
  round = A ⟶ B ∶[ 1 , tt ]
            (  s/bool ·· end
            ∷  s/bool ·· >> ( B ⟶ C ∶[ 0 , tt ] ( s/bool ·· end
                                                ∷ [])
                            )
            ∷ [])

  -----------------------------------------------------------------------------

  -- The processes below shoud not type, and they don't
  p/C2 : Proc 0 0
  p/C2 = Σ B ？[ [ s/bool ] ]· (Σ B ？[ [ s/bool ] ]· (∅ ∷ []) ∷ [])

  t/C/bad : [] & [] / >> round ↑ C ⊢p< mg > p/C2 → ⊥
  t/C/bad (t/recv R[ step/tl/I x x₁ ] conts) = ⊥-elim (x (inj₂ (_∈pr_.∈S refl)))
  t/C/bad (t/skip is-recv SK[ _ , _ , ii ] _) with ii ([ step/i zero , (λ{ (∈S ()) ; (∈R ()) }) ]► (■ , tt))
  t/C/bad (MPST.t/skip MPST.is-recv MPST.SK[ _ , _ , _ ] _) | _ , BTheory.■ , ()
  t/C/bad (MPST.t/skip MPST.is-recv MPST.SK[ _ , _ , _ ] _) | _ , (() BTheory.► fst) , snd

  p/C3 : Proc 0 0
  p/C3 = Σ A ？[ s/bool ∷ [] ]· (Σ B ？[ s/bool ∷ [] ]· (∅ ∷ []) ∷ [])

  t/C3/bad : [] & [] / >> round ↑ C ⊢p< mg > p/C3 → ⊥
  t/C3/bad (t/recv R[ step/tl/I x x₁ ] conts) = ⊥-elim (x (inj₁ (_∈pr_.∈S refl)))
  t/C3/bad (t/skip is-recv SK[ _ , _ , ii ] _) with ii (([ step/i zero , (λ{ (∈S ()) ; (∈R ()) }) ]► (■ , tt))) -- (tr/trans (step/i zero) (λ{ (∈S ()) ; (∈R ()) }) tr/refl)
  t/C3/bad (MPST.t/skip MPST.is-recv MPST.SK[ _ , _ , _ ] _) | _ , BTheory.■ , ()
  t/C3/bad (MPST.t/skip MPST.is-recv MPST.SK[ _ , _ , _ ] _) | _ , (() BTheory.► fst) , snd
  -- t/C3/bad (t/skip is-recv _ _) | _ , now () _
  -- t/C3/bad (t/skip is-recv _ _) | _ , [ () , _ ]► _

  p/C4 : Proc 0 0
  p/C4 = rec (v zero)

  td/C2 : [] & [] / >> round ↑ C ⊢p< mg > p/C4 → ⊥
  td/C2 (MPST.t/skip () x₁ conts)

  -----------------------------------------------------------------------------

  -- this can be typed, but it is no longer a problem (see td/C2 above)
  td/C2-bad : [] & >> round ∷ [] / >> round ↑ C ⊢p< ng > v zero
  td/C2-bad = t/var ~refl (■ , tt)
