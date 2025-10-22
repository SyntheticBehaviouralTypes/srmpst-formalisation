{-# OPTIONS --guardedness #-}
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Vec hiding (_++_)
open import Data.Product
open import Relation.Nullary.Decidable
  using (True ; False ; toWitnessFalse ; fromWitnessFalse ; fromWitness ; toWitness)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Utils
open import Definitions

module Examples.RoundRobin where
  open import Examples.SimpleGT(3)

  A : Part
  A = zero

  B : Part
  B = suc zero

  C : Part
  C = suc (suc zero)

  module NonRecursive where
    round : Global 0 ng
    round = >> (A ⟶ B ∶[ 0 , tt ] ((s/bool ··
      >> (B ⟶ C ∶[ 0 , tt ] ((s/bool ··
      (>> (C ⟶ A ∶[ 0 , tt ] ((s/bool ··
      end) ∷ [])))) ∷ []))) ∷ []))

    r1 : Global 0 ng
    r1 = >> ((B ⟶ C ∶[ 0 , tt ] ((s/bool ·· (>> (C ⟶ A ∶[ 0 , tt ] ((s/bool ·· end) ∷ []))))
      ∷ [])))

    r2 : Global 0 ng
    r2 =  >> (C ⟶ A ∶[ 0 , tt ] ((s/bool ·· end) ∷ []))

    round/step-1 : round -< A ⟶ B # [ s/bool ] , zero >-> r1
    round/step-1 = step/i zero

    round/step-2 : r1  -< B ⟶ C # [ s/bool ] , zero >-> r2
    round/step-2 = step/i zero

    round/step-3 : r2 -< C ⟶ A # [ s/bool ] , zero >-> end
    round/step-3 = step/i zero


    p/A : Proc 0 0
    p/A = B ! 0 , zero < (val (v/bool true)) >∙ (Σ C ？[ [ s/bool ] ]· (∅ ∷ []))

    MS1 : must-skip
      (((s/bool ··
         >>
         (B ⟶ C ∶[ 0 , tt ]
          ((s/bool ·· >> (C ⟶ A ∶[ 0 , tt ] ((s/bool ·· end) ∷ []))) ∷ [])))
        ∷ [])
       [ zero ]cont)
      A
      C
    MS1 .MPST.must-skip.ms-sound (BTheory.■ , snd) x₁ (BTheory.■ , BTheory.∈-tr (step/i zero) (∈S ()) , snd₁)
    MS1 .MPST.must-skip.ms-sound (BTheory.■ , snd) x₁ (BTheory.■ , BTheory.∈-tr (step/i zero) (∈R ()) , snd₁)
    MS1 .MPST.must-skip.ms-sound (BTheory.■ , snd) x₁ (BTheory.■ , BTheory.∈-tr (step/tl/I x (step/choice/cons (step/i i) _)) _ , _) = ⊥-elim (x (inj₂ (_∈pr_.∈S refl)))
    MS1 .MPST.must-skip.ms-sound (BTheory.■ , snd) x₁ (BTheory.■ , BTheory.∈-tr (step/tl/I x (step/choice/cons (step/tl/I x₂ (step/choice/cons () x₄)) _)) _ , _)
    MS1 .MPST.must-skip.ms-sound (BTheory.■ , snd) x₁ (step/i zero BTheory.► fst , (a , b) , d , e) = d (∈-tr (step/i zero) (_∈pr_.∈R refl))
    MS1 .MPST.must-skip.ms-sound (BTheory.■ , snd) x₁ (step/tl/I x x₂ BTheory.► fst , snd₁) = snd₁ .proj₂ .proj₁ (∈-tr (_-<_>->_.step/i zero) (_∈pr_.∈R refl))
    MS1 .MPST.must-skip.ms-sound (step/i zero BTheory.► BTheory.■ , snd) x₁ x₂ = x₁ (∈-tr (_-<_>->_.step/i zero) (_∈pr_.∈R refl))
    MS1 .MPST.must-skip.ms-sound (step/i zero BTheory.► step/i zero BTheory.► fst , snd) x₁ x₂ = snd .proj₂ .proj₁ (_∈pr_.∈R refl)
    MS1 .MPST.must-skip.ms-sound (step/i zero BTheory.► step/tl/I x (step/choice/cons () x₄) BTheory.► fst , snd) x₁ x₂
    MS1 .MPST.must-skip.ms-sound (step/tl/I x (step/choice/cons (step/i zero) x₄) BTheory.► fst , snd) x₁ x₂ = snd .proj₁ (_∈pr_.∈R refl)
    MS1 .MPST.must-skip.ms-sound (step/tl/I x (step/choice/cons (step/tl/I x₃ (step/choice/cons () x₆)) x₄) BTheory.► fst , snd) x₁ x₂
    MS1 .MPST.must-skip.ms-noact (BTheory.∈-tr (step/tl/I x (step/choice/cons (step/tl/I x₁ x₃) x₂)) (∈S refl)) = x₁ (inj₂ (_∈pr_.∈S refl))
    MS1 .MPST.must-skip.ms-noact (BTheory.∈-tr (step/tl/I x (step/choice/cons (step/i _) x₂)) (∈R refl)) = x (inj₂ (_∈pr_.∈S refl))
    MS1 .MPST.must-skip.ms-noact (BTheory.∈-tr (step/tl/I x (step/choice/cons (step/tl/I x₁ x₃) x₂)) (∈R refl)) = x₁ (inj₂ (_∈pr_.∈R refl))
    MS1 .MPST.must-skip.ms-activ (BTheory.■ , snd) = _ , step/i zero ► ■ , (λ{ (BTheory.∈-tr (step/tl/I x (step/choice/cons (step/tl/I x₁ x₄) x₃)) (∈S x₂)) → x₁ (inj₂ (_∈pr_.∈S x₂)) ; (BTheory.∈-tr (step/tl/I x (step/choice/cons (step/i zero) x₃)) (∈R x₂)) → x (inj₂ (_∈pr_.∈S refl)) ; (BTheory.∈-tr (step/tl/I x (step/choice/cons (step/tl/I x₁ x₄) x₃)) (∈R x₂)) → x₁ (inj₂ (_∈pr_.∈R x₂)) }) , ∈-tr (_-<_>->_.step/i zero) (_∈pr_.∈R refl)
    MS1 .MPST.must-skip.ms-activ (step/i zero BTheory.► BTheory.■ , snd) = _ , (■ , BTheory.∈-tr (step/i zero) (_∈pr_.∈R refl))
    MS1 .MPST.must-skip.ms-activ (step/i zero BTheory.► step/i zero BTheory.► BTheory.■ , a , b) = ⊥-elim (b .proj₁ (_∈pr_.∈R refl))
    MS1 .MPST.must-skip.ms-activ (step/i zero BTheory.► step/tl/I x (step/choice/cons () _) BTheory.► fst , snd)
    MS1 .MPST.must-skip.ms-activ (step/tl/I x (step/choice/cons (step/i zero) x₂) BTheory.► fst , snd) = ⊥-elim (snd .proj₁ (_∈pr_.∈R refl))
    MS1 .MPST.must-skip.ms-activ (step/tl/I x (step/choice/cons (step/tl/I x₁ (step/choice/cons () x₄)) x₂) BTheory.► fst , snd)

    td/A : [] & [] / round ↑ A ⊢p< ng > p/A
    td/A = t/send (step/i zero) (te/val tv/bool) (t/skip is-comm.is-recv MS1
      λ{ (BTheory.■ , BTheory.∈-tr (step/i zero) (∈S ()))
       ; (BTheory.■ , BTheory.∈-tr (step/i zero) (∈R ()))
       ; (BTheory.■ , BTheory.∈-tr (step/tl/I x (step/choice/cons (step/tl/I _ (step/choice/cons () _)) _)) ∈-prf)
       ; (BTheory.■ , BTheory.∈-tr (step/tl/I x (step/choice/cons (step/i zero) _)) ∈-prf) → ⊥-elim (x (inj₂ (_∈pr_.∈S refl)))
       ; (step/tl/I x (step/choice/cons (step/tl/I _ (step/choice/cons () _)) _) BTheory.► fst , snd)
       ; (step/tl/I x (step/choice/cons (step/i zero) _) BTheory.► fst , snd) → ⊥-elim (x (inj₂ (_∈pr_.∈S refl)))
       ; (step/i zero BTheory.► step/i zero BTheory.► fst , _ , f , _) → ⊥-elim (f (∈-tr (_-<_>->_.step/i zero) (_∈pr_.∈R refl)))
       ; (step/i zero BTheory.► step/tl/I x (step/choice/cons () _) BTheory.► fst , snd)

       ; (step/i zero BTheory.► BTheory.■ , a , ∈-tr b c) → t/recvhd (λ{ zero → tt/end })
      })

    p/B : Proc 0 0
    p/B = Σ A ？[ [ s/bool ] ]· ((C ! 0 , zero < (val (v/bool true)) >∙ ∅) ∷ [])

    td/B : [] & [] / round ↑ B ⊢p< ng > p/B
    td/B = t/recvhd (λ{ zero → t/send (_-<_>->_.step/i zero) (te/val tv/bool) tt/end })

    p/C : Proc 0 0
    p/C = Σ B ？[ [ s/bool ] ]· ((A ! 0 , zero < (val (v/bool true)) >∙ ∅) ∷ [])

    MS2 : must-skip round C B
    MS2 .MPST.must-skip.ms-sound (BTheory.■ , snd) x₁ (BTheory.■ , BTheory.∈-tr (step/i zero) (∈S ()) , snd₁)
    MS2 .MPST.must-skip.ms-sound (BTheory.■ , snd) x₁ (BTheory.■ , BTheory.∈-tr (step/i zero) (∈R ()) , snd₁)
    MS2 .MPST.must-skip.ms-sound (BTheory.■ , snd) x₁ (BTheory.■ , BTheory.∈-tr (step/tl/I x (step/choice/cons (step/i zero) _)) ∈-prf , snd₁) = x (inj₂ (_∈pr_.∈S refl))
    MS2 .MPST.must-skip.ms-sound (BTheory.■ , snd) x₁ (BTheory.■ , BTheory.∈-tr (step/tl/I x (step/choice/cons (step/tl/I y (step/choice/cons (step/i zero) _)) _)) ∈-prf , snd₁) = y (inj₂ ∈-prf)
    MS2 .MPST.must-skip.ms-sound (BTheory.■ , snd) x₁ (BTheory.■ , BTheory.∈-tr (step/tl/I x (step/choice/cons (step/tl/I y (step/choice/cons (step/tl/I z (step/choice/cons () _)) _)) _)) ∈-prf , snd₁)
    MS2 .MPST.must-skip.ms-sound (BTheory.■ , snd) x₁ (step/i zero BTheory.► fst , snd₁) = snd₁ .proj₂ .proj₁ (∈-tr (_-<_>->_.step/i zero) (_∈pr_.∈R refl))
    MS2 .MPST.must-skip.ms-sound (BTheory.■ , snd) x₁ (step/tl/I x (step/choice/cons (step/i zero) _) BTheory.► fst , snd₁) = x (inj₂ (_∈pr_.∈S refl))
    MS2 .MPST.must-skip.ms-sound (BTheory.■ , snd) x₁ (step/tl/I x (step/choice/cons (step/tl/I y (step/choice/cons (step/i zero) _)) _) BTheory.► fst , snd₁) = x (inj₁ (_∈pr_.∈R refl))
    MS2 .MPST.must-skip.ms-sound (BTheory.■ , snd) x₁ (step/tl/I x (step/choice/cons (step/tl/I y (step/choice/cons (step/tl/I z (step/choice/cons () _)) _)) _) BTheory.► fst , snd₁)
    MS2 .MPST.must-skip.ms-sound (step/i zero BTheory.► BTheory.■ , snd) x₁ x₂ = x₁ (∈-tr (_-<_>->_.step/i zero) (_∈pr_.∈R refl))
    MS2 .MPST.must-skip.ms-sound (step/i zero BTheory.► step/i zero BTheory.► fst , snd) x₁ x₂ = snd .proj₂ .proj₁ (_∈pr_.∈R refl)
    MS2 .MPST.must-skip.ms-sound (step/i zero BTheory.► step/tl/I x (step/choice/cons (step/i zero) x₄) BTheory.► fst , snd) x₁ x₂ = snd .proj₂ .proj₁ (_∈pr_.∈S refl)
    MS2 .MPST.must-skip.ms-sound (step/i zero BTheory.► step/tl/I x (step/choice/cons (step/tl/I y (step/choice/cons () _)) x₄) BTheory.► fst , snd) x₁ x₂
    MS2 .MPST.must-skip.ms-sound (step/tl/I x (step/choice/cons (step/i zero) x₄) BTheory.► fst , snd) x₁ x₂ = snd .proj₁ (_∈pr_.∈R refl)
    MS2 .MPST.must-skip.ms-sound (step/tl/I x (step/choice/cons (step/tl/I x₃ (step/choice/cons (step/i zero) x₆)) x₄) BTheory.► fst , snd) x₁ x₂ = snd .proj₁ (_∈pr_.∈S refl)
    MS2 .MPST.must-skip.ms-sound (step/tl/I x (step/choice/cons (step/tl/I x₃ (step/choice/cons (step/tl/I y (step/choice/cons () _)) x₆)) x₄) BTheory.► fst , snd) x₁ x₂
    MS2 .MPST.must-skip.ms-noact (BTheory.∈-tr (step/tl/I x (step/choice/cons (step/tl/I x₁ x₃) x₂)) (∈S refl)) = x₁ (inj₂ (_∈pr_.∈S refl))
    MS2 .MPST.must-skip.ms-noact (BTheory.∈-tr (step/tl/I x (step/choice/cons (step/i _) x₂)) (∈R refl)) = x (inj₂ (_∈pr_.∈S refl))
    MS2 .MPST.must-skip.ms-noact (BTheory.∈-tr (step/tl/I x (step/choice/cons (step/tl/I x₁ x₃) x₂)) (∈R refl)) = x₁ (inj₂ (_∈pr_.∈R refl))
    MS2 .MPST.must-skip.ms-activ (BTheory.■ , snd) = _ , step/i zero ► ■ , (λ{ (BTheory.∈-tr (step/tl/I x (step/choice/cons (step/tl/I x₁ x₄) x₃)) (∈S x₂)) → x₁ (inj₂ (_∈pr_.∈S x₂)) ; (BTheory.∈-tr (step/tl/I x (step/choice/cons (step/i zero) x₃)) (∈R x₂)) → x (inj₂ (_∈pr_.∈S refl)) ; (BTheory.∈-tr (step/tl/I x (step/choice/cons (step/tl/I x₁ x₄) x₃)) (∈R x₂)) → x₁ (inj₂ (_∈pr_.∈R x₂)) }) , ∈-tr (_-<_>->_.step/i zero) (_∈pr_.∈R refl)
    MS2 .MPST.must-skip.ms-activ (step/i zero BTheory.► BTheory.■ , snd) = _ , (■ , BTheory.∈-tr (step/i zero) (_∈pr_.∈R refl))
    MS2 .MPST.must-skip.ms-activ (step/i zero BTheory.► step/i zero BTheory.► BTheory.■ , a , b) = ⊥-elim (b .proj₁ (_∈pr_.∈R refl))
    MS2 .MPST.must-skip.ms-activ (step/i zero BTheory.► step/i zero BTheory.► step/i zero BTheory.► fst , fst₁ , snd) = ⊥-elim (snd .proj₁ (_∈pr_.∈R refl))
    MS2 .MPST.must-skip.ms-activ (step/i zero BTheory.► step/i zero BTheory.► (step/tl/I x y) BTheory.► fst , fst₁ , snd) = ⊥-elim (snd .proj₁ (_∈pr_.∈R refl))
    MS2 .MPST.must-skip.ms-activ (step/i zero BTheory.► step/tl/I x (step/choice/cons (step/i zero) _) BTheory.► fst , snd) = ⊥-elim (snd .proj₂ .proj₁ (_∈pr_.∈S refl))
    MS2 .MPST.must-skip.ms-activ (step/i zero BTheory.► step/tl/I x (step/choice/cons (step/tl/I y (step/choice/cons () _)) _) BTheory.► fst , snd)
    MS2 .MPST.must-skip.ms-activ (step/tl/I x (step/choice/cons (step/i zero) x₂) BTheory.► fst , snd) = ⊥-elim (snd .proj₁ (_∈pr_.∈R refl))
    MS2 .MPST.must-skip.ms-activ (step/tl/I x (step/choice/cons (step/tl/I x₁ (step/choice/cons (step/i zero) x₄)) x₂) BTheory.► fst , snd) = ⊥-elim (snd .proj₁ (_∈pr_.∈S refl))
    MS2 .MPST.must-skip.ms-activ (step/tl/I x (step/choice/cons (step/tl/I x₁ (step/choice/cons (step/tl/I y (step/choice/cons () _)) x₄)) x₂) BTheory.► fst , snd)

    td/C : [] & [] / round ↑ C ⊢p< ng > p/C
    td/C = t/skip is-comm.is-recv MS2
      λ{ (BTheory.■ , snd) → ⊥-elim (MS2 .must-skip.ms-noact snd)
       ; (step/tl/I x (step/choice/cons (step/i zero) _) BTheory.► fst , snd) → ⊥-elim (x (inj₂ (_∈pr_.∈S refl)))
       ; (step/tl/I x (step/choice/cons (step/tl/I y (step/choice/cons (step/i zero) _)) _) BTheory.► fst , snd) → ⊥-elim (y (inj₂ (_∈pr_.∈S refl)))
       ; (step/tl/I x (step/choice/cons (step/tl/I y (step/choice/cons (step/tl/I z (step/choice/cons () _)) _)) _) BTheory.► fst , snd)
       ; (step/i zero BTheory.► step/i zero BTheory.► fst , snd) → ⊥-elim
                                                                    (snd .proj₂ .proj₁ (∈-tr (_-<_>->_.step/i zero) (_∈pr_.∈R refl)))
       ; (step/i zero BTheory.► step/tl/I x (step/choice/cons (step/i zero) _) BTheory.► fst , snd) → ⊥-elim (x (inj₂ (_∈pr_.∈S refl)))
       ; (step/i zero BTheory.► step/tl/I x (step/choice/cons (step/tl/I y (step/choice/cons () _)) _) BTheory.► fst , snd)

       ; (step/i zero BTheory.► BTheory.■ , snd) → t/recvhd (λ{ zero → t/send (_-<_>->_.step/i zero) (te/val tv/bool) tt/end })
       }

    M : Session
    M = p/A ∷ p/B ∷ p/C ∷ []

    td/M : ⊢s M ∶ round
    td/M zero = td/A
    td/M (suc zero) = td/B
    td/M (suc (suc zero)) = td/C

  -- module Recursive where
  --   round : Global 0 ng
  --   round = μ (A ⟶ B ∶[ 0 , tt ] ((s/bool ··
  --     >> (B ⟶ C ∶[ 0 , tt ] ((s/bool ··
  --     (>> (C ⟶ A ∶[ 0 , tt ] ((s/bool ··
  --     var zero) ∷ [])))) ∷ []))) ∷ []))

  --   p/A : Proc 0 0
  --   p/A = rec (B ! 0 , zero < (val (v/bool true)) >∙ (Σ C ？[ [ s/bool ] ]· (v zero ∷ [])))
