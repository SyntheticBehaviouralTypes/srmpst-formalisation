{-# OPTIONS --guardedness #-}
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤ ; tt)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Vec hiding (_++_)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Decidable
  using (True ; False ; toWitnessFalse ; fromWitnessFalse ; fromWitness ; toWitness)

open import Utils
open import Definitions


module Examples.PingPong where
  open import Examples.SimpleGT(2)

  A : Part
  A = zero

  B : Part
  B = suc zero

  module NonRecursive where
    -- Non recursive ping pong
    ping-pong : Global 0 ng
    ping-pong = >> (A ⟶ B ∶[ 0 , tt ] ((s/bool ·· (>> (B ⟶ A ∶[ 0 , tt ] ((s/nat ·· end) ∷ [])))) ∷ []))

    choicesAB : Vec Sort 1
    choicesAB = s/bool ∷ []

    choicesBA : Vec Sort 1
    choicesBA = s/nat ∷ []

    p1 : Global 0 ng
    p1 = >> (B ⟶ A ∶[ 0 , tt ] ((s/nat ·· end) ∷ []))

    pp/step-1 : ping-pong  -< A ⟶ B # [ s/bool ] , zero >-> p1
    pp/step-1 = step/i zero

    pp/step-2 : p1  -< B ⟶ A # [ s/nat ] , zero >-> end
    pp/step-2 = step/i zero

    p/A : Proc 0 0
    p/A = B ! 0 , zero < val (v/bool true) >∙ (Σ B ？[ [ s/nat ] ]· (∅ ∷ []))

    p/B : Proc 0 0
    p/B = Σ A ？[ [ s/bool ] ]· ((A ! 0 , zero < (val (v/nat zero)) >∙ ∅) ∷ [])

    M : Session
    M = p/A ∷ p/B ∷ []

    td/A : [] & [] / ping-pong ↑ A ⊢p< ng > p/A
    td/A = t/send (step/i zero)  (te/val tv/bool) (t/recv R[ step/i zero ] cont/typ)
      where
        cont/typ : ∀ {i} {G'} →
          p1 -< (B ⟶ A # [ s/nat ]) , i >-> G' →
          (α/sort ((B ⟶ A # [ s/nat ]) , i) ∷ []) & [] / G' ↑ A ⊢p< ng > lookup (∅ ∷ []) i
        cont/typ {zero} (step/i .zero) = tt/end
        cont/typ {zero} (step/tl/I x x₁) = ⊥-elim (x (inj₂ (_∈pr_.∈R refl)))

    td/B : [] & [] / ping-pong ↑ B ⊢p< ng > p/B
    td/B = t/recv R[ step/i zero ] cont/typ
      where
        cont/typ : ∀ {i} {G'} →
           ping-pong -< (A ⟶ B # [ s/bool ]) , i >-> G' →
           (α/sort ((A ⟶ B # [ s/bool ]) , i) ∷ []) & [] / G' ↑ B ⊢p< ng >
           lookup ((A ! 0 , zero < val (v/nat zero) >∙ ∅) ∷ []) i
        cont/typ {zero} (step/i .zero) = t/send (step/i zero) (te/val tv/nat) tt/end
        cont/typ {zero} (step/tl/I x x₁) = ⊥-elim (x (inj₂ (_∈pr_.∈R refl)))

    td/S : ⊢s M ∶ ping-pong
    td/S zero = td/A
    td/S (suc zero) = td/B

  module Recursive where
    -- Recursive ping pong
    ping-pong : Global 0 ng
    ping-pong = μ (A ⟶ B ∶[ 0 , tt ] ((s/bool ·· (>> (B ⟶ A ∶[ 0 , tt ] ((s/nat ·· var zero) ∷ [])))) ∷ []))

    p1 : Global 0 ng
    p1 = >> (B ⟶ A ∶[ 0 , tt ] ((s/nat ·· ping-pong) ∷ []))

    choicesAB : Vec Sort 1
    choicesAB = s/bool ∷ []

    choicesBA : Vec Sort 1
    choicesBA = s/nat ∷ []

    pp/step-1 : ping-pong  -< A ⟶ B # [ s/bool ] , zero >-> p1
    pp/step-1 = step/unfold (step/i zero)

    pp/step-2 : p1  -< B ⟶ A # [ s/nat ] , zero >-> ping-pong
    pp/step-2 = step/i zero

    p/A : Proc 0 0
    p/A = rec (B ! 0 , zero < val (v/bool true) >∙ (Σ B ？[ [ s/nat ] ]· (v zero ∷ [])))

    p/B : Proc 0 0
    p/B = rec (Σ A ？[ [ s/bool ] ]· ((A ! 0 , zero < (val (v/nat zero)) >∙ v zero) ∷ []))

    M : Session
    M = p/A ∷ p/B ∷ []

    td/A : [] & [] / ping-pong ↑ A ⊢p< ng > p/A
    td/A = tt/rec (t/send (_-<_>->_.step/unfold (_-<_>->_.step/i zero))
      (te/val tv/bool)
      (t/recvhd λ{ zero → tt/var }))

    td/B : [] & [] / ping-pong ↑ B ⊢p< ng > p/B
    td/B = t/bisim (~sym ~unfold) (tt/rec
      (t/recvhd λ{ zero →
        t/send (_-<_>->_.step/i zero) (te/val tv/nat) (tt/var/unfold) }))

    td/S : ⊢s M ∶ ping-pong
    td/S zero = td/A
    td/S (suc zero) = td/B
