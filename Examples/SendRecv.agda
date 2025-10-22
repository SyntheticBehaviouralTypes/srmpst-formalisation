{-# OPTIONS --guardedness #-}
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤ ; tt)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Vec hiding (_++_)
open import Data.Product
open import Relation.Nullary.Decidable
  using (True ; False ; toWitnessFalse ; fromWitnessFalse ; fromWitness ; toWitness)
open import Relation.Binary.PropositionalEquality hiding ( [_] )

open import Utils
open import Definitions

module Examples.SendRecv where
  open import Examples.SimpleGT(2)

  A : Part
  A = zero

  B : Part
  B = suc zero

  module SendRecvNR where
    -- Non recursive protocol
    send-recv : Global 0 ng
    send-recv = >> (A ⟶ B ∶[ 0 , tt ] ((s/bool ·· end) ∷ []))

    sr/step : send-recv -< A ⟶ B # [ s/bool ] , zero >-> end
    sr/step = step/i zero

    p/A : Proc 0 0
    p/A = B ! 0 , zero < val (v/bool true) >∙ ∅

    p/B : Proc 0 0
    p/B = Σ A ？[ [ s/bool ] ]· (∅ ∷ [])

    M : Session
    M = p/A ∷ p/B ∷ []

    td/A : [] & [] / send-recv ↑ A ⊢p< ng > p/A
    td/A = t/send (step/i zero) (te/val tv/bool) tt/end

    td/B : [] & [] / send-recv ↑ B ⊢p< ng > p/B
    td/B = t/recvhd λ { zero -> tt/end }

    td/M : ⊢s M ∶ send-recv
    td/M zero = td/A
    td/M (suc zero) = td/B

  module SendRecv where
    -- Recursive protocol
    send-recv : Global 0 ng
    send-recv = μ (A ⟶ B ∶[ 0 , tt ] ((s/bool ·· var zero) ∷ []))

    sr/step : send-recv -< A ⟶ B # [ s/bool ] , zero >-> send-recv
    sr/step = step/unfold (step/i zero)

    p/A : Proc 0 0
    p/A = rec (B ! 0 , zero < val (v/bool true) >∙ v zero)

    p/B : Proc 0 0
    p/B = rec (Σ A ？[ [ s/bool ] ]· ((v zero) ∷ []))

    M : Session
    M = p/A ∷ p/B ∷ []

    td/A : [] & [] / send-recv ↑ A ⊢p< ng > p/A
    td/A = tt/rec
             (t/send (step/unfold (step/i zero))
             (te/val tv/bool)
             tt/var)

    td/B : [] & [] / send-recv ↑ B ⊢p< ng > p/B
    td/B = t/bisim (~sym ~unfold) (tt/rec (t/recvhd λ{ zero → tt/var/unfold }))

    td/S : ⊢s M ∶ send-recv
    td/S zero = td/A
    td/S (suc zero) = td/B

  module SendRecv' where
    -- Recursive protocol but now the the process starts by sending before doing the loop
    send-recv : Global 0 ng
    send-recv = μ (A ⟶ B ∶[ 0 , tt ] ((s/bool ·· var zero) ∷ []))

    sr/step : send-recv -< A ⟶ B # [ s/bool ] , zero >-> send-recv
    sr/step = step/unfold (step/i zero)

    p/A : Proc 0 0 -- Now A unfolds the loop once
    p/A = B ! 0 , zero < val (v/bool true) >∙ (rec (B ! 0 , zero < val (v/bool true) >∙ v zero))

    p/B : Proc 0 0
    p/B = rec (Σ A ？[ [ s/bool ] ]· ((v zero) ∷ []))

    M : Session
    M = p/A ∷ p/B ∷ []

    td/A : [] & [] / send-recv ↑ A ⊢p< ng > p/A
    td/A = t/send sr/step
      (te/val tv/bool)
      (t/rec rt/refl (t/send (step/unfold (step/i zero))  (te/val tv/bool) (tt/var)))

    td/B : [] & [] / send-recv ↑ B ⊢p< ng > p/B
    td/B = t/rec rt/refl (t/recv R[ step/unfold (step/i zero) ] cont/typ)
      where
        cont/typ : ∀ {i} {G'} →
          send-recv -< (A ⟶ suc zero # [ s/bool ]) , i >-> G' →
          (α/sort ((A ⟶ B # [ s/bool ]) , i) ∷ []) & send-recv ∷ [] /
          G' ↑ suc zero ⊢p< ng > lookup (v zero ∷ []) i
        cont/typ {zero} (step/unfold (step/i .zero)) = tt/var
        cont/typ {zero} (step/unfold (step/tl/I indep _)) = ⊥-elim (indep (inj₂ (_∈pr_.∈R refl)))


    td/M : ⊢s M ∶ send-recv
    td/M zero = td/A
    td/M (suc zero) = td/B
