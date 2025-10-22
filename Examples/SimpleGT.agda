{-# OPTIONS --guardedness #-}
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤ ; tt)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Vec hiding (_++_)
open import Data.Vec.Properties
open import Data.Product
open import Relation.Nullary using (contraposition)
open import Relation.Nullary.Decidable
  using (True ; False ; toWitnessFalse ; fromWitnessFalse ; fromWitness ; toWitness)
open import Relation.Binary.PropositionalEquality hiding ( [_] )

open import Utils
open import Definitions

module Examples.SimpleGT (N : ℕ) where
  open import Definitions.Types(N) public
  module Parts = MPST GT-Properties
  open PreTypes public
  open Parts public hiding (_-<_>->_)

  t/recvhd : ∀{γ δ g P Q I pnq Γ}{Δ : Vec Behav δ}
    {Chs : Vec (Choice 0) (suc I)}
    {Br : Vec (Proc (suc γ) δ) (suc I)}
    (conts : ∀ (i : Fin (suc I)) ->
      (Chs [ i ]sort ∷ Γ) & Δ / Chs [ i ]cont ↑ Q ⊢p< ng > (lookup Br i))
    -> Γ & Δ / >> (P ⟶ Q ∶[ I , pnq ] Chs) ↑ Q ⊢p< g > (Σ P ？[ ch/sorts Chs ]· Br)
  t/recvhd {P = P} {Q = Q} {I = I} {pnq} {Γ} {Δ} {Chs} {Br} conts =
    t/recv R[ step/i zero ] tcont
    where
      tcont : ∀ {i : Fin (suc I)} {G' : Behav} →
        (>> (P ⟶ Q ∶[ I , pnq ] Chs)) -< P ⟶ Q # ch/sorts Chs , i >-> G' →
        (α/sort (P ⟶ Q # ch/sorts Chs , i) ∷ Γ) & Δ / G' ↑ Q ⊢p< ng > lookup Br i
      tcont {i} (step/i .i)
        rewrite lu/ch/sorts i Chs = conts i
      tcont (step/tl/I x z) = ⊥-elim (x (inj₂ (_∈pr_.∈R refl)))


  tt/end : ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{P G}
    → {p∉g : False (P ∈G? G)} → Γ & Δ / G ↑ P ⊢p< ng > ∅
  tt/end {p∉g = p∉g} = t/end (contraposition ∈T-∈G (toWitnessFalse p∉g))

  tt/rec : ∀{γ δ Γ Δ P G}{Pr : Proc γ (suc δ)}
    → Γ & (G ∷ Δ) / G ↑ P ⊢p< mg > Pr → Γ & Δ / G ↑ P ⊢p< ng > rec Pr
  tt/rec = t/rec rt/refl

  tt/var : ∀{γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{P G X}
    → Γ & insertAt Δ X G / G ↑ P ⊢p< ng > v X
  tt/var {_}{_}{_}{Δ}{_}{G}{X} with sym (insertAt-lookup Δ X G)
  ... | eq = t/var (subst (λ G → _ ~ G) eq ~refl) (■ , tt)

  tt/var/unfold : ∀{γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{P G X}
    → Γ & insertAt Δ X (>> (unfold/global G)) / μ G ↑ P ⊢p< ng > v X
  tt/var/unfold {_}{_}{_}{Δ}{_}{G}{X} with sym (insertAt-lookup Δ X (>> (unfold/global G)))
  ... | eq = t/var (subst (λ G → _ ~ G) eq ~unfold) (■ , tt)
