{-# OPTIONS --guardedness #-}
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤ ; tt)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties using (<ᵇ⇒<)
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Vec hiding (_++_)
open import Data.Product
open import Relation.Nullary using (¬_ ; yes ; no)
open import Relation.Nullary.Decidable
  using (True ; False ; toWitnessFalse ; fromWitnessFalse ; fromWitness ; toWitness)
open import Relation.Binary.PropositionalEquality hiding ( [_] )

open import Utils
open import Definitions

module Examples.NoSynGT where

  module Behaviours where
    open import Definitions.Expr
    open import Definitions.Common(3)
    open import Definitions.Actions(3)

    pattern f0 = zero
    pattern f1 = suc f0
    pattern f2 = suc f1
    pattern f3 = suc f2
    pattern f4 = suc f3
    pattern f5 = suc f4
    pattern f6 = suc f5

    pattern ss0 = suc _
    pattern ss1 = suc ss0
    pattern ss2 = suc ss1
    pattern ss3 = suc ss2
    pattern ss4 = suc ss3
    pattern ss5 = suc ss4
    pattern ss6 = suc ss5

    mk-fin : ∀ m n → {t : T (m <ᵇ suc n)} → Fin (suc n)
    mk-fin m n {t = t} = fromℕ< (<ᵇ⇒< m (suc n) t)

    -- The participants
    A = mk-fin 0 2
    B = mk-fin 1 2
    C = mk-fin 2 2


    -- The Protocol states
    IndepProto-State = Fin 4

    s0  = mk-fin 0 3
    s1  = mk-fin 1 3
    s2  = mk-fin 2 3
    s3  = mk-fin 3 3


    -- The labels and their s/itm
    item = mk-fin 0 0
    s/itm = s/unit ∷ []

    -- The LTS
    open HeadAct

    data LTS : IndepProto-State → Part → Part → {I : ℕ} → Vec Sort (suc I)
         → Fin (suc I) → IndepProto-State → Set where
      a→b/0   : LTS s0 A B s/itm item s1
      a→c/0   : LTS s0 A C s/itm item s2

      a→c/1   : LTS s1 A C s/itm item s3
      a→b/1   : LTS s2 A B s/itm item s3

    TheLTS : IndepProto-State → Action → IndepProto-State → Set
    TheLTS si (P ⟶ Q # S , i) so = LTS si P Q S i so

    IndepProtoTheory : BTheory 3
    IndepProtoTheory .BTheory.Behav = IndepProto-State
    IndepProtoTheory .BTheory._-<_>->_ = TheLTS

    open BTheory IndepProtoTheory

    pattern ≢S = ∈S ()
    pattern ≢R = ∈R ()

    pattern S≢S = inj₁ (∈S ())
    pattern S≢R = inj₁ (∈R ())

    pattern R≢S = inj₂ (∈S ())
    pattern R≢R = inj₂ (∈R ())

    recv-act-eq : ∀ {G} {α} {α'} {G'} {G''} →
              G -< α >-> G' →
              G -< α' >-> G'' → receiver α ∈α α' → proj₁ α ≡ proj₁ α'
    recv-act-eq a→b/0 () (∈S refl)
    recv-act-eq a→c/0 () (∈S refl)
    recv-act-eq a→c/1 () (∈S refl)
    recv-act-eq a→b/1 () (∈S refl)
    recv-act-eq a→b/0 a→b/0 (∈R refl) = refl
    recv-act-eq a→c/0 a→c/0 (∈R refl) = refl
    recv-act-eq a→c/1 a→c/1 (∈R refl) = refl
    recv-act-eq a→b/1 a→b/1 (∈R refl) = refl

    send-act-indep : ∀ {G} {α} {α'} {G'} {G''} →
                 G -< α >-> G' → G -< α' >-> G'' → sender α' ∉α α → α ∥ α'
    send-act-indep a→b/0 a→b/0 x₂ = ⊥-elim (x₂ (∈S refl))
    send-act-indep a→b/0 a→c/0 x₂ = ⊥-elim (x₂ (∈S refl))
    send-act-indep a→c/0 a→b/0 x₂ = ⊥-elim (x₂ (∈S refl))
    send-act-indep a→c/0 a→c/0 x₂ = ii-disj (λ z → x₂ (∈S refl))
    send-act-indep a→c/1 a→c/1 x₂ = ii-disj (λ z → x₂ (∈S refl))
    send-act-indep a→b/1 a→b/1 x₂ = ii-disj (λ z → x₂ (∈S refl))

    snd≢rcv : ∀ {G} {G'} {α} → G -< α >-> G' → sender α ≢ receiver α
    snd≢rcv () refl

    step-det : ∀ {G} {α} {G'} {G''} →
           G -< α >-> G' → G -< α >-> G'' → G' ≡ G''
    step-det a→b/0 a→b/0 = refl
    step-det a→c/0 a→c/0 = refl
    step-det a→c/1 a→c/1 = refl
    step-det a→b/1 a→b/1 = refl

    ~stepback : ∀ {α} {G0} {G1} {G1'} →
            G1 ~ G1' →
            G0 -< α >-> G1 → ∃-syntax (λ G0' → (G0 ~ G0') × (G0' -< α >-> G1'))
    ~stepback {G1' = f0} b a→b/0 with ~R→ b a→b/0
    ... | ()
    ~stepback {G1' = f1} b a→b/0 = f0 , ~refl , a→b/0
    ~stepback {G1' = f2} b a→b/0 with ~L→ b a→c/1
    ... | ()
    ~stepback {G1' = f3} b a→b/0 with ~L→ b a→c/1
    ... | ()
    ~stepback {G1' = f0} b a→c/0 with _~_.~R b a→b/0
    ... | f3 , a→b/1 , b' with ~R→ b' a→c/1
    ... | ()
    ~stepback {G1' = f1} b a→c/0 with ~L→ b a→b/1
    ... | ()
    ~stepback {G1' = f2} b a→c/0 = f0 , ~refl , a→c/0
    ~stepback {G1' = f3} b a→c/0 with ~L→ b a→b/1
    ... | ()
    ~stepback {G1' = f0} b a→c/1 with _~_.~R b a→b/0
    ... | _ , () , b'
    ~stepback {G1' = f1} b a→c/1 with ~R→ b a→c/1
    ... | ()
    ~stepback {G1' = f2} b a→c/1 with ~R→ b a→b/1
    ... | ()
    ~stepback {G1' = f3} b a→c/1 = f1 , ~refl , a→c/1
    ~stepback {G1' = f0} b a→b/1 with ~R→ b a→b/0
    ... | ()
    ~stepback {G1' = f1} b a→b/1 with ~R→ b a→c/1
    ... | ()
    ~stepback {G1' = f2} b a→b/1 with _~_.~R b a→b/1
    ... | _ , () , b'
    ~stepback {G1' = f3} b a→b/1 = f2 , ~refl , a→b/1

    diamond : ∀ {G} {α} {G₁} {α'} {G₂} →
          G -< α >-> G₁ →
          G -< α' >-> G₂ →
          α ∥ α' → ∃-syntax (λ G' → (G₁ -< α' >-> G') × (G₂ -< α >-> G'))
    diamond a→b/0 a→b/0 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond a→b/0 a→c/0 ii = s3 , a→c/1 , a→b/1
    diamond a→c/0 a→b/0 ii = s3 , a→b/1 , a→c/1
    diamond a→c/0 a→c/0 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond a→c/1 a→c/1 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond a→b/1 a→b/1 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)

    cond-comm : ∀ {hα} {i j : Fin (suc (nchoices hα))}
                    {α'} {G} {G'} {Gᵢ} {Gⱼ'} →
                  hα ∥ₕ proj₁ α' →
                  G -< α' >-> G' →
                  G -< hα , i >-> Gᵢ →
                  G' -< hα , j >-> Gⱼ' → ∃-syntax (_-<_>->_ G (hα , j))
    cond-comm ii a→b/0 a→c/0 a→c/1 = _ , a→c/0
    cond-comm ii a→c/0 a→b/0 a→b/1 = s1 , a→b/0

    IndepProto-Properties : BT-Prop IndepProtoTheory
    IndepProto-Properties .BT-Prop.recv-act-eq = recv-act-eq
    -- IndepProto-Properties .BT-Prop.send-act-indep = send-act-indep
    IndepProto-Properties .BT-Prop.snd≢rcv = snd≢rcv
    IndepProto-Properties .BT-Prop.step-det = step-det
    IndepProto-Properties .BT-Prop.~stepback = ~stepback
    IndepProto-Properties .BT-Prop.diamond = diamond
    IndepProto-Properties .BT-Prop.cond-comm = cond-comm

    -- The processes

  open Behaviours
  open Definitions.MPST Behaviours.IndepProto-Properties

  p/A : Proc 0 0
  p/A = ifp (is-zero (val (v/nat zero)))
          then
            (B ! _ , item < val v/unit >∙
             C ! _ , item < val v/unit >∙ ∅ )
          else
            (C ! _ , item < val v/unit >∙
             B ! _ , item < val v/unit >∙ ∅ )

  p/B : Proc 0 0
  p/B = Σ A ？[ s/itm ]· ( ∅ ∷ [])

  p/C : Proc 0 0
  p/C = Σ A ？[ s/itm ]· ( ∅ ∷ [])

  tt/end : ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{P}  →  Γ & Δ / s3 ↑ P ⊢p< ng > ∅
  tt/end = t/end (λ{ (BTheory.in/α () x₁) ; (BTheory.in/later () x₁) })

  t/A : [] & [] / s0 ↑ A ⊢p< ng > p/A
  t/A = t/if (te/is-zero (te/val tv/nat))
    (t/send a→b/0 (te/val tv/unit) (t/send a→c/1 (te/val tv/unit) tt/end))
    (t/send a→c/0 (te/val tv/unit) (t/send a→b/1 (te/val tv/unit) tt/end))

  t/B : [] & [] / s0 ↑ B ⊢p< ng > p/B
  t/B = t/recv R[ a→b/0 ] λ{ a→b/0 → t/end (λ{ (BTheory.in/α a→c/1 ≢R) ; (BTheory.in/α a→c/1 ≢S) ; (BTheory.in/later a→c/1 (BTheory.in/α () x₁)) ; (BTheory.in/later a→c/1 (BTheory.in/later () x₁)) }) }

  t/C : [] & [] / s0 ↑ C ⊢p< ng > p/C
  t/C = t/recv R[ a→c/0 ] λ{ a→c/0 → t/end (λ{ (BTheory.in/α a→b/1 ≢R) ; (BTheory.in/α a→b/1 ≢S) ; (BTheory.in/later a→b/1 (BTheory.in/α () x₁)) ; (BTheory.in/later a→b/1 (BTheory.in/later () x₁)) }) }
