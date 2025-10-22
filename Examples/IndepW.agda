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
  using (Dec; True ; False ; toWitnessFalse ; fromWitnessFalse ; fromWitness ; toWitness)
open import Relation.Binary.PropositionalEquality hiding ( [_] )

open import Utils
open import Definitions

module Examples.IndepW where

  module Behaviours where
    open import Definitions.Expr
    open import Definitions.Common(7)
    open import Definitions.Actions(7)

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
    S  = mk-fin 0 6
    A1 = mk-fin 1 6
    B1 = mk-fin 2 6
    C1 = mk-fin 3 6
    A2 = mk-fin 4 6
    B2 = mk-fin 5 6
    C2 = mk-fin 6 6


    -- The Protocol states
    IndepProto-State = Fin 7

    s0  = mk-fin 0 6
    s1  = mk-fin 1 6
    s2  = mk-fin 2 6
    s3  = mk-fin 3 6
    s4  = mk-fin 4 6
    s5  = mk-fin 5 6
    s6  = mk-fin 6 6


    -- The labels and their s/itm
    item = mk-fin 0 0
    s/itm = s/unit ∷ []

    -- The LTS
    open HeadAct

    data LTS : IndepProto-State → Part → Part → {I : ℕ} → Vec Sort (suc I)
         → Fin (suc I) → IndepProto-State → Set where
      s→a1    : LTS s0 S  A1 s/itm item s1

      s→a2/1  : LTS s1 S  A2 s/itm item s3
      a1→b1/1 : LTS s1 A1 B1 s/itm item s2

      s→a2/2  : LTS s2 S  A2 s/itm item s4
      b→c1/2  : LTS s2 B1 C1 s/itm item s1

      a1→b1/3 : LTS s3 A1 B1 s/itm item s4
      a2→b2/3 : LTS s3 A2 B2 s/itm item s5

      b1→c1/4 : LTS s4 B1 C1 s/itm item s3
      a2→b2/4 : LTS s4 A2 B2 s/itm item s6

      b2→c2/5 : LTS s5 B2 C2 s/itm item s3
      a1→b1/5 : LTS s5 A1 B1 s/itm item s6

      b1→c1/6 : LTS s6 B1 C1 s/itm item s5
      b2→c2/6 : LTS s6 B2 C2 s/itm item s4

    TheLTS : IndepProto-State → Action → IndepProto-State → Set
    TheLTS si (P ⟶ Q # S , i) so = LTS si P Q S i so

    IndepProtoTheory : BTheory 7
    IndepProtoTheory .BTheory.Behav = IndepProto-State
    IndepProtoTheory .BTheory._-<_>->_ = TheLTS

    open BTheory IndepProtoTheory

    pattern ≢S = ∈S ()
    pattern ≢R = ∈R ()

    pattern S≢S = inj₁ (∈S ())
    pattern S≢R = inj₁ (∈R ())

    pattern R≢S = inj₂ (∈S ())
    pattern R≢R = inj₂ (∈R ())

    can-step? : ∀ P B → Dec (P ∈tr B)
    can-step? f0 f0 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr s→a1 (∈S refl))
    can-step? f0 f1 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr s→a2/1 (∈S refl))
    can-step? f0 f2 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr s→a2/2 (∈S refl))
    can-step? f0 f3 = no (λ{ (BTheory.∈-tr a1→b1/3 ≢S)
                           ; (BTheory.∈-tr a1→b1/3 ≢R)
                           ; (BTheory.∈-tr a2→b2/3 ≢S)
                           ; (BTheory.∈-tr a2→b2/3 ≢R) })
    can-step? f0 f4 = no (λ{ (BTheory.∈-tr b1→c1/4 ≢S)
                           ; (BTheory.∈-tr b1→c1/4 ≢R)
                           ; (BTheory.∈-tr a2→b2/4 ≢S)
                           ; (BTheory.∈-tr a2→b2/4 ≢R) })
    can-step? f0 f5 = no (λ{ (BTheory.∈-tr b2→c2/5 ≢S)
                           ; (BTheory.∈-tr b2→c2/5 ≢R)
                           ; (BTheory.∈-tr a1→b1/5 ≢S)
                           ; (BTheory.∈-tr a1→b1/5 ≢R) })
    can-step? f0 f6 = no (λ{ (BTheory.∈-tr b1→c1/6 ≢S)
                           ; (BTheory.∈-tr b1→c1/6 ≢R)
                           ; (BTheory.∈-tr b2→c2/6 ≢S)
                           ; (BTheory.∈-tr b2→c2/6 ≢R) })
    can-step? f1 f0 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr s→a1 (∈R refl))
    can-step? f1 f1 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a1→b1/1 (∈S refl))
    can-step? f1 f2 = no (λ{ (BTheory.∈-tr s→a2/2 ≢S)
                           ; (BTheory.∈-tr s→a2/2 ≢R)
                           ; (BTheory.∈-tr b→c1/2 ≢S)
                           ; (BTheory.∈-tr b→c1/2 ≢R) })
    can-step? f1 f3 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a1→b1/3 (∈S refl))
    can-step? f1 f4 = no (λ{ (BTheory.∈-tr b1→c1/4 ≢S)
                           ; (BTheory.∈-tr b1→c1/4 ≢R)
                           ; (BTheory.∈-tr a2→b2/4 ≢S)
                           ; (BTheory.∈-tr a2→b2/4 ≢R) })
    can-step? f1 f5 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a1→b1/5 (∈S refl))
    can-step? f1 f6 = no (λ{ (BTheory.∈-tr b1→c1/6 ≢S)
                           ; (BTheory.∈-tr b1→c1/6 ≢R)
                           ; (BTheory.∈-tr b2→c2/6 ≢S)
                           ; (BTheory.∈-tr b2→c2/6 ≢R) })
    can-step? f2 f0 = no (λ{ (BTheory.∈-tr s→a1 ≢S)
                           ; (BTheory.∈-tr s→a1 ≢R) })
    can-step? f2 f1 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a1→b1/1 (∈R refl))
    can-step? f2 f2 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr b→c1/2 (∈S refl))
    can-step? f2 f3 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a1→b1/3 (∈R refl))
    can-step? f2 f4 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr b1→c1/4 (∈S refl))
    can-step? f2 f5 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a1→b1/5 (∈R refl))
    can-step? f2 f6 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr b1→c1/6 (∈S refl))
    can-step? f3 f0 = no (λ{ (BTheory.∈-tr s→a1 ≢S)
                           ; (BTheory.∈-tr s→a1 ≢R) })
    can-step? f3 f1 = no (λ{ (BTheory.∈-tr s→a2/1 ≢S)
                           ; (BTheory.∈-tr s→a2/1 ≢R)
                           ; (BTheory.∈-tr a1→b1/1 ≢S)
                           ; (BTheory.∈-tr a1→b1/1 ≢R) })
    can-step? f3 f2 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr b→c1/2 (∈R refl))
    can-step? f3 f3 = no (λ{ (BTheory.∈-tr a1→b1/3 ≢S)
                           ; (BTheory.∈-tr a1→b1/3 ≢R)
                           ; (BTheory.∈-tr a2→b2/3 ≢S)
                           ; (BTheory.∈-tr a2→b2/3 ≢R) })
    can-step? f3 f4 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr b1→c1/4 (∈R refl))
    can-step? f3 f5 = no (λ{ (BTheory.∈-tr b2→c2/5 ≢S)
                           ; (BTheory.∈-tr b2→c2/5 ≢R)
                           ; (BTheory.∈-tr a1→b1/5 ≢S)
                           ; (BTheory.∈-tr a1→b1/5 ≢R) })
    can-step? f3 f6 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr b1→c1/6 (∈R refl))
    can-step? f4 f0 = no (λ{ (BTheory.∈-tr s→a1 ≢S)
                           ; (BTheory.∈-tr s→a1 ≢R) })
    can-step? f4 f1 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr s→a2/1 (∈R refl))
    can-step? f4 f2 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr s→a2/2 (∈R refl))
    can-step? f4 f3 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a2→b2/3 (∈S refl))
    can-step? f4 f4 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a2→b2/4 (∈S refl))
    can-step? f4 f5 = no (λ{ (BTheory.∈-tr b2→c2/5 ≢S)
                           ; (BTheory.∈-tr b2→c2/5 ≢R)
                           ; (BTheory.∈-tr a1→b1/5 ≢S)
                           ; (BTheory.∈-tr a1→b1/5 ≢R) })
    can-step? f4 f6 = no (λ{ (BTheory.∈-tr b1→c1/6 ≢S)
                           ; (BTheory.∈-tr b1→c1/6 ≢R)
                           ; (BTheory.∈-tr b2→c2/6 ≢S)
                           ; (BTheory.∈-tr b2→c2/6 ≢R) })
    can-step? f5 f0 = no (λ{ (BTheory.∈-tr s→a1 ≢S)
                           ; (BTheory.∈-tr s→a1 ≢R) })
    can-step? f5 f1 = no (λ{ (BTheory.∈-tr s→a2/1 ≢S)
                           ; (BTheory.∈-tr s→a2/1 ≢R)
                           ; (BTheory.∈-tr a1→b1/1 ≢S)
                           ; (BTheory.∈-tr a1→b1/1 ≢R) })
    can-step? f5 f2 = no (λ{ (BTheory.∈-tr s→a2/2 ≢S)
                           ; (BTheory.∈-tr s→a2/2 ≢R)
                           ; (BTheory.∈-tr b→c1/2 ≢S)
                           ; (BTheory.∈-tr b→c1/2 ≢R) })
    can-step? f5 f3 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a2→b2/3 (∈R refl))
    can-step? f5 f4 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a2→b2/4 (∈R refl))
    can-step? f5 f5 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr b2→c2/5 (∈S refl))
    can-step? f5 f6 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr b2→c2/6 (∈S refl))
    can-step? f6 f0 = no (λ{ (BTheory.∈-tr s→a1 ≢S)
                           ; (BTheory.∈-tr s→a1 ≢R) })
    can-step? f6 f1 = no (λ{ (BTheory.∈-tr s→a2/1 ≢S)
                           ; (BTheory.∈-tr s→a2/1 ≢R)
                           ; (BTheory.∈-tr a1→b1/1 ≢S)
                           ; (BTheory.∈-tr a1→b1/1 ≢R) })
    can-step? f6 f2 = no (λ{ (BTheory.∈-tr s→a2/2 ≢S)
                           ; (BTheory.∈-tr s→a2/2 ≢R)
                           ; (BTheory.∈-tr b→c1/2 ≢S)
                           ; (BTheory.∈-tr b→c1/2 ≢R) })
    can-step? f6 f3 = no (λ{ (BTheory.∈-tr a1→b1/3 ≢S)
                           ; (BTheory.∈-tr a1→b1/3 ≢R)
                           ; (BTheory.∈-tr a2→b2/3 ≢S)
                           ; (BTheory.∈-tr a2→b2/3 ≢R) })
    can-step? f6 f4 = no (λ{ (BTheory.∈-tr b1→c1/4 ≢S)
                           ; (BTheory.∈-tr b1→c1/4 ≢R)
                           ; (BTheory.∈-tr a2→b2/4 ≢S)
                           ; (BTheory.∈-tr a2→b2/4 ≢R) })
    can-step? f6 f5 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr b2→c2/5 (∈R refl))
    can-step? f6 f6 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr b2→c2/6 (∈R refl))

    -- The properties
    --
    open _~_
    ~≡ : ∀ G G' → G ~ G' → G ≡ G'
    ~≡ f0 f0 b = refl
    ~≡ f0 ss0 b with ~L b s→a1
    ... | _ , () , _
    ~≡ f1 f0 b with ~R b s→a1
    ... | _ , () , _
    ~≡ f1 f1 b = refl
    ~≡ f1 f2 b with ~R b b→c1/2
    ... | _ , () , _
    ~≡ f1 ss2 b with ~L b s→a2/1
    ... | _ , () , _
    ~≡ f2 f0 b with ~R b s→a1
    ... | _ , () , _
    ~≡ f2 f1 b with ~R b a1→b1/1
    ... | _ , () , _
    ~≡ f2 f2 b = refl
    ~≡ f2 ss2 b with ~L b s→a2/2
    ... | _ , () , _
    ~≡ f3 f0 b with ~R b s→a1
    ... | _ , () , _
    ~≡ f3 f1 b with ~R b s→a2/1
    ... | _ , () , _
    ~≡ f3 f2 b with ~R b s→a2/2
    ... | _ , () , _
    ~≡ f3 f3 b = refl
    ~≡ f3 f4 b with ~R b b1→c1/4
    ... | _ , () , _
    ~≡ f3 ss4 b with ~L b a2→b2/3
    ... | _ , () , _
    ~≡ f4 f0 b with ~R b s→a1
    ... | _ , () , _
    ~≡ f4 f1 b with ~R b a1→b1/1
    ... | _ , () , _
    ~≡ f4 f2 b with ~R b s→a2/2
    ... | _ , () , _
    ~≡ f4 f3 b with ~R b a1→b1/3
    ... | _ , () , _
    ~≡ f4 f4 b = refl
    ~≡ f4 ss4 b with ~L b a2→b2/4
    ... | _ , () , _
    ~≡ f5 f0 b with ~R b s→a1
    ... | _ , () , _
    ~≡ f5 f1 b with ~R b s→a2/1
    ... | _ , () , _
    ~≡ f5 f2 b with ~R b s→a2/2
    ... | _ , () , _
    ~≡ f5 f3 b with ~R b a2→b2/3
    ... | _ , () , _
    ~≡ f5 f4 b with ~R b b1→c1/4
    ... | _ , () , _
    ~≡ f5 f5 b = refl
    ~≡ f5 ss5 b with ~L b a1→b1/5
    ... | _ , () , _
    ~≡ f6 f0 b with ~R b s→a1
    ... | _ , () , _
    ~≡ f6 f1 b with ~R b a1→b1/1
    ... | _ , () , _
    ~≡ f6 f2 b with ~R b s→a2/2
    ... | _ , () , _
    ~≡ f6 f3 b with ~R b a2→b2/3
    ... | _ , () , _
    ~≡ f6 f4 b with ~R b a2→b2/4
    ... | _ , () , _
    ~≡ f6 f5 b with ~R b a1→b1/5
    ... | _ , () , _
    ~≡ f6 f6 b = refl

    indep? : ∀ {G} {α} {α'} {G'} {G''} →
         G -< α >-> G' → G -< α' >-> G'' → ((proj₁ α) ⋔ (proj₁ α')) ⊎ proj₁ α ≡ proj₁ α'
    indep? s→a1 s→a1 = inj₂ refl
    indep? s→a2/1 s→a2/1 = inj₂ refl
    indep? s→a2/1 a1→b1/1 = inj₁ (λ{ S≢S ; S≢R ; R≢S ; R≢R })
    indep? a1→b1/1 s→a2/1 = inj₁ (λ{ S≢S ; S≢R ; R≢S ; R≢R })
    indep? a1→b1/1 a1→b1/1 = inj₂ refl
    indep? s→a2/2 s→a2/2 = inj₂ refl
    indep? s→a2/2 b→c1/2 = inj₁ (λ{ S≢S ; S≢R ; R≢S ; R≢R })
    indep? b→c1/2 s→a2/2 = inj₁ (λ{ S≢S ; S≢R ; R≢S ; R≢R })
    indep? b→c1/2 b→c1/2 = inj₂ refl
    indep? a1→b1/3 a1→b1/3 = inj₂ refl
    indep? a1→b1/3 a2→b2/3 = inj₁ (λ{ S≢S ; S≢R ; R≢S ; R≢R })
    indep? a2→b2/3 a1→b1/3 = inj₁ (λ{ S≢S ; S≢R ; R≢S ; R≢R })
    indep? a2→b2/3 a2→b2/3 = inj₂ refl
    indep? b1→c1/4 b1→c1/4 = inj₂ refl
    indep? b1→c1/4 a2→b2/4 = inj₁ (λ{ S≢S ; S≢R ; R≢S ; R≢R })
    indep? a2→b2/4 b1→c1/4 = inj₁ (λ{ S≢S ; S≢R ; R≢S ; R≢R })
    indep? a2→b2/4 a2→b2/4 = inj₂ refl
    indep? b2→c2/5 b2→c2/5 = inj₂ refl
    indep? b2→c2/5 a1→b1/5 = inj₁ (λ{ S≢S ; S≢R ; R≢S ; R≢R })
    indep? a1→b1/5 b2→c2/5 = inj₁ (λ{ S≢S ; S≢R ; R≢S ; R≢R })
    indep? a1→b1/5 a1→b1/5 = inj₂ refl
    indep? b1→c1/6 b1→c1/6 = inj₂ refl
    indep? b1→c1/6 b2→c2/6 = inj₁ (λ{ S≢S ; S≢R ; R≢S ; R≢R })
    indep? b2→c2/6 b1→c1/6 = inj₁ (λ{ S≢S ; S≢R ; R≢S ; R≢R })
    indep? b2→c2/6 b2→c2/6 = inj₂ refl

    snd≢rcv : ∀ {G} {G'} {α} → G -< α >-> G' → sender α ≢ receiver α
    snd≢rcv () refl

    step-det : ∀ {G} {α} {G'} {G''} →
           G -< α >-> G' → G -< α >-> G'' → G' ≡ G''
    step-det s→a1 s→a1 = refl
    step-det s→a2/1 s→a2/1 = refl
    step-det a1→b1/1 a1→b1/1 = refl
    step-det s→a2/2 s→a2/2 = refl
    step-det b→c1/2 b→c1/2 = refl
    step-det a1→b1/3 a1→b1/3 = refl
    step-det a2→b2/3 a2→b2/3 = refl
    step-det b1→c1/4 b1→c1/4 = refl
    step-det a2→b2/4 a2→b2/4 = refl
    step-det b2→c2/5 b2→c2/5 = refl
    step-det a1→b1/5 a1→b1/5 = refl
    step-det b1→c1/6 b1→c1/6 = refl
    step-det b2→c2/6 b2→c2/6 = refl

    ~stepback : ∀ {α} {G0} {G1} {G1'} →
            G1 ~ G1' →
            G0 -< α >-> G1 → ∃-syntax (λ G0' → (G0 ~ G0') × (G0' -< α >-> G1'))
    ~stepback x x₁ with ~≡ _ _ x
    ... | refl = _ , ~refl , x₁

    diamond : ∀ {G} {α} {G₁} {α'} {G₂} →
          G -< α >-> G₁ →
          G -< α' >-> G₂ →
          α ∥ α' → ∃-syntax (λ G' → (G₁ -< α' >-> G') × (G₂ -< α >-> G'))
    diamond s→a1 s→a1 ii       = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond s→a2/1 s→a2/1 ii   = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond s→a2/1 a1→b1/1 ii  = s4 , a1→b1/3 , s→a2/2
    diamond a1→b1/1 s→a2/1 ii  = s4 , s→a2/2 , a1→b1/3
    diamond a1→b1/1 a1→b1/1 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond s→a2/2 s→a2/2 ii   = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond s→a2/2 b→c1/2 ii   = s3 , b1→c1/4 , s→a2/1
    diamond b→c1/2 s→a2/2 ii   = s3 , s→a2/1 , b1→c1/4
    diamond b→c1/2 b→c1/2 ii   = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond a1→b1/3 a1→b1/3 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond a1→b1/3 a2→b2/3 ii = s6 , a2→b2/4 , a1→b1/5
    diamond a2→b2/3 a1→b1/3 ii = s6 , a1→b1/5 , a2→b2/4
    diamond a2→b2/3 a2→b2/3 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond b1→c1/4 b1→c1/4 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond b1→c1/4 a2→b2/4 ii = s5 , a2→b2/3 , b1→c1/6
    diamond a2→b2/4 b1→c1/4 ii = s5 , b1→c1/6 , a2→b2/3
    diamond a2→b2/4 a2→b2/4 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond b2→c2/5 b2→c2/5 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond b2→c2/5 a1→b1/5 ii = s4 , a1→b1/3 , b2→c2/6
    diamond a1→b1/5 b2→c2/5 ii = s4 , b2→c2/6 , a1→b1/3
    diamond a1→b1/5 a1→b1/5 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond b1→c1/6 b1→c1/6 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond b1→c1/6 b2→c2/6 ii = s3 , b2→c2/5 , b1→c1/4
    diamond b2→c2/6 b1→c1/6 ii = s3 , b1→c1/4 , b2→c2/5
    diamond b2→c2/6 b2→c2/6 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)

    cond-comm : ∀ {hα} {i j : Fin (suc (nchoices hα))}
                    {α'} {G} {G'} {Gᵢ} {Gⱼ'} →
                  hα ∥ₕ proj₁ α' →
                  G -< α' >-> G' →
                  G -< hα , i >-> Gᵢ →
                  G' -< hα , j >-> Gⱼ' → ∃-syntax (_-<_>->_ G (hα , j))
    cond-comm ii s→a1 s→a1       z = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    cond-comm ii s→a2/1 a1→b1/1 a1→b1/3 = s2 , a1→b1/1
    cond-comm ii a1→b1/1 s→a2/1 s→a2/2 = s3 , s→a2/1
    cond-comm ii s→a2/2 b→c1/2 b1→c1/4 = s1 , b→c1/2
    cond-comm ii b→c1/2 s→a2/2 s→a2/1 = s4 , s→a2/2
    cond-comm ii a1→b1/3 a2→b2/3 a2→b2/4 = s5 , a2→b2/3
    cond-comm ii a2→b2/3 a1→b1/3 a1→b1/5 = s4 , a1→b1/3
    cond-comm ii b1→c1/4 a2→b2/4 a2→b2/3 = s6 , a2→b2/4
    cond-comm ii a2→b2/4 b1→c1/4 b1→c1/6 = s3 , b1→c1/4
    cond-comm ii b2→c2/5 a1→b1/5 a1→b1/3 = s6 , a1→b1/5
    cond-comm ii a1→b1/5 b2→c2/5 b2→c2/6 = s3 , b2→c2/5
    cond-comm ii b1→c1/6 b2→c2/6 b2→c2/5 = s4 , b2→c2/6
    cond-comm ii b2→c2/6 b1→c1/6 b1→c1/4 = s5 , b1→c1/6

    IndepProto-Properties : BT-Prop IndepProtoTheory
    IndepProto-Properties .BT-Prop.recv-act-eq x x₁ x₂ with indep? x x₁
    ... | inj₁ ii = ⊥-elim (ii (inj₂ x₂))
    ... | inj₂ refl = refl
    IndepProto-Properties .BT-Prop.snd≢rcv = snd≢rcv
    IndepProto-Properties .BT-Prop.step-det = step-det
    IndepProto-Properties .BT-Prop.~stepback = ~stepback
    IndepProto-Properties .BT-Prop.diamond = diamond
    IndepProto-Properties .BT-Prop.cond-comm = cond-comm

    Extra : BT-Extra IndepProtoTheory
    Extra .BT-Extra.can-step? = can-step?

  open Behaviours
  open MPST Behaviours.IndepProto-Properties
  open Definitions.MPST-Extra Behaviours.IndepProto-Properties Behaviours.Extra
  open BT-Extra Behaviours.Extra

  mutual
    s0∉Ts6 : s0 ∉T s6
    s0∉Ts6 (BTheory.in/α b1→c1/6 ≢S)
    s0∉Ts6 (BTheory.in/α b2→c2/6 ≢S)
    s0∉Ts6 (BTheory.in/α b1→c1/6 ≢R)
    s0∉Ts6 (BTheory.in/α b2→c2/6 ≢R)
    s0∉Ts6 (BTheory.in/later b1→c1/6 x₁) = s0∉Ts5 x₁
    s0∉Ts6 (BTheory.in/later b2→c2/6 x₁) = s0∉Ts4 x₁

    s0∉Ts5 : s0 ∉T s5
    s0∉Ts5 (BTheory.in/α b2→c2/5 ≢S)
    s0∉Ts5 (BTheory.in/α a1→b1/5 ≢S)
    s0∉Ts5 (BTheory.in/α b2→c2/5 ≢R)
    s0∉Ts5 (BTheory.in/α a1→b1/5 ≢R)
    s0∉Ts5 (BTheory.in/later b2→c2/5 x₁) = s0∉Ts3 x₁
    s0∉Ts5 (BTheory.in/later a1→b1/5 x₁) = s0∉Ts6 x₁

    s0∉Ts4 : s0 ∉T s4
    s0∉Ts4 (BTheory.in/α b1→c1/4 ≢S)
    s0∉Ts4 (BTheory.in/α a2→b2/4 ≢S)
    s0∉Ts4 (BTheory.in/α b1→c1/4 ≢R)
    s0∉Ts4 (BTheory.in/α a2→b2/4 ≢R)
    s0∉Ts4 (BTheory.in/later b1→c1/4 x₁) = s0∉Ts3 x₁
    s0∉Ts4 (BTheory.in/later a2→b2/4 x₁) = s0∉Ts6 x₁

    s0∉Ts3 : s0 ∉T s3
    s0∉Ts3 (BTheory.in/α a1→b1/3 ≢S)
    s0∉Ts3 (BTheory.in/α a2→b2/3 ≢S)
    s0∉Ts3 (BTheory.in/α a1→b1/3 ≢R)
    s0∉Ts3 (BTheory.in/α a2→b2/3 ≢R)
    s0∉Ts3 (BTheory.in/later a1→b1/3 x₁) = s0∉Ts4 x₁
    s0∉Ts3 (BTheory.in/later a2→b2/3 x₁) = s0∉Ts5 x₁


  p/S : Proc 0 0
  p/S = A1 ! _ , item < val v/unit >∙
        A2 ! _ , item < val v/unit >∙
        ∅

  p/C : ∀ {γ} → Part → Proc γ 0
  p/C B = rec (Σ B ？[ s/itm ]· ( v zero ∷ [] ))

  p/B : ∀ {γ} → Part → Part → Proc γ 0
  p/B A C = rec (Σ A ？[ s/itm ]·
            ( (C ! _ , item < val v/unit >∙ v zero)
            ∷ []
            ))

  p/A : Part → Proc 0 0
  p/A B = Σ S ？[ s/itm ]·
            ( B ! _ , item < val v/unit >∙ ( rec (B ! _ , item < val v/unit >∙ v zero) ) -- TODO: fix this manual unfolding
            ∷ []
            )

  tl-until : ∀{G0 G1 G2}{P : Part}{α}(a0 : G0 -< α >-> G1){tr : G1 ~~> G2} → True (unrelated? P (a0 ► tr)) → True (unrelated? P tr)
  tl-until _ x with toWitness x
  ... | (_ , x) = fromWitness x

  tl-sk : ∀{G0 G1 G2}{P : Part}{α}(a0 : G0 -< α >-> G1){tr : G1 ~~> G2} → True (skippable? P (a0 ► tr)) → True (skippable? P tr)
  tl-sk _ x with toWitness x
  ... | (_ , x) = fromWitness x

--- TYD of S

  t/S : [] & [] / s0 ↑ S ⊢p< ng > p/S
  t/S = t/send s→a1 (te/val tv/unit) (t/send s→a2/1 (te/val tv/unit) (t/end s0∉Ts3))


-- TYD of A1

  module TYD-A1 where
   mutual
     CC2 : Causal? s2 A1 B1
     CC2 BTheory.■ U P∉G′ BTheory.■ () x₁
     CC2 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
     CC2 (s→a2/2 BTheory.► tr) U P∉G′ tr' x x₁ = CC4 tr (tl-until s→a2/2 U) P∉G′ tr' x x₁
     CC2 (b→c1/2 BTheory.► tr) U P∉G′ tr' x x₁ = CC1 tr (tl-until b→c1/2 U) P∉G′ tr' x x₁

     CC4 : Causal? s4 A1 B1
     CC4 BTheory.■ U P∉G′ BTheory.■ () x₁
     CC4 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
     CC4 (b1→c1/4 BTheory.► tr) U P∉G′ tr' x x₁ = CC3 tr (tl-until b1→c1/4 U) P∉G′ tr' x x₁
     CC4 (a2→b2/4 BTheory.► tr) U P∉G′ tr' x x₁ = CC6 tr (tl-until a2→b2/4 U) P∉G′ tr' x x₁

     CC1 : Causal? s1 A1 B1
     CC1 (s→a2/1 BTheory.► tr) U P∉G′ tr' x x₁ = CC3 tr (tl-until s→a2/1 U) P∉G′ tr' x x₁

     CC3 : Causal? s3 A1 B1
     CC3 (a2→b2/3 BTheory.► tr) U P∉G′ tr' x x₁ = CC5 tr (tl-until a2→b2/3 U) P∉G′ tr' x x₁

     CC6 : Causal?  s6 A1 B1
     CC6 BTheory.■ U P∉G′ BTheory.■ () x₁
     CC6 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
     CC6 (b1→c1/6 BTheory.► tr) U P∉G′ tr' x x₁ = CC5 tr (tl-until b1→c1/6 U) P∉G′ tr' x x₁
     CC6 (b2→c2/6 BTheory.► tr) U P∉G′ tr' x x₁ = CC4 tr (tl-until b2→c2/6 U) P∉G′ tr' x x₁

     CC5 : Causal? s5 A1 B1
     CC5 (b2→c2/5 BTheory.► tr) U P∉G′ tr' x x₁ = CC3 tr (tl-until b2→c2/5 U) P∉G′ tr' x x₁

   mutual
     AA2 : Active? s2 A1
     AA2 BTheory.■ x = Active (b→c1/2 _~~>_.► _~~>_.■)
     AA2 (s→a2/2 BTheory.► tr) x = AA4 tr (tl-until s→a2/2 x)
     AA2 (b→c1/2 BTheory.► tr) x = AA1 tr (tl-until b→c1/2 x)

     AA4 : Active? s4 A1
     AA4 BTheory.■ x = Active (b1→c1/4 _~~>_.► _~~>_.■)
     AA4 (b1→c1/4 BTheory.► tr) x = AA3 tr (tl-until b1→c1/4 x)
     AA4 (a2→b2/4 BTheory.► tr) x = AA6 tr (tl-until a2→b2/4 x)

     AA1 : Active? s1 A1
     AA1 BTheory.■ x = Active _~~>_.■
     AA1 (s→a2/1 BTheory.► tr) x = AA3 tr (tl-until s→a2/1 x)

     AA3 : Active? s3 A1
     AA3 BTheory.■ x = Active _~~>_.■
     AA3 (a2→b2/3 BTheory.► tr) x = AA5 tr (tl-until a2→b2/3 x)

     AA6 : Active? s6 A1
     AA6 BTheory.■ x = Active (b2→c2/6 _~~>_.► b1→c1/4 _~~>_.► _~~>_.■)
     AA6 (b1→c1/6 BTheory.► tr) x = AA5 tr (tl-until b1→c1/6 x)
     AA6 (b2→c2/6 BTheory.► tr) x = AA4 tr (tl-until b2→c2/6 x)

     AA5 : Active? s5 A1
     AA5 BTheory.■ x = Active _~~>_.■
     AA5 (b2→c2/5 BTheory.► tr) x = AA3 tr (tl-until b2→c2/5 x)

   mutual
     tK2 : ∀ {B} → (tr : s2 ~~> B) → True (skippable? A1 tr) → (s/unit ∷ []) & s2 ∷ [] / B ↑ A1  ⊢p< mg > (B1 ! 0 , item < val v/unit >∙ v f0)
     tK2 (s→a2/2 BTheory.► tr) x = tK4 tr (tl-sk s→a2/2 x)
     tK2 (b→c1/2 BTheory.► tr) x = tK1 tr (tl-sk b→c1/2 x)
     tK4 : ∀ {B} → (tr : s4 ~~> B) → (sk : True (skippable? A1 tr)) → (s/unit ∷ []) & s2 ∷ [] / B ↑ A1  ⊢p< mg > (B1 ! 0 , item < val v/unit >∙ v f0)
     tK4 (b1→c1/4 BTheory.► tr) sk = tK3 tr (tl-sk b1→c1/4 sk)
     tK4 (a2→b2/4 BTheory.► tr) sk = tK6 tr (tl-sk a2→b2/4 sk)
     tK1 : ∀ {B} → (tr : s1 ~~> B) → (sk : True (skippable? A1 tr)) → (s/unit ∷ []) & s2 ∷ [] / B ↑ A1  ⊢p< mg > (B1 ! 0 , item < val v/unit >∙ v f0)
     tK1 BTheory.■ sk = t/send a1→b1/1 (te/val tv/unit) (t/var ~refl (_~~>_.■ , sk))
     tK3 : ∀ {B} → (tr : s3 ~~> B) → (sk : True (skippable? A1 tr)) → (s/unit ∷ []) & s2 ∷ [] / B ↑ A1  ⊢p< mg > (B1 ! 0 , item < val v/unit >∙ v f0)
     tK3 BTheory.■ sk = t/send a1→b1/3 (te/val tv/unit) (t/var ~refl ((s→a2/2 _~~>_.► _~~>_.■) , (λ{ ≢S; ≢R }) , tt))
     tK6 : ∀ {B} → (tr : s6 ~~> B) → (sk : True (skippable? A1 tr)) → (s/unit ∷ []) & s2 ∷ [] / B ↑ A1  ⊢p< mg > (B1 ! 0 , item < val v/unit >∙ v f0)
     tK6 (b1→c1/6 BTheory.► tr) sk = tK5 tr (tl-sk b1→c1/6 sk)
     tK6 (b2→c2/6 BTheory.► tr) sk = tK4 tr (tl-sk b2→c2/6 sk)
     tK5 : ∀ {B} → (tr : s5 ~~> B) → (sk : True (skippable? A1 tr)) → (s/unit ∷ []) & s2 ∷ [] / B ↑ A1  ⊢p< mg > (B1 ! 0 , item < val v/unit >∙ v f0)
     tK5 BTheory.■ sk = t/send a1→b1/5 (te/val tv/unit) (t/var ~refl ((s→a2/2 _~~>_.► a2→b2/4 _~~>_.► _~~>_.■) , (λ{ ≢S; ≢R }) , ((λ{ ≢S; ≢R }) , tt)))

   t/A1 : [] & [] / s0 ↑ A1 ⊢p< ng > (p/A B1)
   t/A1 = t/recv R[ s→a1 ] (λ{ s→a1 →
       t/send a1→b1/1 (te/val tv/unit) (t/rec rt/refl (dt/skip B1 CC2 AA2 λ tr {sk} → tK2 tr sk ))})

-- TYD of B1

  module TYD-B1 where

    mutual
      CC0 : Causal? s0 B1 A1
      CC0 BTheory.■ U P∉G′ BTheory.■ () x₁
      CC0 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
      CC0 (s→a1 BTheory.► tr) U P∉G′ tr' x x₁ = CC1 tr (tl-until s→a1 U) P∉G′ tr' x x₁
      CC1 : Causal? s1 B1 A1
      CC1 (s→a2/1 BTheory.► tr) U P∉G′ tr' x x₁ = CC3 tr (tl-until s→a2/1 U) P∉G′ tr' x x₁
      CC3 : Causal? s3 B1 A1
      CC3 (a2→b2/3 BTheory.► tr) U P∉G′ tr' x x₁ = CC5 tr (tl-until a2→b2/3 U) P∉G′ tr' x x₁
      CC5 : Causal? s5 B1 A1
      CC5 (b2→c2/5 BTheory.► tr) U P∉G′ tr' x x₁ = CC3 tr (tl-until b2→c2/5 U) P∉G′ tr' x x₁

    mutual
      AA0 : Active? s0 B1
      AA0 BTheory.■ x = Active (s→a1 _~~>_.► _~~>_.■)
      AA0 (s→a1 BTheory.► tr) x = AA1 tr (tl-until s→a1 x)
      AA2 : Active? s2 B1
      AA2 BTheory.■ x = Active _~~>_.■
      AA2 (s→a2/2 BTheory.► tr) x = AA4 tr (tl-until s→a2/2 x)
      AA4 : Active? s4 B1
      AA4 BTheory.■ x = Active _~~>_.■
      AA4 (a2→b2/4 BTheory.► tr) x = AA6 tr (tl-until a2→b2/4 x)

      AA1 : Active? s1 B1
      AA1 BTheory.■ x = Active _~~>_.■
      AA1 (s→a2/1 BTheory.► tr) x = AA3 tr (tl-until s→a2/1 x)

      AA3 : Active? s3 B1
      AA3 BTheory.■ x = Active _~~>_.■
      AA3 (a2→b2/3 BTheory.► tr) x = AA5 tr (tl-until a2→b2/3 x)

      AA6 : Active? s6 B1
      AA6 BTheory.■ x = Active _~~>_.■
      AA6 (b2→c2/6 BTheory.► tr) x = AA4 tr (tl-until b2→c2/6 x)

      AA5 : Active? s5 B1
      AA5 BTheory.■ x = Active _~~>_.■
      AA5 (b2→c2/5 BTheory.► tr) x = AA3 tr (tl-until b2→c2/5 x)



    mutual
      t/B1 : [] & [] / s0 ↑ B1 ⊢p< ng > (p/B A1 C1)
      t/B1 = t/rec rt/refl (dt/skip A1 CC0 AA0 λ tr {sk} → tK0 tr sk)

      tK0 : ∀ {G'} (tr : s0 ~~> G') (sk : True (skippable? B1 tr)) →
        [] & s0 ∷ [] / G' ↑ B1 ⊢p< mg > (Σ A1 ？[ s/itm ]· (C1 ! 0 , item < val v/unit >∙ v f0 ∷ []))
      tK0 (s→a1 BTheory.► BTheory.■) sk = t/recv R[ a1→b1/1 ] λ{ a1→b1/1 → t/send b→c1/2 (te/val tv/unit) (t/var ~refl ((s→a1 _~~>_.► _~~>_.■) , (λ{ ≢S; ≢R }) , tt)) }

-- TYD of C1

  module TYD-C1 where

    mutual
      CC0 : Causal? s0 C1 B1
      CC0 BTheory.■ U P∉G′ (s→a1 BTheory.► BTheory.■) () x₁
      CC0 BTheory.■ U P∉G′ (s→a1 BTheory.► x₂ BTheory.► tr') x ()
      CC0 (s→a1 BTheory.► tr) U P∉G′ tr' x x₁ = CC1 tr (tl-until s→a1 U) P∉G′ tr' x x₁
      CC1 : Causal? s1 C1 B1
      CC1 BTheory.■ U P∉G′ BTheory.■ () x₁
      CC1 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
      CC1 (s→a2/1 BTheory.► tr) U P∉G′ tr' x x₁ = CC3 tr (tl-until s→a2/1 U) P∉G′ tr' x x₁
      CC1 (a1→b1/1 BTheory.► tr) U P∉G′ tr' x x₁ = CC2 tr (tl-until a1→b1/1 U) P∉G′ tr' x x₁

      CC3 : Causal? s3 C1 B1
      CC3 BTheory.■ U P∉G′ BTheory.■ () x₁
      CC3 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
      CC3 (a1→b1/3 BTheory.► tr) U P∉G′ tr' x x₁ = CC4 tr (tl-until a1→b1/3 U) P∉G′ tr' x x₁
      CC3 (a2→b2/3 BTheory.► tr) U P∉G′ tr' x x₁ = CC5 tr (tl-until a2→b2/3 U) P∉G′ tr' x x₁
      CC5 : Causal? s5 C1 B1
      CC5 BTheory.■ U P∉G′ BTheory.■ () x₁
      CC5 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
      CC5 (b2→c2/5 BTheory.► tr) U P∉G′ tr' x x₁ = CC3 tr (tl-until b2→c2/5 U) P∉G′ tr' x x₁
      CC5 (a1→b1/5 BTheory.► tr) U P∉G′ tr' x x₁ = CC6 tr (tl-until a1→b1/5 U) P∉G′ tr' x x₁

      CC2 : Causal? s2 C1 B1
      CC2 (s→a2/2 BTheory.► tr) U P∉G′ tr' x x₁ = CC4 tr (tl-until s→a2/2 U) P∉G′ tr' x x₁
      CC4 : Causal? s4 C1 B1
      CC4 (a2→b2/4 BTheory.► tr) U P∉G′ tr' x x₁ = CC6 tr (tl-until a2→b2/4 U) P∉G′ tr' x x₁
      CC6 : Causal? s6 C1 B1
      CC6 (b2→c2/6 BTheory.► tr) U P∉G′ tr' x x₁ = CC4 tr (tl-until b2→c2/6 U) P∉G′ tr' x x₁

    mutual
      AA0 : Active? s0 C1
      AA0 BTheory.■ x = Active (s→a1 _~~>_.► a1→b1/1 _~~>_.► _~~>_.■)
      AA0 (s→a1 BTheory.► tr) x = AA1 tr (tl-until s→a1 x)

      AA2 : Active? s2 C1
      AA2 BTheory.■ x = Active _~~>_.■
      AA2 (s→a2/2 BTheory.► tr) x = AA4 tr (tl-until s→a2/2 x)

      AA4 : Active? s4 C1
      AA4 BTheory.■ x = Active _~~>_.■
      AA4 (a2→b2/4 BTheory.► tr) x = AA6 tr (tl-until a2→b2/4 x)

      AA1 : Active? s1 C1
      AA1 BTheory.■ x = Active (a1→b1/1 _~~>_.► _~~>_.■)
      AA1 (s→a2/1 BTheory.► tr) x = AA3 tr (tl-until s→a2/1 x)
      AA1 (a1→b1/1 BTheory.► tr) x = AA2 tr (tl-until a1→b1/1 x)

      AA3 : Active? s3 C1
      AA3 BTheory.■ x = Active (a1→b1/3 _~~>_.► _~~>_.■)
      AA3 (a1→b1/3 BTheory.► tr) x = AA4 tr (tl-until a1→b1/3 x)
      AA3 (a2→b2/3 BTheory.► tr) x = AA5 tr (tl-until a2→b2/3 x)

      AA6 : Active? s6 C1
      AA6 BTheory.■ x = Active _~~>_.■
      AA6 (b2→c2/6 BTheory.► tr) x = AA4 tr (tl-until b2→c2/6 x)

      AA5 : Active? s5 C1
      AA5 BTheory.■ x = Active (b2→c2/5 _~~>_.► a1→b1/3 _~~>_.► _~~>_.■)
      AA5 (b2→c2/5 BTheory.► tr) x = AA3 tr (tl-until b2→c2/5 x)
      AA5 (a1→b1/5 BTheory.► tr) x = AA6 tr (tl-until a1→b1/5 x)



    mutual
      t/C1 : [] & [] / s0 ↑ C1 ⊢p< ng > (p/C B1)
      t/C1 = t/rec rt/refl (dt/skip B1 CC0 AA0 λ tr {sk} → tK0 tr sk)

      tK0 : ∀ {G' : IndepProto-State} (tr : s0 ~~> G')
        (sk : True (skippable? C1 tr)) → [] & s0 ∷ [] / G' ↑ C1 ⊢p< mg > (Σ B1 ？[ s/itm ]· (v f0 ∷ []))
      tK0 (s→a1 BTheory.► s→a2/1 BTheory.► tr) sk = tK3 tr (tl-sk s→a2/1 (tl-sk s→a1 sk))
      tK0 (s→a1 BTheory.► a1→b1/1 BTheory.► tr) sk = tK2 tr (tl-sk a1→b1/1 (tl-sk s→a1 sk))

      tK2 : ∀ {G' : IndepProto-State} (tr : s2 ~~> G')
        (sk : True (skippable? C1 tr)) → [] & s0 ∷ [] / G' ↑ C1 ⊢p< mg > (Σ B1 ？[ s/itm ]· (v f0 ∷ []))
      tK2 BTheory.■ sk = t/recv R[ b→c1/2 ] (λ{ b→c1/2 → t/var ~refl ((s→a1 _~~>_.► _~~>_.■) , (λ{ ≢S; ≢R }) , tt) })

      tK3 : ∀ {G' : IndepProto-State} (tr : s3 ~~> G')
        (sk : True (skippable? C1 tr)) → [] & s0 ∷ [] / G' ↑ C1 ⊢p< mg > (Σ B1 ？[ s/itm ]· (v f0 ∷ []))
      tK3 (a1→b1/3 BTheory.► tr) sk = tK4 tr (tl-sk a1→b1/3 sk)
      tK3 (a2→b2/3 BTheory.► tr) sk = tK5 tr (tl-sk a2→b2/3 sk)

      tK5 : ∀ {G' : IndepProto-State} (tr : s5 ~~> G')
        (sk : True (skippable? C1 tr)) → [] & s0 ∷ [] / G' ↑ C1 ⊢p< mg > (Σ B1 ？[ s/itm ]· (v f0 ∷ []))
      tK5 (b2→c2/5 BTheory.► tr) sk = tK3 tr (tl-sk b2→c2/5 sk)
      tK5 (a1→b1/5 BTheory.► tr) sk = tK6  tr (tl-sk a1→b1/5 sk)

      tK6 : ∀ {G' : IndepProto-State} (tr : s6 ~~> G')
        (sk : True (skippable? C1 tr)) → [] & s0 ∷ [] / G' ↑ C1 ⊢p< mg > (Σ B1 ？[ s/itm ]· (v f0 ∷ []))
      tK6 BTheory.■ sk = t/recv R[ b1→c1/6 ] (λ{ b1→c1/6 → t/var ~refl ((s→a1 _~~>_.► s→a2/1 _~~>_.► a2→b2/3 _~~>_.► _~~>_.■) , (λ{ ≢S; ≢R }) , ((λ{ ≢S; ≢R }) , ((λ{ ≢S; ≢R }) , tt)))})

      tK4 : ∀ {G' : IndepProto-State} (tr : s4 ~~> G')
        (sk : True (skippable? C1 tr)) → [] & s0 ∷ [] / G' ↑ C1 ⊢p< mg > (Σ B1 ？[ s/itm ]· (v f0 ∷ []))
      tK4 BTheory.■ sk = t/recv R[ b1→c1/4 ] (λ{ b1→c1/4 → t/var ~refl ((s→a1 _~~>_.► s→a2/1 _~~>_.► _~~>_.■) , (λ{ ≢S; ≢R }) , ((λ{ ≢S; ≢R }) , tt))})

-- TYD of A2

  module TYD-A2 where
   mutual
     CC0 : Causal? s0 A2 f0
     CC0 BTheory.■ U P∉G′ BTheory.■ () x₁
     CC0 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
     CC0 (s→a1 BTheory.► a1→b1/1 BTheory.► tr) U P∉G′ tr' x x₁
       = CC2 tr (tl-until a1→b1/1 (tl-until s→a1 U)) P∉G′ tr' x x₁

     CC2 : Causal? s2 A2 f0
     CC2 (b→c1/2 BTheory.► a1→b1/1 BTheory.► tr) U P∉G′ tr' x x₁
       = CC2 tr (tl-until a1→b1/1 (tl-until b→c1/2 U)) P∉G′ tr' x x₁

   mutual
     AA0 : Active? s0 A2
     AA0 BTheory.■ x = Active (s→a1 _~~>_.► _~~>_.■)
     AA0 (s→a1 BTheory.► BTheory.■) x = Active _~~>_.■
     AA0 (s→a1 BTheory.► a1→b1/1 ► tr) x
       = AA2 tr (tl-until a1→b1/1 (tl-until s→a1 x))

     AA2 : Active? s2 A2
     AA2 BTheory.■ x = Active _~~>_.■
     AA2 (b→c1/2 BTheory.► BTheory.■) x = Active _~~>_.■
     AA2 (b→c1/2 BTheory.► a1→b1/1 BTheory.► tr) x
       = AA2 tr (tl-until a1→b1/1 (tl-until b→c1/2 x))

   mutual
     CD5 : Causal? s5 f4 B2
     CD5 BTheory.■ U P∉G′ BTheory.■ () x₁
     CD5 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
     CD5 (b2→c2/5 BTheory.► tr) U P∉G′ tr' x x₁
       = CD3 tr (tl-until b2→c2/5 U) P∉G′ tr' x x₁
     CD5 (a1→b1/5 BTheory.► BTheory.■) U P∉G′ BTheory.■ () x₁
     CD5 (a1→b1/5 BTheory.► BTheory.■) U P∉G′ (x₂ BTheory.► tr') x ()
     CD5 (a1→b1/5 BTheory.► b1→c1/6 BTheory.► tr) U P∉G′ tr' x x₁
       = CD5 tr (tl-until b1→c1/6 (tl-until a1→b1/5 U)) P∉G′ tr' x x₁
     CD5 (a1→b1/5 BTheory.► b2→c2/6 BTheory.► b1→c1/4 BTheory.► tr) U P∉G′ tr' x x₁
       = CD3 tr (tl-until b1→c1/4 (tl-until b2→c2/6 (tl-until a1→b1/5 U))) P∉G′ tr' x x₁

     CD3 : Causal? s3 f4 B2
     CD3 (a1→b1/3 BTheory.► b1→c1/4 BTheory.► tr) U P∉G′ tr' x x₁
       = CD3 tr (tl-until b1→c1/4 (tl-until a1→b1/3 U)) P∉G′ tr' x x₁

   mutual
     AD5 : Active? s5 A2
     AD5 BTheory.■ x = Active (b2→c2/5 _~~>_.► _~~>_.■)
     AD5 (b2→c2/5 BTheory.► tr) x = AD3 tr (tl-until b2→c2/5 x)
     AD5 (a1→b1/5 BTheory.► BTheory.■) x
       = Active (b1→c1/6 _~~>_.► b2→c2/5 _~~>_.► _~~>_.■)
     AD5 (a1→b1/5 BTheory.► b1→c1/6 BTheory.► tr) x
       = AD5 tr (tl-until b1→c1/6 (tl-until a1→b1/5 x))
     AD5 (a1→b1/5 BTheory.► b2→c2/6 BTheory.► BTheory.■) x = Active _~~>_.■
     AD5 (a1→b1/5 BTheory.► b2→c2/6 BTheory.► b1→c1/4 BTheory.► tr) x
       = AD3 tr (tl-until b1→c1/4 (tl-until b2→c2/6 (tl-until a1→b1/5 x)))
     AD3 : Active? s3 A2
     AD3 BTheory.■ x = Active _~~>_.■
     AD3 (a1→b1/3 BTheory.► BTheory.■) x = Active _~~>_.■
     AD3 (a1→b1/3 BTheory.► b1→c1/4 BTheory.► tr) x
       = AD3 tr (tl-until b1→c1/4 (tl-until a1→b1/3 x))

   mutual
     tK0 : ∀ {B} → (tr : s0 ~~> B) → True (skippable? A2 tr) → [] & [] / B ↑ A2 ⊢p< ng > p/A B2
     tK0 (s→a1 BTheory.► BTheory.■) x = t/recv R[ s→a2/1 ] (λ{ s→a2/1 →
       t/send a2→b2/3 (te/val tv/unit) (
       t/rec rt/refl (dt/skip B2 CD5 AD5
         λ{ (b2→c2/5 BTheory.► BTheory.■) → t/send a2→b2/3 (te/val tv/unit) (t/var ~refl (_~~>_.■ , tt))
          ; (a1→b1/5 BTheory.► tr) {sk = sk} → tK6 tr (tl-sk a1→b1/5 sk)
          })
       )})

     tK6 : ∀ {B} → (tr : s6 ~~> B) → True (skippable? A2 tr) → (s/unit ∷ []) & s5 ∷ [] / B ↑ A2 ⊢p< mg > (B2 ! 0 , item < val v/unit >∙ v f0)
     tK6 (b1→c1/6 BTheory.► b2→c2/5 BTheory.► BTheory.■) x = t/send a2→b2/3 (te/val tv/unit) (t/var ~refl (_~~>_.■ , tt))
     tK6 (b2→c2/6 BTheory.► BTheory.■) x = t/send a2→b2/4 (te/val tv/unit) (t/var ~refl ((a1→b1/5 _~~>_.► _~~>_.■) , (λ{ ≢S; ≢R }) , tt))
     tK6 (b1→c1/6 BTheory.► a1→b1/5 BTheory.► tr) x = tK6 tr (tl-sk a1→b1/5 (tl-sk b1→c1/6 x))

   t/A2 : [] & [] / s0 ↑ A2 ⊢p< ng > (p/A B2)
   t/A2 = dt/skip f0 CC0 AA0 λ tr {sk = sk} → tK0 tr sk

-- TYD of A2

  module TYD-B2 where

    mutual
      CC0 : Causal? s0 B2 A2
      CC0 BTheory.■ U P∉G′ (s→a1 BTheory.► BTheory.■) () x₁
      CC0 BTheory.■ U P∉G′ (s→a1 BTheory.► x₂ BTheory.► tr') x ()
      CC0 (s→a1 BTheory.► BTheory.■) U P∉G′ BTheory.■ () x₁
      CC0 (s→a1 BTheory.► BTheory.■) U P∉G′ (x₂ BTheory.► tr') x ()
      CC0 (s→a1 BTheory.► s→a2/1 BTheory.► tr) U P∉G′ tr' x x₁
        = CC3 tr (tl-until s→a2/1 (tl-until s→a1 U)) P∉G′ tr' x x₁
      CC0 (s→a1 BTheory.► a1→b1/1 BTheory.► tr) U P∉G′ tr' x x₁
        = CC2 tr (tl-until a1→b1/1 (tl-until s→a1 U)) P∉G′ tr' x x₁

      CC3 : Causal? s3 B2 A2
      CC3 (a1→b1/3 BTheory.► b1→c1/4 BTheory.► tr) U P∉G′ tr' x x₁
        = CC3 tr (tl-until b1→c1/4 (tl-until a1→b1/3 U)) P∉G′ tr' x x₁

      CC2 : Causal? s2 B2 A2
      CC2 BTheory.■ U P∉G′ BTheory.■ () x₁
      CC2 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
      CC2 (s→a2/2 BTheory.► tr) U P∉G′ tr' x x₁
        = CC4 tr (tl-until s→a2/2 U) P∉G′ tr' x x₁
      CC2 (b→c1/2 BTheory.► tr) U P∉G′ tr' x x₁
        = CC1 tr (tl-until b→c1/2 U) P∉G′ tr' x x₁

      CC4 : Causal? s4 B2 A2
      CC4 (b1→c1/4 BTheory.► tr) U P∉G′ tr' x x₁
        = CC3 tr (tl-until b1→c1/4 U) P∉G′ tr' x x₁

      CC1 : Causal? s1 B2 A2
      CC1 BTheory.■ U P∉G′ BTheory.■ () x₁
      CC1 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
      CC1 (s→a2/1 BTheory.► tr) U P∉G′ tr' x x₁
        = CC3 tr (tl-until s→a2/1 U) P∉G′ tr' x x₁
      CC1 (a1→b1/1 BTheory.► tr) U P∉G′ tr' x x₁
        = CC2 tr (tl-until a1→b1/1 U) P∉G′ tr' x x₁

    mutual
      AA0 : Active? s0 B2
      AA0 BTheory.■ x = Active (s→a1 _~~>_.► s→a2/1 _~~>_.► _~~>_.■)
      AA0 (s→a1 BTheory.► BTheory.■) x = Active (s→a2/1 _~~>_.► _~~>_.■)
      AA0 (s→a1 BTheory.► s→a2/1 BTheory.► tr) x = AA3 tr (tl-until s→a2/1 (tl-until s→a1 x))
      AA0 (s→a1 BTheory.► a1→b1/1 BTheory.► tr) x = AA2 tr (tl-until a1→b1/1 (tl-until s→a1 x))

      AA3 : Active? s3 B2
      AA3 BTheory.■ x = Active _~~>_.■
      AA3 (a1→b1/3 BTheory.► BTheory.■) x = Active _~~>_.■
      AA3 (a1→b1/3 BTheory.► b1→c1/4 BTheory.► tr) x = AA3 tr (tl-until b1→c1/4 (tl-until a1→b1/3 x))

      AA2 : Active? s2 B2
      AA2 BTheory.■ x = Active (b→c1/2 _~~>_.► s→a2/1 _~~>_.► _~~>_.■)
      AA2 (s→a2/2 BTheory.► BTheory.■) x = Active _~~>_.■
      AA2 (s→a2/2 BTheory.► b1→c1/4 BTheory.► tr) x = AA3 tr (tl-until b1→c1/4 (tl-until s→a2/2 x))
      AA2 (b→c1/2 BTheory.► BTheory.■) x = Active (s→a2/1 _~~>_.► _~~>_.■)
      AA2 (b→c1/2 BTheory.► s→a2/1 BTheory.► tr) x = AA3 tr (tl-until s→a2/1 (tl-until b→c1/2 x))
      AA2 (b→c1/2 BTheory.► a1→b1/1 BTheory.► tr) x = AA2 tr (tl-until a1→b1/1 (tl-until b→c1/2 x))

    mutual
      t/B2 : [] & [] / s0 ↑ B2 ⊢p< ng > (p/B A2 C2)
      t/B2 = t/rec rt/refl (dt/skip A2 CC0 AA0
        λ{ (s→a1 BTheory.► s→a2/1 BTheory.► tr) {sk = sk}
           → tK3 tr (tl-sk s→a2/1 (tl-sk s→a1 sk))
         ; (s→a1 BTheory.► a1→b1/1 BTheory.► tr) {sk = sk}
           → tK2 tr (tl-sk a1→b1/1 (tl-sk s→a1 sk))
        })

      tK2 : ∀{G'} → (tr : s2 ~~> G') → True (skippable? B2 tr)
        → [] & s0 ∷ [] / G' ↑ B2 ⊢p< mg > (Σ A2 ？[ s/itm ]· (C2 ! 0 , item < val v/unit >∙ v f0 ∷ []))
      tK2 (s→a2/2 BTheory.► BTheory.■) x = t/recv R[ a2→b2/4 ] (λ{ a2→b2/4 →
        t/send b2→c2/6 (te/val tv/unit) (t/var ~refl ((s→a1 _~~>_.► s→a2/1 _~~>_.► a1→b1/3 _~~>_.► _~~>_.■) , (λ{ ≢S; ≢R }) , (λ{ ≢S; ≢R }) , ((λ{ ≢S; ≢R }) , tt)))})
      tK2 (b→c1/2 BTheory.► s→a2/1 BTheory.► tr) x
        = tK3 tr (tl-sk s→a2/1 (tl-sk b→c1/2 x))
      tK2 (b→c1/2 BTheory.► a1→b1/1 BTheory.► tr) x
        = tK2 tr (tl-sk a1→b1/1 (tl-sk b→c1/2 x))

      tK3 : ∀{G'} → (tr : s3 ~~> G') → True (skippable? B2 tr)
        → [] & s0 ∷ [] / G' ↑ B2 ⊢p< mg > (Σ A2 ？[ s/itm ]· (C2 ! 0 , item < val v/unit >∙ v f0 ∷ []))
      tK3 BTheory.■ x = t/recv R[ a2→b2/3 ] λ{ a2→b2/3 → t/send b2→c2/5 (te/val tv/unit) (t/var ~refl ((s→a1 _~~>_.► s→a2/1 _~~>_.► _~~>_.■) , (λ{ ≢S; ≢R }) , ((λ{ ≢S; ≢R }) , tt))) }

-- TYD of C2

  module TYD-C2 where
    mutual
      CC0 : Causal? s0 C2 B2
      CC0 BTheory.■ U P∉G′ (s→a1 BTheory.► s→a2/1 BTheory.► BTheory.■) () x₁
      CC0 BTheory.■ U P∉G′ (s→a1 BTheory.► s→a2/1 BTheory.► x₂ BTheory.► tr') x ()
      CC0 BTheory.■ U P∉G′ (s→a1 BTheory.► a1→b1/1 BTheory.► s→a2/2 BTheory.► BTheory.■) () x₁
      CC0 BTheory.■ U P∉G′ (s→a1 BTheory.► a1→b1/1 BTheory.► s→a2/2 BTheory.► x₂ BTheory.► tr') x ()
      CC0 BTheory.■ U P∉G′ (s→a1 BTheory.► a1→b1/1 BTheory.► b→c1/2 BTheory.► tr) x y
        = NC1 tr (tl-sk b→c1/2 (tl-sk a1→b1/1 (tl-sk s→a1 x)))
                 (tl-sk b→c1/2 (tl-sk a1→b1/1 (tl-sk s→a1 y)))
      CC0 (s→a1 BTheory.► BTheory.■) U P∉G′ tr' x x₁ = NC1 tr' x x₁
      CC0 (s→a1 BTheory.► s→a2/1 BTheory.► tr) U P∉G′ tr' x x₁
        = CC3 tr (tl-until s→a2/1 (tl-until s→a1 U)) P∉G′ tr' x x₁
      CC0 (s→a1 BTheory.► a1→b1/1 BTheory.► tr) U P∉G′ tr' x x₁
        = CC2 tr (tl-until a1→b1/1 (tl-until s→a1 U)) P∉G′ tr' x x₁

      CC2 : Causal? s2 C2 B2
      CC2 BTheory.■ U P∉G′ tr' x x₁ = NC2 tr' x x₁
      CC2 (s→a2/2 BTheory.► BTheory.■) U P∉G′ BTheory.■ () x₁
      CC2 (s→a2/2 BTheory.► BTheory.■) U P∉G′ (x₂ BTheory.► tr') x ()
      CC2 (s→a2/2 BTheory.► b1→c1/4 BTheory.► BTheory.■) U P∉G′ BTheory.■ () x₁
      CC2 (s→a2/2 BTheory.► b1→c1/4 BTheory.► BTheory.■) U P∉G′ (x₂ BTheory.► tr') x ()
      CC2 (s→a2/2 BTheory.► b1→c1/4 BTheory.► tr) U P∉G′ tr' x y
        = CC3 tr (tl-until b1→c1/4 (tl-until s→a2/2 U)) P∉G′ tr' x y
      CC2 (s→a2/2 BTheory.► a2→b2/4 BTheory.► tr) U P∉G′ tr' x y
        = CC6 tr (tl-until a2→b2/4 (tl-until s→a2/2 U)) P∉G′ tr' x y -- state 6
      CC2 (b→c1/2 BTheory.► BTheory.■) U P∉G′ tr' x x₁ = NC1 tr' x x₁
      CC2 (b→c1/2 BTheory.► s→a2/1 BTheory.► tr) U P∉G′ tr' x x₁
        = CC3 tr (tl-until s→a2/1 (tl-until b→c1/2 U)) P∉G′ tr' x x₁
      CC2 (b→c1/2 BTheory.► a1→b1/1 BTheory.► tr) U P∉G′ tr' x x₁
        = CC2 tr (tl-until a1→b1/1 (tl-until b→c1/2 U)) P∉G′ tr' x x₁

      CC3 : Causal? s3 C2 B2
      CC3 BTheory.■ U P∉G′ BTheory.■ () x₁
      CC3 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
      CC3 (a1→b1/3 BTheory.► BTheory.■) U P∉G′ BTheory.■ () x₁
      CC3 (a1→b1/3 BTheory.► BTheory.■) U P∉G′ (x₂ BTheory.► tr') x ()
      CC3 (a1→b1/3 BTheory.► b1→c1/4 BTheory.► tr) U P∉G′ tr' x x₁
        = CC3 tr (tl-until b1→c1/4 (tl-until a1→b1/3 U)) P∉G′ tr' x x₁ -- State 3
      CC3 (a1→b1/3 BTheory.► a2→b2/4 BTheory.► tr) U P∉G′ tr' x x₁
        = CC6 tr (tl-until a2→b2/4 (tl-until a1→b1/3 U)) P∉G′ tr' x x₁ -- State 6
      CC3 (a2→b2/3 BTheory.► a1→b1/5 BTheory.► tr) U P∉G′ tr' x x₁
        = CC6 tr (tl-until a1→b1/5 (tl-until a2→b2/3 U)) P∉G′ tr' x x₁ -- State 6

      CC6 : Causal? s6 C2 B2
      CC6 (b1→c1/6 BTheory.► a1→b1/5 BTheory.► tr) U P∉G′ tr' x x₁
        = CC6 tr (tl-until a1→b1/5 (tl-until b1→c1/6 U)) P∉G′ tr' x x₁

      NC1 : ∀{G″} → (tr' : s1 ~~> G″) → True (skippable? C2 tr') → True (skippable? B2 tr') → ⊥
      NC1 (s→a2/1 BTheory.► BTheory.■) () x₁
      NC1 (s→a2/1 BTheory.► x₂ BTheory.► tr') x ()
      NC1 (a1→b1/1 BTheory.► s→a2/2 BTheory.► BTheory.■) () x₁
      NC1 (a1→b1/1 BTheory.► s→a2/2 BTheory.► x₂ BTheory.► tr') x ()
      NC1 (a1→b1/1 BTheory.► b→c1/2 BTheory.► tr') x x₁
        = NC1 tr' ((tl-sk b→c1/2 (tl-sk a1→b1/1 x)))
                  ((tl-sk b→c1/2 (tl-sk a1→b1/1 x₁)))

      NC2 : ∀{G″} → (tr' : s2 ~~> G″) → True (skippable? C2 tr') → True (skippable? B2 tr') → ⊥
      NC2 (s→a2/2 BTheory.► BTheory.■) () y
      NC2 (s→a2/2 BTheory.► x₁ BTheory.► tr') x ()
      NC2 (b→c1/2 BTheory.► s→a2/1 BTheory.► BTheory.■) () y
      NC2 (b→c1/2 BTheory.► s→a2/1 BTheory.► x₁ BTheory.► tr') x ()
      NC2 (b→c1/2 BTheory.► a1→b1/1 BTheory.► s→a2/2 BTheory.► BTheory.■) () y
      NC2 (b→c1/2 BTheory.► a1→b1/1 BTheory.► s→a2/2 BTheory.► x₁ BTheory.► tr') x ()
      NC2 (b→c1/2 BTheory.► a1→b1/1 BTheory.► b→c1/2 BTheory.► tr') x y
        = NC1 tr' (tl-sk b→c1/2 (tl-sk a1→b1/1 (tl-sk b→c1/2 x)))
                  (tl-sk b→c1/2 (tl-sk a1→b1/1 (tl-sk b→c1/2 y)))

    mutual
      AA0 : Active? s0 C2
      AA0 BTheory.■ x = Active (s→a1 ► s→a2/1 ► a2→b2/3 ► _~~>_.■)
      AA0 (s→a1 BTheory.► tr) x = AA1 tr (tl-until s→a1 x)

      AA3 : Active? s3 C2
      AA3 BTheory.■ x = Active (a2→b2/3 ► _~~>_.■)
      AA3 (a1→b1/3 BTheory.► tr) x = AA4 tr (tl-until a1→b1/3 x)
      AA3 (a2→b2/3 BTheory.► BTheory.■) x = Active ■
      AA3 (a2→b2/3 BTheory.► a1→b1/5 BTheory.► tr) x
        = AA6 tr (tl-until a1→b1/5 (tl-until a2→b2/3 x))

      AA4 : Active? s4 C2
      AA4 BTheory.■ x = Active (a2→b2/4 ► ■)
      AA4 (b1→c1/4 BTheory.► tr) x = AA3 tr (tl-until b1→c1/4 x)
      AA4 (a2→b2/4 BTheory.► tr) x = AA6 tr (tl-until a2→b2/4 x)

      AA6 : Active? s6 C2
      AA6 BTheory.■ x = Active ■
      AA6 (b1→c1/6 BTheory.► BTheory.■) x = Active ■
      AA6 (b1→c1/6 BTheory.► a1→b1/5 BTheory.► tr) x = AA6 tr (tl-until a1→b1/5 (tl-until b1→c1/6 x))

      AA1 : Active? s1 C2
      AA1 (BTheory.■) x = Active (s→a2/1 ► a2→b2/3 ► _~~>_.■)
      AA1 (s→a2/1 BTheory.► tr) x = AA3 tr (tl-until s→a2/1 x)
      AA1 (a1→b1/1 BTheory.► BTheory.■) x = Active (s→a2/2 ► a2→b2/4 ► ■)
      AA1 (a1→b1/1 BTheory.► s→a2/2 BTheory.► tr) x
        = AA4 tr (tl-until s→a2/2 (tl-until a1→b1/1 x))
      AA1 (a1→b1/1 BTheory.► b→c1/2 BTheory.► tr) x
        = AA1 tr (tl-until b→c1/2 (tl-until a1→b1/1 x))
    mutual
      t/C2 : [] & [] / s0 ↑ C2 ⊢p< ng > (p/C B2)
      t/C2 = t/rec rt/refl (dt/skip B2 CC0 AA0
        λ{ (s→a1 BTheory.► tr) {sk = sk} → t/K1 tr (tl-sk s→a1 sk)
         })

      t/K1 : ∀{G'}
        → (tr : s1 ~~> G')
        → True (skippable? C2 tr)
        → [] & s0 ∷ [] / G' ↑ C2 ⊢p< mg > (Σ B2 ？[ s/itm ]· (v f0 ∷ []))
      t/K1 (s→a2/1 BTheory.► tr) x = t/K3 tr (tl-sk s→a2/1 x)
      t/K1 (a1→b1/1 BTheory.► s→a2/2 BTheory.► tr) x
        = t/K4 tr (tl-sk s→a2/2 (tl-sk a1→b1/1 x))
      t/K1 (a1→b1/1 BTheory.► b→c1/2 BTheory.► tr) x
        = t/K1 tr (tl-sk b→c1/2 (tl-sk a1→b1/1 x))

      t/K3 : ∀{G'}
        → (tr : s3 ~~> G')
        → True (skippable? C2 tr)
        → [] & s0 ∷ [] / G' ↑ C2 ⊢p< mg > (Σ B2 ？[ s/itm ]· (v f0 ∷ []))
      t/K3 (a1→b1/3 BTheory.► tr) x = t/K4 tr (tl-sk a1→b1/3 x)
      t/K3 (a2→b2/3 BTheory.► tr) x = t/K5 tr (tl-sk a2→b2/3 x)

      t/K4 : ∀{G'}
        → (tr : s4 ~~> G')
        → True (skippable? C2 tr)
        → [] & s0 ∷ [] / G' ↑ C2 ⊢p< mg > (Σ B2 ？[ s/itm ]· (v f0 ∷ []))
      t/K4 (b1→c1/4 BTheory.► tr) x = t/K3 tr (tl-sk b1→c1/4 x)
      t/K4 (a2→b2/4 BTheory.► tr) x = t/K6 tr (tl-sk a2→b2/4 x)

      t/K5 : ∀{G'}
        → (tr : s5 ~~> G')
        → True (skippable? C2 tr)
        → [] & s0 ∷ [] / G' ↑ C2 ⊢p< mg > (Σ B2 ？[ s/itm ]· (v f0 ∷ []))
      t/K5 BTheory.■ x = t/recv R[ b2→c2/5 ] (λ{ b2→c2/5 →
        t/var ~refl ((s→a1 _~~>_.► s→a2/1 _~~>_.► _~~>_.■) , (λ{ ≢S; ≢R }) , ((λ{ ≢S; ≢R }) , tt)) })

      t/K6 : ∀{G'}
        → (tr : s6 ~~> G')
        → True (skippable? C2 tr)
        → [] & s0 ∷ [] / G' ↑ C2 ⊢p< mg > (Σ B2 ？[ s/itm ]· (v f0 ∷ []))
      t/K6 BTheory.■ x = t/recv R[ b2→c2/6 ] (λ{ b2→c2/6 →
        t/var ~refl ((s→a1 _~~>_.► s→a2/1 _~~>_.► a1→b1/3 _~~>_.► _~~>_.■) , (λ{ ≢S; ≢R }) , ((λ{ ≢S; ≢R }) , ((λ{ ≢S; ≢R }) , tt))) })
