{-# OPTIONS --guardedness #-}
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤ ; tt)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Vec hiding (_++_)
open import Data.Product
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (Dec; True ; False ; toWitnessFalse ; fromWitnessFalse; fromWitness;
        toWitness; yes; no)
open import Relation.Binary.PropositionalEquality hiding ( [_] )

open import Utils
open import Definitions

module Examples.OAuth2 where

  module Behaviours where
    open import Definitions.Expr
    open import Definitions.Common(3)
    open import Definitions.Actions(3)

    -- Protocol states
    OAuth2-States = Fin 5

    initial-state : OAuth2-States
    initial-state = zero

    pattern sx = suc _
    pattern ssx = suc (suc _)
    pattern sssx = suc (suc (suc _))

    pattern f0 = zero
    pattern f1 = suc zero
    pattern f2 = suc (suc zero)
    pattern f3 = suc (suc (suc zero))
    pattern f4 = suc (suc (suc (suc zero)))

    s0 : OAuth2-States
    s0 = f0
    s1 : OAuth2-States
    s1 = f1
    s2 : OAuth2-States
    s2 = f2
    s3 : OAuth2-States
    s3 = f3
    s4 : OAuth2-States
    s4 = f4

    S : Part
    S = zero

    C : Part
    C = suc zero

    A : Part
    A = suc (suc zero)

    login : Fin 2
    login = zero

    passwd : Fin 2
    passwd = zero

    quit : Fin 2
    quit = suc zero

    cancel : Fin 2
    cancel = suc zero

    open HeadAct

    data LTS : OAuth2-States → Part → Part → {I : ℕ} → Vec Sort (suc I)
         → Fin (suc I) → OAuth2-States → Set where
      s→c/login : LTS s0 S C (s/nat ∷ s/nat ∷ []) login s1
      c→a/pwd : LTS s1 C A (s/nat ∷ s/bool ∷ []) passwd s2
      a→s/auth : LTS s2 A S (s/bool ∷ []) zero s3

      s→c/cancel : LTS s0 S C (s/nat ∷ s/nat ∷ []) cancel s4
      c→a/quit : LTS s4 C A (s/nat ∷ s/bool ∷ []) quit s3

    TheLTS : OAuth2-States → Action → OAuth2-States → Set
    TheLTS si (P ⟶ Q # S , i) so = LTS si P Q S i so

    OAuth2Theory : BTheory 3
    OAuth2Theory .BTheory.Behav = OAuth2-States
    OAuth2Theory .BTheory._-<_>->_ = TheLTS

    open BTheory OAuth2Theory

    pattern ≢S = (∈S ())
    pattern ≢R = (∈R ())

    can-step? : ∀ P G → Dec (P ∈tr G)
    can-step? f0 f0 = yes (∈-tr s→c/login (∈S refl))
    can-step? f0 f1 = no λ{ (BTheory.∈-tr c→a/pwd (∈S ())) ; (BTheory.∈-tr c→a/pwd (∈R ())) }
    can-step? f0 f2 = yes (∈-tr a→s/auth (∈R refl))
    can-step? f0 f3 = no (λ{ ()})
    can-step? f0 f4 = no λ{ (BTheory.∈-tr c→a/quit (∈S ())) ; (BTheory.∈-tr c→a/quit (∈R ())) }
    can-step? f1 f0 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr s→c/login (∈R refl))
    can-step? f1 f1 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr c→a/pwd (∈S refl))
    can-step? f1 f2 = no (λ{ (BTheory.∈-tr a→s/auth ≢S) ; (BTheory.∈-tr a→s/auth ≢R) })
    can-step? f1 f3 = no (λ ())
    can-step? f1 f4 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr c→a/quit (∈S refl))
    can-step? f2 f0 = no λ{ (BTheory.∈-tr s→c/cancel (∈S ())) ; (BTheory.∈-tr s→c/cancel (∈R ())); (BTheory.∈-tr s→c/login (∈S ())) ; (BTheory.∈-tr s→c/login (∈R ())) }
    can-step? f2 f1 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr c→a/pwd (∈R refl))
    can-step? f2 f2 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr a→s/auth (∈S refl))
    can-step? f2 f3 = no (λ ())
    can-step? f2 f4 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr c→a/quit (∈R refl))

    o-indep? : ∀ {G α α' G' G''} →
      G -< α >-> G' → G -< α' >-> G'' → (proj₁ α) ⋔ (proj₁ α') ⊎ proj₁ α ≡ proj₁ α'
    o-indep? s→c/login s→c/login = inj₂ refl
    o-indep? s→c/login s→c/cancel = inj₂ refl
    o-indep? c→a/pwd c→a/pwd = inj₂ refl
    o-indep? a→s/auth a→s/auth = inj₂ refl
    o-indep? s→c/cancel s→c/login = inj₂ refl
    o-indep? s→c/cancel s→c/cancel = inj₂ refl
    o-indep? c→a/quit c→a/quit = inj₂ refl

    o-snd≢rcv : ∀ {G G' α} → G -< α >-> G' → sender α ≢ receiver α
    o-snd≢rcv () refl

    o-step-det : ∀ {G α G' G''} → TheLTS G α G' → TheLTS G α G'' → G' ≡ G''
    o-step-det s→c/login s→c/login = refl
    o-step-det c→a/pwd c→a/pwd = refl
    o-step-det a→s/auth a→s/auth = refl
    o-step-det s→c/cancel s→c/cancel = refl
    o-step-det c→a/quit c→a/quit = refl

    open _~_
    ~≡ : ∀ G G' → G ~ G' → G ≡ G'
    ~≡ f0 f0 b = refl
    ~≡ f0 sx b with ~L b s→c/login
    ... | _ , () , next-R

    ~≡ f1 f0 b with ~L b c→a/pwd
    ... | _ , () , next-R
    ~≡ f1 f1 b = refl
    ~≡ f1 ssx b with ~L b c→a/pwd
    ... | _ , () , next-R

    ~≡ f2 f0 b with ~L b a→s/auth
    ... | _ , () , next-R
    ~≡ f2 f1 b with ~L b a→s/auth
    ... | _ , () , next-R
    ~≡ f2 f2 b = refl
    ~≡ f2 sssx b with ~L b a→s/auth
    ... | _ , () , next-R

    ~≡ f3 f0 b with ~R b s→c/login
    ... | _ , () , next-R
    ~≡ f3 f1 b with ~R b c→a/pwd
    ... | _ , () , next-R
    ~≡ f3 f2 b with ~R b a→s/auth
    ... | _ , () , next-R
    ~≡ f3 f3 b = refl
    ~≡ f3 f4 b with ~R b c→a/quit
    ... | _ , () , _

    ~≡ f4 f0  b with ~R b s→c/login
    ... | _ , () , next-R
    ~≡ f4 f1  b with ~R b c→a/pwd
    ... | _ , () , next-R
    ~≡ f4 f2  b with ~R b a→s/auth
    ... | _ ,  () , next-R
    ~≡ f4 f3  b with ~L b c→a/quit
    ... | _ , () , _
    ~≡ f4 f4 b = refl

    o-~stepback : ∀ {α} {G0} {G1} {G1'} →
                G1 ~ G1' →
                G0 -< α >-> G1 → ∃-syntax (λ G0' → (G0 ~ G0') × (G0' -< α >-> G1'))
    o-~stepback {G0 = G0} b st with ~≡ _ _ b
    ... | refl = G0 , ~refl , st

    o-diamond : ∀ {G} {α} {G₁} {α'} {G₂} →
              G -< α >-> G₁ → G -< α' >-> G₂ →
              ((proj₁ α) ⋔ (proj₁  α')) →
              ∃-syntax (λ G' → (G₁ -< α' >-> G') × (G₂ -< α >-> G'))
    o-diamond s→c/login s→c/login   f = ⊥-elim (f (inj₂ (∈R refl)))
    o-diamond s→c/login s→c/cancel  f = ⊥-elim (f (inj₂ (∈R refl)))
    o-diamond c→a/pwd c→a/pwd       f = ⊥-elim (f (inj₂ (∈R refl)))
    o-diamond a→s/auth a→s/auth     f = ⊥-elim (f (inj₂ (∈R refl)))
    o-diamond s→c/cancel s→c/login  f = ⊥-elim (f (inj₂ (∈R refl)))
    o-diamond s→c/cancel s→c/cancel f = ⊥-elim (f (inj₂ (∈R refl)))
    o-diamond c→a/quit c→a/quit f = ⊥-elim (f (inj₂ (∈R refl)))

    diamond : ∀ {G} {α} {G₁} {α'} {G₂} →
              G -< α >-> G₁ → G -< α' >-> G₂ →
              α ∥ α' →
              ∃-syntax (λ G' → (G₁ -< α' >-> G') × (G₂ -< α >-> G'))
    diamond s→c/login  s→c/login  (ii-≡snd refl x₃) = ⊥-elim (x₃ refl)
    diamond s→c/login  s→c/cancel (ii-≡snd refl x₃) = ⊥-elim (x₃ refl)
    diamond c→a/pwd c→a/pwd       (ii-≡snd refl x₃) = ⊥-elim (x₃ refl)
    diamond a→s/auth a→s/auth     (ii-≡snd refl x₃) = ⊥-elim (x₃ refl)
    diamond s→c/cancel s→c/login  (ii-≡snd refl x₃) = ⊥-elim (x₃ refl)
    diamond s→c/cancel s→c/cancel (ii-≡snd refl x₃) = ⊥-elim (x₃ refl)
    diamond c→a/quit c→a/quit (ii-≡snd refl x₃) = ⊥-elim (x₃ refl)
    diamond x x₁ (ii-disj x₂) = o-diamond x x₁ x₂

    o-cond-comm : ∀ {hα} {i j : Fin (suc (nchoices hα))}
                      {α'} {G} {G'} {Gᵢ} {Gⱼ'} →
                    hα ∥ₕ (proj₁ α') →
                    G -< α' >-> G' →
                    G -< hα , i >-> Gᵢ →
                    G' -< hα , j >-> Gⱼ' → ∃-syntax (_-<_>->_ G (hα , j))
    o-cond-comm x () s→c/login s→c/login
    o-cond-comm x () s→c/login s→c/cancel
    o-cond-comm x () c→a/pwd c→a/pwd
    o-cond-comm x () c→a/pwd c→a/quit
    o-cond-comm x () a→s/auth a→s/auth
    o-cond-comm x () s→c/cancel s→c/login
    o-cond-comm x () s→c/cancel s→c/cancel
    o-cond-comm x () c→a/quit c→a/pwd
    o-cond-comm x () c→a/quit c→a/quit

    OAuth2-Properties : BT-Prop OAuth2Theory
    OAuth2-Properties .BT-Prop.recv-act-eq x x₁ x₂ with o-indep? x x₁
    ... | inj₁ ii = ⊥-elim (ii (inj₂ x₂))
    ... | inj₂ refl = refl
    OAuth2-Properties .BT-Prop.snd≢rcv = o-snd≢rcv
    OAuth2-Properties .BT-Prop.step-det = o-step-det
    OAuth2-Properties .BT-Prop.~stepback = o-~stepback
    OAuth2-Properties .BT-Prop.diamond = diamond
    OAuth2-Properties .BT-Prop.cond-comm = o-cond-comm

    OAuth2-Extra : BT-Extra OAuth2Theory
    OAuth2-Extra .BT-Extra.can-step? = can-step?

  open Behaviours
  open Definitions.MPST Behaviours.OAuth2-Properties
  open Definitions.MPST-Extra Behaviours.OAuth2-Properties Behaviours.OAuth2-Extra

  sorts/S : Vec Sort 2
  sorts/S = s/nat ∷ s/nat ∷ []

  p/S : Proc 0 0
  p/S = C ! _ , cancel < val (v/nat 0) >∙ ∅

  P∉s3 : ∀ {P} → P ∈T s3 → ⊥
  P∉s3 (BTheory.in/α () x₁)
  P∉s3 (BTheory.in/later () x₁)

  tt/end : ∀ {γ δ P}{Γ : Vec Sort γ}{Δ : Vec Behav δ}
    → Γ & Δ / s3 ↑ P ⊢p< ng > ∅
  tt/end = t/end P∉s3

  S∉s4 : S ∈T s4 → ⊥
  S∉s4 (in/α c→a/quit (∈S ()))
  S∉s4 (in/α c→a/quit (∈R ()))
  S∉s4 (in/later c→a/quit x) = P∉s3 x

  t/S : [] & [] / s0 ↑ S ⊢p< ng > p/S
  t/S = t/send s→c/cancel  (te/val tv/nat) (t/end S∉s4)

  p/C : Proc 0 0
  p/C = Σ S ？[ sorts/S ]·
          ( A ! _ , passwd < val (v/nat 0) >∙ ∅
          ∷ A ! _ , quit < val (v/bool true) >∙ ∅
          ∷ [])


  C∉s2 : C ∈T s2 → ⊥
  C∉s2 (BTheory.in/α a→s/auth (∈S ()))
  C∉s2 (BTheory.in/α a→s/auth (∈R ()))
  C∉s2 (BTheory.in/later a→s/auth x₁) = P∉s3 x₁

  t/C : [] & [] / s0 ↑ C ⊢p< ng > p/C
  t/C = t/recv R[ s→c/login ]
          (λ{ s→c/login → t/send c→a/pwd  (te/val tv/nat) (t/end C∉s2)
            ; s→c/cancel → t/send c→a/quit  (te/val tv/bool) (t/end P∉s3)
            })

  p/A : Proc 0 0
  p/A = Σ C ？[ s/nat ∷ s/bool ∷ [] ]·
          ( S ! zero , zero < val (v/bool true) >∙ ∅
          ∷ ∅
          ∷ [])

  c0AC : Causal? s0 A C
  c0AC BTheory.■ _ _ BTheory.■ () x₁
  c0AC BTheory.■ _ _ (s→c/login BTheory.► tr) x ()
  c0AC BTheory.■ _ _ (s→c/cancel BTheory.► tr) x ()
  c0AC (s→c/login BTheory.► c→a/pwd BTheory.► tr) () _ tr' x x₁
  c0AC (s→c/cancel BTheory.► c→a/quit BTheory.► tr) () _ tr' x x₁

  a0A : Active? s0 A
  a0A = λ{ BTheory.■ _ → Active (s→c/login ► ■)
        ; (s→c/login BTheory.► BTheory.■) _ → Active ■
        ; (s→c/cancel BTheory.► BTheory.■) _ → Active ■
        ; (s→c/login BTheory.► c→a/pwd BTheory.► _) ()
        ; (s→c/cancel BTheory.► c→a/quit BTheory.► tr) ()
        }

  t/A : [] & [] / s0 ↑ A ⊢p< ng > p/A
  t/A = dt/skip C c0AC a0A
        λ{ (s→c/login BTheory.► BTheory.■) → t/recv R[ c→a/pwd ] (λ{ c→a/pwd → t/send a→s/auth (te/val tv/bool) tt/end})
        ; (s→c/cancel BTheory.► BTheory.■) → t/recv R[ c→a/quit ] (λ{ c→a/quit → tt/end })
        }
