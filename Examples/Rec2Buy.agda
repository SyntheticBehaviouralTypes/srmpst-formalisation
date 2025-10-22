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

module Examples.Rec2Buy where

  module Behaviours where
    open import Definitions.Expr
    open import Definitions.Common(3)
    open import Definitions.Actions(3)

    mk-fin : ∀ m n → {t : T (m <ᵇ suc n)} → Fin (suc n)
    mk-fin m n {t = t} = fromℕ< (<ᵇ⇒< m (suc n) t)

    -- The participants
    A = mk-fin 0 2
    B = mk-fin 1 2
    S = mk-fin 2 2


    -- The Protocol states
    Rec2Buy-State = Fin 7

    s0  = mk-fin 0 6
    s1  = mk-fin 1 6
    s2  = mk-fin 2 6
    s3  = mk-fin 3 6
    s4  = mk-fin 4 6
    s5  = mk-fin 5 6
    s6  = mk-fin 6 6

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

    -- The labels and their sorts
    item = mk-fin 0 0
    price = mk-fin 0 0
    split-itm = mk-fin 0 1
    cancel = mk-fin 1 1
    yes-b = mk-fin 0 1
    no-b = mk-fin 1 1
    no-s = mk-fin 1 1
    buy = mk-fin 0 1
    s/a-s1 = s/nat ∷ []
    s/a-s2 = s/unit ∷ s/unit ∷ []
    s/a-b = s/nat ∷ s/unit ∷ []

    -- The LTS
    open HeadAct

    data LTS : Rec2Buy-State → Part → Part → {I : ℕ} → Vec Sort (suc I)
         → Fin (suc I) → Rec2Buy-State → Set where
      a→s/item   : LTS s0 A S s/a-s1 item      s1
      s→a/price  : LTS s1 S A s/a-s1 price     s2

      a→b/cancel : LTS s2 A B s/a-b  cancel    s3
      a→s/no     : LTS s3 A S s/a-s2 no-s      s6

      a→b/split  : LTS s2 A B s/a-b  split-itm s4

      b→a/no     : LTS s4 B A s/a-b  no-b      s2
      b→a/yes    : LTS s4 B A s/a-b  yes-b     s5
      a→s/buy    : LTS s5 A S s/a-s2 buy       s6

    TheLTS : Rec2Buy-State → Action → Rec2Buy-State → Set
    TheLTS si (P ⟶ Q # S , i) so = LTS si P Q S i so

    Rec2BuyTheory : BTheory 3
    Rec2BuyTheory .BTheory.Behav = Rec2Buy-State
    Rec2BuyTheory .BTheory._-<_>->_ = TheLTS

    open BTheory Rec2BuyTheory

    pattern ≢S = ∈S ()
    pattern ≢R = ∈R ()

    pattern S≢S = inj₁ (∈S ())
    pattern S≢R = inj₁ (∈R ())

    pattern R≢S = inj₂ (∈S ())
    pattern R≢R = inj₂ (∈R ())

    can-step? : ∀ P B → Dec (P ∈tr B)
    can-step? _  f6 = no (λ ())
    can-step? f0 f0 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a→s/item (∈S refl))
    can-step? f0 f1 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr s→a/price (∈R refl))
    can-step? f0 f2 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a→b/cancel (∈S refl))
    can-step? f0 f3 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a→s/no (∈S refl))
    can-step? f0 f4 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr b→a/no (∈R refl))
    can-step? f0 f5 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a→s/buy (∈S refl))
    can-step? f1 f0 = no (λ{ (BTheory.∈-tr a→s/item ≢S)
                           ; (BTheory.∈-tr a→s/item ≢R) })
    can-step? f1 f1 = no (λ{ (BTheory.∈-tr s→a/price ≢S)
                           ; (BTheory.∈-tr s→a/price ≢R) })
    can-step? f1 f2 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a→b/cancel (∈R refl))
    can-step? f1 f3 = no (λ{ (BTheory.∈-tr a→s/no ≢S)
                           ; (BTheory.∈-tr a→s/no ≢R) })
    can-step? f1 f4 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr b→a/no (∈S refl))
    can-step? f1 f5 = no (λ{ (BTheory.∈-tr a→s/buy ≢S)
                           ; (BTheory.∈-tr a→s/buy ≢R) })
    can-step? f2 f0 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a→s/item (∈R refl))
    can-step? f2 f1 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr s→a/price (∈S refl))
    can-step? f2 f2 = no (λ{ (BTheory.∈-tr a→b/cancel ≢S)
                           ; (BTheory.∈-tr a→b/cancel ≢R)
                           ; (BTheory.∈-tr a→b/split ≢S)
                           ; (BTheory.∈-tr a→b/split ≢R) })
    can-step? f2 f3 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a→s/no (∈R refl))
    can-step? f2 f4 = no (λ{ (BTheory.∈-tr b→a/no ≢S)
                           ; (BTheory.∈-tr b→a/no ≢R)
                           ; (BTheory.∈-tr b→a/yes ≢S)
                           ; (BTheory.∈-tr b→a/yes ≢R) })
    can-step? f2 f5 = true Relation.Nullary.because
      Relation.Nullary.ofʸ (∈-tr a→s/buy (∈R refl))

    -- The properties

    open _~_
    ~≡ : ∀ G G' → G ~ G' → G ≡ G'
    ~≡ f0 f0 _ = refl
    ~≡ f0 ss0 b with ~L b a→s/item
    ... | fst , () , snd

    ~≡ f1 f0 b  with ~R b a→s/item
    ... | fst , () , snd
    ~≡ f1 f1 _ = refl
    ~≡ f1 ss1 b  with ~L b s→a/price
    ... | fst , () , _

    ~≡ f2 f0 b  with ~R b a→s/item
    ... | fst , () , snd
    ~≡ f2 f1 b  with ~R b s→a/price
    ... | fst , () , snd
    ~≡ f2 f2 _ = refl
    ~≡ f2 ss2 b  with ~L b a→b/cancel
    ... | fst , () , _

    ~≡ f3 f0 b  with ~R b a→s/item
    ... | fst , () , snd
    ~≡ f3 f1 b  with ~R b s→a/price
    ... | fst , () , snd
    ~≡ f3 f2 b  with ~R b a→b/cancel
    ... | fst , () , snd
    ~≡ f3 f3 _ = refl
    ~≡ f3 ss3 b  with ~L b a→s/no
    ... | fst , () , _

    ~≡ f4 f0 b  with ~R b a→s/item
    ... | fst , () , snd
    ~≡ f4 f1 b  with ~R b s→a/price
    ... | fst , () , snd
    ~≡ f4 f2 b  with ~R b a→b/cancel
    ... | fst , () , snd
    ~≡ f4 f3 b  with ~R b a→s/no
    ... | fst , () , snd
    ~≡ f4 f4 _ = refl
    ~≡ f4 ss4 b  with ~L b b→a/no
    ... | fst , () , _

    ~≡ f5 f0 b  with ~R b a→s/item
    ... | fst , () , snd
    ~≡ f5 f1 b  with ~R b s→a/price
    ... | fst , () , snd
    ~≡ f5 f2 b  with ~R b a→b/cancel
    ... | fst , () , snd
    ~≡ f5 f3 b  with ~R b a→s/no
    ... | fst , () , snd
    ~≡ f5 f4 b  with ~R b b→a/no
    ... | fst , () , snd
    ~≡ f5 f5 _ = refl
    ~≡ f5 ss5 b  with ~L b a→s/buy
    ... | fst , () , _

    ~≡ f6 f0 b  with ~R b a→s/item
    ... | fst , () , snd
    ~≡ f6 f1 b  with ~R b s→a/price
    ... | fst , () , snd
    ~≡ f6 f2 b  with ~R b a→b/cancel
    ... | fst , () , snd
    ~≡ f6 f3 b  with ~R b a→s/no
    ... | fst , () , snd
    ~≡ f6 f4 b  with ~R b b→a/no
    ... | fst , () , snd
    ~≡ f6 f5 b  with ~R b a→s/buy
    ... | fst , () , snd
    ~≡ f6 f6 _ = refl

    indep? : ∀ {G} {α} {α'} {G'} {G''} →
         G -< α >-> G' → G -< α' >-> G'' → ((proj₁ α) ⋔ (proj₁ α')) ⊎ proj₁ α ≡ proj₁ α'
    indep? a→s/item a→s/item = inj₂ refl
    indep? s→a/price s→a/price = inj₂ refl
    indep? a→b/cancel a→b/cancel = inj₂ refl
    indep? a→b/cancel a→b/split = inj₂ refl
    indep? a→s/no a→s/no = inj₂ refl
    indep? a→b/split a→b/cancel = inj₂ refl
    indep? a→b/split a→b/split = inj₂ refl
    indep? b→a/no b→a/no = inj₂ refl
    indep? b→a/no b→a/yes = inj₂ refl
    indep? b→a/yes b→a/no = inj₂ refl
    indep? b→a/yes b→a/yes = inj₂ refl
    indep? a→s/buy a→s/buy = inj₂ refl

    snd≢rcv : ∀ {G} {G'} {α} → G -< α >-> G' → sender α ≢ receiver α
    snd≢rcv () refl

    step-det : ∀ {G} {α} {G'} {G''} →
           G -< α >-> G' → G -< α >-> G'' → G' ≡ G''
    step-det a→s/item a→s/item = refl
    step-det s→a/price s→a/price = refl
    step-det a→b/cancel a→b/cancel = refl
    step-det a→s/no a→s/no = refl
    step-det a→b/split a→b/split = refl
    step-det b→a/no b→a/no = refl
    step-det b→a/yes b→a/yes = refl
    step-det a→s/buy a→s/buy = refl

    ~stepback : ∀ {α} {G0} {G1} {G1'} →
            G1 ~ G1' →
            G0 -< α >-> G1 → ∃-syntax (λ G0' → (G0 ~ G0') × (G0' -< α >-> G1'))
    ~stepback x x₁ with ~≡ _ _ x
    ... | refl = _ , ~refl , x₁

    diamond : ∀ {G} {α} {G₁} {α'} {G₂} →
          G -< α >-> G₁ →
          G -< α' >-> G₂ →
          α ∥ α' → ∃-syntax (λ G' → (G₁ -< α' >-> G') × (G₂ -< α >-> G'))
    diamond a→s/item a→s/item ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond s→a/price s→a/price ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond a→b/cancel a→b/cancel ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond a→b/cancel a→b/split ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond a→s/no a→s/no ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond a→b/split a→b/cancel ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond a→b/split a→b/split ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond b→a/no b→a/no ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond b→a/no b→a/yes ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond b→a/yes b→a/no ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond b→a/yes b→a/yes ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond a→s/buy a→s/buy ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)

    cond-comm : ∀ {hα} {i j : Fin (suc (nchoices hα))}
                    {α'} {G} {G'} {Gᵢ} {Gⱼ'} →
                  hα ∥ₕ proj₁ α' →
                  G -< α' >-> G' →
                  G -< hα , i >-> Gᵢ →
                  G' -< hα , j >-> Gⱼ' → ∃-syntax (_-<_>->_ G (hα , j))
    cond-comm x a→s/item a→s/item ()
    cond-comm x s→a/price s→a/price ()
    cond-comm x a→b/cancel a→b/cancel ()
    cond-comm x a→b/cancel a→b/split ()
    cond-comm x a→b/split a→b/cancel ()
    cond-comm x a→b/split a→b/split ()
    cond-comm x b→a/no b→a/no ()
    cond-comm x b→a/no b→a/yes ()
    cond-comm x b→a/yes b→a/no ()
    cond-comm x b→a/yes b→a/yes ()


    Rec2Buy-Properties : BT-Prop Rec2BuyTheory
    Rec2Buy-Properties .BT-Prop.recv-act-eq x x₁ x₂ with indep? x x₁
    ... | inj₁ ii = ⊥-elim (ii (inj₂ x₂))
    ... | inj₂ refl = refl
    Rec2Buy-Properties .BT-Prop.snd≢rcv = snd≢rcv
    Rec2Buy-Properties .BT-Prop.step-det = step-det
    Rec2Buy-Properties .BT-Prop.~stepback = ~stepback
    Rec2Buy-Properties .BT-Prop.diamond = diamond
    Rec2Buy-Properties .BT-Prop.cond-comm = cond-comm

    Extra : BT-Extra Rec2BuyTheory
    Extra .BT-Extra.can-step? = can-step?

  open Behaviours
  open MPST Behaviours.Rec2Buy-Properties
  open Definitions.MPST-Extra Behaviours.Rec2Buy-Properties Behaviours.Extra

  p/A : Proc 0 0
  p/A = S ! _ , item < val (v/nat 0) >∙
        Σ S ？[ s/a-s1 ]· ((
        rec
        (ifp is-zero (var zero) -- ideally "less than whatever"
          then B ! _ , split-itm < val (v/nat 0) >∙
               Σ B ？[ s/a-b ]· (
                   ( S ! _ , buy < val (v/unit) >∙ ∅ )
                 ∷ ( v zero )
                 ∷ []
               )
          else (B ! _ , cancel < val (v/unit) >∙
               S ! _ , no-s < val (v/unit) >∙ ∅))
        ) ∷ [])

  p/B : Proc 0 0
  p/B = rec (
      Σ A ？[ s/a-b ]·
        ( (ifp is-zero (var zero)
               then A ! _ , yes-b < val (v/nat 0) >∙ ∅
               else A ! _ , no-b < val (v/unit) >∙ v zero)
        ∷ ∅
        ∷ []
        ))

  p/S : Proc 0 0
  p/S = Σ A ？[ s/a-s1 ]·
          ( A ! _ , price < val (v/nat 0) >∙
            Σ A ？[ s/a-s2 ]· ( ∅ ∷ ∅ ∷ [] )
          ∷ []
          )

  -- -- -- NOTE: Most of the below is generated by an entirely mechanical process of
  -- -- -- "case splitting + try to solve + try to contradict": it should be easy to
  -- -- -- build an algorithm

  C0 : Causal? s2 S A
  C0 BTheory.■ U P∉G′ BTheory.■ () x₁
  C0 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
  C0 (a→b/cancel BTheory.► a→s/no BTheory.► _) () P∉G′ tr' x x₁
  C0 (a→b/split BTheory.► BTheory.■) U P∉G′ BTheory.■ () x₁
  C0 (a→b/split BTheory.► BTheory.■) U P∉G′ (x₂ BTheory.► tr') x ()
  C0 (a→b/split BTheory.► b→a/no BTheory.► tr) U P∉G′ tr' x x₁ with toWitness U
  ... | (_ , _ , uu) = C0 tr (fromWitness uu) P∉G′ tr' x x₁
  C0 (a→b/split BTheory.► b→a/yes BTheory.► a→s/buy BTheory.► _) () P∉G′ tr' x x₁

  A0 : Active? s2 S
  A0 BTheory.■ tt = Active (a→b/cancel _~~>_.► _~~>_.■)
  A0 (a→b/cancel BTheory.► BTheory.■) x = Active _~~>_.■
  A0 (a→b/cancel BTheory.► a→s/no BTheory.► _) ()
  A0 (a→b/split BTheory.► BTheory.■) x = Active (b→a/no _~~>_.► a→b/cancel _~~>_.► _~~>_.■)
  A0 (a→b/split BTheory.► b→a/no BTheory.► tr) x with toWitness x
  ... | (_ , _ , xx) = A0 tr (fromWitness xx)
  A0 (a→b/split BTheory.► b→a/yes BTheory.► BTheory.■) x = Active _~~>_.■
  A0 (a→b/split BTheory.► b→a/yes BTheory.► a→s/buy BTheory.► tr) ()

  t/S : [] & [] / s0 ↑ S ⊢p< ng > p/S
  t/S = t/recv R[ a→s/item ] (λ{ a→s/item →
        t/send s→a/price (te/val tv/nat)
        (dt/skip A C0 A0 t/K)})
    where
    t/K : ∀ {G'} → (tr : s2 ~~> G')
      → {sk : True (BT-Extra.skippable? Extra S tr)}
      → (s/nat ∷ []) & [] / G' ↑ f2 ⊢p< ng > (Σ A ？[ s/a-s2 ]· (∅ ∷ ∅ ∷ []))
    t/K (a→b/cancel BTheory.► BTheory.■) = t/recv R[ a→s/no ] (λ{ a→s/no → t/end (λ{ (BTheory.in/α () x₁) ; (BTheory.in/later () x₁) }) })
    t/K (a→b/split BTheory.► b→a/no BTheory.► tr) {sk = sk} with toWitness sk
    ... | (_ , _ , sk) = t/K tr {sk = fromWitness sk}
    t/K (a→b/split BTheory.► b→a/yes BTheory.► BTheory.■) = t/recv R[ a→s/buy ] (λ{ a→s/buy → t/end (λ{ (BTheory.in/α () x₁) ; (BTheory.in/later () x₁) })})

  t/A : [] & [] / s0 ↑ A ⊢p< ng > p/A
  t/A = t/send a→s/item (te/val tv/nat) (t/recv R[ s→a/price ] (λ{ s→a/price →
        t/rec rt/refl (t/if (te/is-zero te/var)
          (t/send a→b/split (te/val tv/nat) (t/recv R[ b→a/no ]
            (λ{ b→a/no → t/var ~refl (_~~>_.■ , tt)
              ; b→a/yes → t/send a→s/buy (te/val tv/unit) ((t/end (λ{ (BTheory.in/α () x₁) ; (BTheory.in/later () x₁) })))
            })))
          (t/send a→b/cancel (te/val tv/unit) (t/send a→s/no (te/val tv/unit) ((t/end (λ{ (BTheory.in/α () x₁) ; (BTheory.in/later () x₁) })))))
        )}))

  C1 : Causal? s0 B A
  C1 BTheory.■ U P∉G′ BTheory.■ () x₁
  C1 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
  C1 (a→s/item BTheory.► BTheory.■) U P∉G′ BTheory.■ () x₁
  C1 (a→s/item BTheory.► BTheory.■) U P∉G′ (x₂ BTheory.► tr') x ()
  C1 (a→s/item BTheory.► s→a/price BTheory.► a→b/cancel BTheory.► tr) () P∉G′ tr' x x₁
  C1 (a→s/item BTheory.► s→a/price BTheory.► a→b/split BTheory.► tr) () P∉G′ tr' x x₁

  A1 : Active? s0 B
  A1 BTheory.■ x = Active (a→s/item _~~>_.► s→a/price _~~>_.► _~~>_.■)
  A1 (a→s/item BTheory.► BTheory.■) x = Active (s→a/price _~~>_.► _~~>_.■)
  A1 (a→s/item BTheory.► s→a/price BTheory.► BTheory.■) x = Active _~~>_.■
  A1 (a→s/item BTheory.► s→a/price BTheory.► a→b/cancel BTheory.► tr) ()
  A1 (a→s/item BTheory.► s→a/price BTheory.► a→b/split BTheory.► tr) ()

  t/B : [] & [] / s0 ↑ B ⊢p< ng > p/B
  t/B = t/rec rt/refl (dt/skip A C1 A1 λ{ (a→s/item BTheory.► s→a/price BTheory.► BTheory.■) →
        t/recv R[ a→b/cancel ]
          (λ{ a→b/cancel → t/end ((λ{ (BTheory.in/α a→s/no ≢S) ; (BTheory.in/α a→s/no ≢R) ; (BTheory.in/later a→s/no (BTheory.in/α () x₁)) ; (BTheory.in/later a→s/no (BTheory.in/later () x₄)) }))
            ; a→b/split →
              t/if (te/is-zero te/var)
                (t/send b→a/yes (te/val tv/nat) (t/end (λ{ (BTheory.in/α a→s/buy ≢S) ; (BTheory.in/α a→s/buy ≢R) ; (BTheory.in/later a→s/buy (BTheory.in/α () x₁)) ; (BTheory.in/later a→s/buy (BTheory.in/later () x₄)) })))
                (t/send b→a/no (te/val tv/unit) (t/var ~refl ((a→s/item _~~>_.► s→a/price _~~>_.► _~~>_.■) , (λ{ ≢S ; ≢R }) , ((λ{ ≢S ; ≢R })) , tt)))
    })
    })
