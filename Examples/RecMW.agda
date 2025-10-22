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

module Examples.RecMW where


  module Behaviours where
    open import Definitions.Expr using (s/nat; s/bool; Sort)
    open import Definitions.Common(4)
    open import Definitions.Actions(4)

    mk-fin : ∀ m n → {t : T (m <ᵇ suc n)} → Fin (suc n)
    mk-fin m n {t = t} = fromℕ< (<ᵇ⇒< m (suc n) t)

    -- The participants
    M = mk-fin 0 3
    R = mk-fin 1 3
    W1 = mk-fin 2 3
    W2 = mk-fin 3 3


    -- The Protocol states
    RecMW-State = Fin 9

    s0  = mk-fin 0 8
    s1  = mk-fin 1 8
    s1a = mk-fin 2 8
    s1b = mk-fin 3 8
    s2  = mk-fin 4 8
    s3  = mk-fin 5 8
    s4  = mk-fin 6 8
    s5  = mk-fin 7 8
    s6  = mk-fin 8 8

    pattern f0 = zero
    pattern f1 = suc zero
    pattern f2 = suc (suc zero)
    pattern f3 = suc f2
    pattern f4 = suc f3
    pattern f5 = suc f4
    pattern f6 = suc f5
    pattern f7 = suc f6
    pattern f8 = suc f7

    pattern ss0 = suc _
    pattern ss1 = suc ss0
    pattern ss2 = suc ss1
    pattern ss3 = suc ss2
    pattern ss4 = suc ss3
    pattern ss5 = suc ss4
    pattern ss6 = suc ss5
    pattern ss7 = suc ss6
    pattern ss8 = suc ss7

    -- The labels and their sorts
    -- m -> w_i
    datum = mk-fin 0 1
    stop = mk-fin 1 1
    s/m-w = s/nat ∷ s/bool ∷ []
    -- w_i -> r
    result = mk-fin 0 0
    s/w-r = s/nat ∷ []
    -- r -> m
    continue = mk-fin 0 1
    -- stop = mk-fin 1 1 (reuse 'stop' above)
    s/r-m = s/nat ∷ s/bool ∷ []

    -- The LTS
    open HeadAct

    data LTS : RecMW-State → Part → Part → {I : ℕ} → Vec Sort (suc I)
         → Fin (suc I) → RecMW-State → Set where
      m→w1/dat : LTS s0 M W1  s/m-w datum s1

      m→w2/dat1 : LTS s1  M  W2 s/m-w datum  s1a
      w1→r/res1 : LTS s1  W1 R  s/w-r result s1b
      w1→r/res2 : LTS s1a W1 R  s/w-r result s2
      m→w2/dat2 : LTS s1b M  W2 s/m-w datum s2

      w2→r/res : LTS s2 W2 R s/w-r result s3

      r→m/cont  : LTS s3 R M s/r-m continue s0
      r→m/stop  : LTS s3 R M s/r-m stop     s4

      m→w1/stop : LTS s4 M W1 s/m-w stop    s5
      m→w2/stop : LTS s5 M W2 s/m-w stop    s6

    TheLTS : RecMW-State → Action → RecMW-State → Set
    TheLTS si (P ⟶ Q # S , i) so = LTS si P Q S i so

    RecMWTheory : Definitions.BTheory 4
    RecMWTheory .Definitions.BTheory.Behav = RecMW-State
    RecMWTheory .Definitions.BTheory._-<_>->_ = TheLTS

    open Definitions.BTheory RecMWTheory

    pattern ≢S = ∈S ()
    pattern ≢R = ∈R ()

    pattern S≢S = inj₁ (∈S ())
    pattern S≢R = inj₁ (∈R ())

    pattern R≢S = inj₂ (∈S ())
    pattern R≢R = inj₂ (∈R ())

    can-step? : ∀ P G → Dec (P ∈tr G)
    can-step? _  f8 = no λ ()
    can-step? f0 f0 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr m→w1/dat (∈S refl))
    can-step? f0 f1 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr m→w2/dat1 (∈S refl))
    can-step? f0 f2 = no (λ{ (Definitions.BTheory.∈-tr w1→r/res2 (∈S ()))
                           ; (Definitions.BTheory.∈-tr w1→r/res2 (∈R ()))
                           })
    can-step? f0 f3 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr m→w2/dat2 (∈S refl))
    can-step? f0 f4 = no (λ{
        (Definitions.BTheory.∈-tr w2→r/res (∈S ()))
      ; (Definitions.BTheory.∈-tr w2→r/res (∈R ()))
      })
    can-step? f0 f5 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr r→m/cont (∈R refl))
    can-step? f0 f6 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr m→w1/stop (∈S refl))
    can-step? f0 f7 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr m→w2/stop (∈S refl))
    can-step? f1 f0 = no (
      λ{ (Definitions.BTheory.∈-tr m→w1/dat (∈S ()))
      ;  (Definitions.BTheory.∈-tr m→w1/dat (∈R ()))
      })
    can-step? f1 f1 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr w1→r/res1 (∈R refl))
    can-step? f1 f2 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr w1→r/res2 (∈R refl))
    can-step? f1 f3 = no (λ{
        (Definitions.BTheory.∈-tr m→w2/dat2 (∈S ()))
      ; (Definitions.BTheory.∈-tr m→w2/dat2 (∈R ())) })
    can-step? f1 f4 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr w2→r/res (∈R refl))
    can-step? f1 f5 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr r→m/cont (∈S refl))
    can-step? f1 f6 = no (λ{
        (Definitions.BTheory.∈-tr m→w1/stop (∈S ()))
      ; (Definitions.BTheory.∈-tr m→w1/stop (∈R ()))
      })
    can-step? f1 f7 = no (λ{
        (Definitions.BTheory.∈-tr m→w2/stop (∈S ()))
      ; (Definitions.BTheory.∈-tr m→w2/stop (∈R ()))})
    can-step? f2 f0 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr m→w1/dat (∈R refl))
    can-step? f2 f1 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr w1→r/res1 (∈S refl))
    can-step? f2 f2 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr w1→r/res2 (∈S refl))
    can-step? f2 f3 = no (λ{
        (Definitions.BTheory.∈-tr m→w2/dat2 (∈S ()))
      ; (Definitions.BTheory.∈-tr m→w2/dat2 (∈R ()))})
    can-step? f2 f4 = no (λ{
      (Definitions.BTheory.∈-tr w2→r/res (∈S ()))
      ; (Definitions.BTheory.∈-tr w2→r/res (∈R ()))
      })
    can-step? f2 f5 = no (λ{
      (Definitions.BTheory.∈-tr r→m/cont (∈S ()))
      ; (Definitions.BTheory.∈-tr r→m/cont (∈R ()))
      ; (Definitions.BTheory.∈-tr r→m/stop (∈S ()))
      ; (Definitions.BTheory.∈-tr r→m/stop (∈R ()))
      })
    can-step? f2 f6 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr m→w1/stop (∈R refl))
    can-step? f2 f7 = no (λ{
      (Definitions.BTheory.∈-tr m→w2/stop (∈S ()))
      ; (Definitions.BTheory.∈-tr m→w2/stop (∈R ()))
      })
    can-step? f3 f0 = no (λ{
      (Definitions.BTheory.∈-tr m→w1/dat (∈S ()))
      ; (Definitions.BTheory.∈-tr m→w1/dat (∈R ()))
      })
    can-step? f3 f1 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr m→w2/dat1 (∈R refl))
    can-step? f3 f2 = no (λ{
      (Definitions.BTheory.∈-tr w1→r/res2 (∈S ()))
      ; (Definitions.BTheory.∈-tr w1→r/res2 (∈R ()))
      })
    can-step? f3 f3 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr m→w2/dat2 (∈R refl))
    can-step? f3 f4 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr w2→r/res (∈S refl))
    can-step? f3 f5 = no (λ{
      (Definitions.BTheory.∈-tr r→m/cont (∈S ()))
      ; (Definitions.BTheory.∈-tr r→m/cont (∈R ()))
      ; (Definitions.BTheory.∈-tr r→m/stop (∈S ()))
      ; (Definitions.BTheory.∈-tr r→m/stop (∈R ()))
      })
    can-step? f3 f6 = no (λ{
      (Definitions.BTheory.∈-tr m→w1/stop (∈S ()))
      ; (Definitions.BTheory.∈-tr m→w1/stop (∈R ()))
      })
    can-step? f3 f7 = true Relation.Nullary.because
                       Relation.Nullary.ofʸ (∈-tr m→w2/stop (∈R refl))


    indep? : ∀ {G} {α} {α'} {G'} {G''} →
         G -< α >-> G' → G -< α' >-> G'' → (proj₁ α) ⋔ (proj₁ α') ⊎ proj₁ α ≡ proj₁ α'
    indep? m→w1/dat m→w1/dat = inj₂ refl
    indep? m→w2/dat1 m→w2/dat1 = inj₂ refl
    indep? m→w2/dat1 w1→r/res1 = inj₁ (disj?f (M ⟶ W2 # (s/unit ∷ [])) (W1 ⟶ R # s/w-r))
    indep? w1→r/res1 m→w2/dat1 = inj₁ (disj?f (W1 ⟶ R # (s/bool ∷ [])) (M ⟶ W2 # s/m-w))
    indep? w1→r/res1 w1→r/res1 = inj₂ refl
    indep? w1→r/res2 w1→r/res2 = inj₂ refl
    indep? m→w2/dat2 m→w2/dat2 = inj₂ refl
    indep? w2→r/res w2→r/res = inj₂ refl
    indep? r→m/cont r→m/cont = inj₂ refl
    indep? r→m/cont r→m/stop = inj₂ refl
    indep? r→m/stop r→m/cont = inj₂ refl
    indep? r→m/stop r→m/stop = inj₂ refl
    indep? m→w1/stop m→w1/stop = inj₂ refl
    indep? m→w2/stop m→w2/stop = inj₂ refl

    snd≢rcv : ∀ {G} {G'} {α} → G -< α >-> G' → sender α ≢ receiver α
    snd≢rcv () refl

    step-det : ∀ {G} {α} {G'} {G''} →
           G -< α >-> G' → G -< α >-> G'' → G' ≡ G''
    step-det m→w1/dat m→w1/dat = refl
    step-det m→w2/dat1 m→w2/dat1 = refl
    step-det w1→r/res1 w1→r/res1 = refl
    step-det w1→r/res2 w1→r/res2 = refl
    step-det m→w2/dat2 m→w2/dat2 = refl
    step-det w2→r/res w2→r/res = refl
    step-det r→m/cont r→m/cont = refl
    step-det r→m/stop r→m/stop = refl
    step-det m→w1/stop m→w1/stop = refl
    step-det m→w2/stop m→w2/stop = refl

    open _~_
    ~≡ : ∀ G G' → G ~ G' → G ≡ G'
    ~≡ f0 f0 _ = refl
    ~≡ f0 ss0 b with ~L b m→w1/dat
    ... | fst , () , snd
    ~≡ f1 f0 b  with ~L b m→w2/dat1
    ... | fst , () , snd
    ~≡ f1 f1 _ = refl
    ~≡ f1 f2 b  with ~R b w1→r/res2
    ... | fst , w1→r/res1 , b' with ~R b' w2→r/res
    ... | _ , () , _
    ~≡ f1 ss2 b  with ~L b w1→r/res1
    ... | fst , () , snd

    ~≡ f2 f0 b  with ~L b w1→r/res2
    ... | fst , () , snd
    ~≡ f2 f1 b  with ~L b w1→r/res2
    ... | fst , w1→r/res1 , b' with ~L b' w2→r/res
    ... | _ , () , _
    ~≡ f2 f2 _ = refl
    ~≡ f2 ss2 b with ~L b w1→r/res2
    ... | fst , () , snd

    ~≡ f3 f0 b  with ~L b m→w2/dat2
    ... | fst , () , snd
    ~≡ f3 f1 b  with ~R b w1→r/res1
    ... | fst ,() , _
    ~≡ f3 f2 b  with ~L b m→w2/dat2
    ... | fst ,() , _
    ~≡ f3 f3 _ = refl
    ~≡ f3 ss3 b with ~L b m→w2/dat2
    ... | fst , () , snd

    ~≡ f4 f0 b  with ~R b m→w1/dat
    ... | fst , () , snd
    ~≡ f4 f1 b  with ~R b m→w2/dat1
    ... | fst ,() , _
    ~≡ f4 f2 b  with ~R b w1→r/res2
    ... | fst ,() , _
    ~≡ f4 f3 b  with ~R b m→w2/dat2
    ... | fst ,() , _
    ~≡ f4 f4 _ = refl
    ~≡ f4 ss4 b with ~L b w2→r/res
    ... | fst , () , snd

    ~≡ f5 f0 b  with ~R b m→w1/dat
    ... | fst , () , snd
    ~≡ f5 f1 b  with ~R b m→w2/dat1
    ... | fst ,() , _
    ~≡ f5 f2 b  with ~R b w1→r/res2
    ... | fst ,() , _
    ~≡ f5 f3 b  with ~R b m→w2/dat2
    ... | fst ,() , _
    ~≡ f5 f4 b  with ~R b w2→r/res
    ... | fst ,() , _
    ~≡ f5 f5 _ = refl
    ~≡ f5 ss5 b with ~L b r→m/cont
    ... | fst , () , snd

    ~≡ f6 f0 b  with ~R b m→w1/dat
    ... | fst , () , snd
    ~≡ f6 f1 b  with ~R b m→w2/dat1
    ... | fst ,() , _
    ~≡ f6 f2 b  with ~R b w1→r/res2
    ... | fst ,() , _
    ~≡ f6 f3 b  with ~R b m→w2/dat2
    ... | fst ,() , _
    ~≡ f6 f4 b  with ~R b w2→r/res
    ... | fst ,() , _
    ~≡ f6 f5 b  with ~R b r→m/cont
    ... | fst ,() , _
    ~≡ f6 f6 _ = refl
    ~≡ f6 ss6 b with ~L b m→w1/stop
    ... | fst , () , snd

    ~≡ f7 f0 b  with ~R b m→w1/dat
    ... | fst , () , snd
    ~≡ f7 f1 b  with ~R b m→w2/dat1
    ... | fst ,() , _
    ~≡ f7 f2 b  with ~R b w1→r/res2
    ... | fst ,() , _
    ~≡ f7 f3 b  with ~R b m→w2/dat2
    ... | fst ,() , _
    ~≡ f7 f4 b  with ~R b w2→r/res
    ... | fst ,() , _
    ~≡ f7 f5 b  with ~R b r→m/cont
    ... | fst ,() , _
    ~≡ f7 f6 b  with ~R b m→w1/stop
    ... | fst ,() , _
    ~≡ f7 f7 _ = refl
    ~≡ f7 ss7 b with ~L b m→w2/stop
    ... | fst , () , snd

    ~≡ f8 f0 b  with ~R b m→w1/dat
    ... | fst , () , snd
    ~≡ f8 f1 b  with ~R b m→w2/dat1
    ... | fst ,() , _
    ~≡ f8 f2 b  with ~R b w1→r/res2
    ... | fst ,() , _
    ~≡ f8 f3 b  with ~R b m→w2/dat2
    ... | fst ,() , _
    ~≡ f8 f4 b  with ~R b w2→r/res
    ... | fst ,() , _
    ~≡ f8 f5 b  with ~R b r→m/cont
    ... | fst ,() , _
    ~≡ f8 f6 b  with ~R b m→w1/stop
    ... | fst ,() , _
    ~≡ f8 f7 b  with ~R b m→w2/stop
    ... | fst ,() , _
    ~≡ f8 f8 _ = refl

    diamond : ∀ {G} {α} {G₁} {α'} {G₂} →
          G -< α >-> G₁ →
          G -< α' >-> G₂ →
          α ∥ α' → ∃-syntax (λ G' → (G₁ -< α' >-> G') × (G₂ -< α >-> G'))
    diamond m→w1/dat m→w1/dat ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond m→w2/dat1 m→w2/dat1 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond m→w2/dat1 w1→r/res1 ii = _ , (w1→r/res2 , m→w2/dat2)
    diamond w1→r/res1 m→w2/dat1 ii = s2 , m→w2/dat2 , w1→r/res2
    diamond w1→r/res1 w1→r/res1 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond w1→r/res2 w1→r/res2 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond m→w2/dat2 m→w2/dat2 ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond w2→r/res w2→r/res   ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond r→m/cont r→m/cont   ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond r→m/cont r→m/stop   ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond r→m/stop r→m/cont   ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond r→m/stop r→m/stop   ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond m→w1/stop m→w1/stop ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)
    diamond m→w2/stop m→w2/stop ii = ⊥-elim (toWitnessFalse {a? = _ ∥h? _} tt ii)

    ~stepback : ∀ {α} {G0} {G1} {G1'} →
            G1 ~ G1' →
            G0 -< α >-> G1 → ∃-syntax (λ G0' → (G0 ~ G0') × (G0' -< α >-> G1'))
    ~stepback b st with ~≡ _ _ b
    ~stepback b st | refl = _ , (~refl , st)

    no-ph-comm : ∀ {hα} {i j : Fin (suc (nchoices hα))}
               {α'} {G} {G'} {Gᵢ} {Gⱼ'} →
             hα ∥ₕ proj₁ α' →
             G -< α' >-> G' →
             G -< hα , i >-> Gᵢ →
             G' -< hα , j >-> Gⱼ' → ∃-syntax (_-<_>->_ G (hα , j))
    no-ph-comm ii m→w1/dat m→w1/dat ()
    no-ph-comm ii m→w2/dat1 w1→r/res1 w1→r/res2 = _ , w1→r/res1
    no-ph-comm ii w1→r/res1 m→w2/dat1 m→w2/dat2 = s1a , m→w2/dat1
    no-ph-comm ii w1→r/res2 w1→r/res2 ()
    no-ph-comm ii m→w2/dat2 m→w2/dat2 ()
    no-ph-comm ii w2→r/res w2→r/res ()
    no-ph-comm ii r→m/cont r→m/cont ()
    no-ph-comm ii r→m/cont r→m/stop ()
    no-ph-comm ii r→m/stop r→m/cont ()
    no-ph-comm ii r→m/stop r→m/stop ()
    no-ph-comm ii m→w1/stop m→w1/stop ()

    RecMW-Properties : BT-Prop RecMWTheory
    RecMW-Properties .BT-Prop.recv-act-eq x x₁ x₂ with indep? x x₁
    ... | inj₁ ii = ⊥-elim (ii (inj₂ x₂))
    ... | inj₂ refl = refl
    RecMW-Properties .BT-Prop.snd≢rcv = snd≢rcv
    RecMW-Properties .BT-Prop.step-det = step-det
    RecMW-Properties .BT-Prop.~stepback = ~stepback
    RecMW-Properties .BT-Prop.diamond = diamond
    RecMW-Properties .BT-Prop.cond-comm = no-ph-comm

    Extra : BT-Extra RecMWTheory
    Extra .BT-Extra.can-step? = can-step?

  open Behaviours
  open MPST Behaviours.RecMW-Properties
  open Definitions.MPST-Extra Behaviours.RecMW-Properties Behaviours.Extra

  p/M : Proc 0 0
  p/M = rec (W1 ! _ , datum < val (v/nat 0) >∙
            (W2 ! _ , datum < val (v/nat 1) >∙
            (Σ R ？[ s/r-m ]·
              ( v zero
              ∷ (W1 ! _ , stop < val (v/bool false) >∙
                (W2 ! _ , stop < val (v/bool false) >∙
                ∅))
              ∷ []))))

  p/R : Proc 0 0
  p/R = rec (Σ W1 ？[ s/w-r ]· (
            (Σ W2 ？[ s/w-r ]· (
            (ifp (is-zero (var zero))
            then M ! _ , stop < val (v/bool true) >∙ ∅
            else (M ! _ , continue < var (suc zero ) >∙ v zero))
            ∷ [])) ∷ []))

  p/W : Proc 0 0
  p/W
    = Σ M ？[ s/m-w ]·
         ( rec
           (R ! (_ , result) < (val (v/nat 0)) >∙
              (Σ M ？[ s/m-w ]·
                ( v zero
                ∷ ∅
                ∷ [])))
         ∷ ∅
         ∷ [])

  C1a0R : Causal? s1a f0 R
  C1a0R BTheory.■ U P∉G′ BTheory.■ () x₁
  C1a0R BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
  C1a0R (w1→r/res2 BTheory.► BTheory.■) U P∉G′ BTheory.■ () x₁
  C1a0R (w1→r/res2 BTheory.► BTheory.■) U P∉G′ (x₂ BTheory.► tr') x ()
  C1a0R (w1→r/res2 BTheory.► w2→r/res BTheory.► r→m/cont BTheory.► tr) () P∉G′ tr' x x₁
  C1a0R (w1→r/res2 BTheory.► w2→r/res BTheory.► r→m/stop BTheory.► tr) () P∉G′ tr' x x₁

  A1a0 : Active? s1a f0
  A1a0 BTheory.■ tt = Active (w1→r/res2 _~~>_.► w2→r/res _~~>_.► _~~>_.■)
  A1a0 (w1→r/res2 BTheory.► BTheory.■) tt = Active (w2→r/res _~~>_.► _~~>_.■)
  A1a0 (w1→r/res2 BTheory.► w2→r/res BTheory.► BTheory.■) x = Active _~~>_.■
  A1a0 (w1→r/res2 BTheory.► w2→r/res BTheory.► r→m/cont BTheory.► tr) ()
  A1a0 (w1→r/res2 BTheory.► w2→r/res BTheory.► r→m/stop BTheory.► tr) ()

  t/M : [] & [] / s0 ↑ M ⊢p< ng > p/M
  t/M = t/rec rt/refl
    (t/send m→w1/dat (te/val tv/nat)
    (t/send m→w2/dat1 (te/val tv/nat)
    (dt/skip R C1a0R A1a0
        λ{ (w1→r/res2 BTheory.► w2→r/res BTheory.► BTheory.■) →
        t/recv R[ r→m/cont ]
          λ{ r→m/cont → t/var ~refl (_~~>_.■ , tt)
           ; r→m/stop → t/send m→w1/stop (te/val tv/bool) (t/send m→w2/stop (te/val tv/bool) (t/end λ{ (BTheory.in/α () x₁) ; (BTheory.in/later () x₄) }))
           }
        }
    )))

  C2 : Causal? s0 R W1
  C2 BTheory.■ U P∉G′ BTheory.■ () x₁
  C2 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
  C2 (m→w1/dat BTheory.► m→w2/dat1 BTheory.► w1→r/res2 BTheory.► tr) () P∉G′ tr' x x₁

  A2 : Active? s0 R
  A2 BTheory.■ tt = Active (m→w1/dat _~~>_.► _~~>_.■)
  A2 (m→w1/dat BTheory.► BTheory.■) x = Active ■
  A2 (m→w1/dat BTheory.► m→w2/dat1 BTheory.► BTheory.■) x = Active _~~>_.■
  A2 (m→w1/dat BTheory.► m→w2/dat1 BTheory.► w1→r/res2 BTheory.► tr) ()

  C3 : Causal? s1b f1 W2
  C3 BTheory.■ U P∉G′ BTheory.■ () x₁
  C3 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
  C3 (m→w2/dat2 BTheory.► w2→r/res BTheory.► tr) () P∉G′ tr' x x₁

  A3 : Active? s1b f1
  A3 BTheory.■ x = Active (m→w2/dat2 _~~>_.► _~~>_.■)
  A3 (m→w2/dat2 BTheory.► BTheory.■) x = Active _~~>_.■
  A3 (m→w2/dat2 BTheory.► w2→r/res BTheory.► tr) ()

  t/R : [] & [] / s0 ↑ R ⊢p< ng > p/R
  t/R = t/rec rt/refl
    (dt/skip W1 C2 A2
    λ{ (m→w1/dat BTheory.► BTheory.■) →
    t/recv R[ w1→r/res1 ] λ{ w1→r/res1 →
    dt/skip W2 C3 A3 λ{
      (m→w2/dat2 BTheory.► BTheory.■) →
    t/recv R[ w2→r/res ] λ{ w2→r/res →
      t/if (te/is-zero te/var)
        (t/send r→m/stop (te/val tv/bool) ((t/end (λ{ (BTheory.in/α m→w1/stop ≢S) ;
                           (BTheory.in/α m→w1/stop ≢R) ; (BTheory.in/later
                           m→w1/stop (BTheory.in/α m→w2/stop ≢S)) ;
                           (BTheory.in/later m→w1/stop (BTheory.in/α m→w2/stop
                           ≢R)); (BTheory.in/later m→w1/stop (BTheory.in/later
                           m→w2/stop (BTheory.in/α () x₁))) ; (BTheory.in/later
                           m→w1/stop (BTheory.in/later m→w2/stop
                           (BTheory.in/later () x₃)))}))))
        (t/send r→m/cont te/var (t/var ~refl (_~~>_.■ , tt)))
    }}}})

  C4 : Causal? s1b (sender ((f2 ⟶ f1 # s/w-r) , result)) M
  C4 BTheory.■ U P∉G′ BTheory.■ () x₁
  C4 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
  C4 (m→w2/dat2 BTheory.► BTheory.■) U P∉G′ (w2→r/res BTheory.► BTheory.■) () x₁
  C4 (m→w2/dat2 BTheory.► BTheory.■) U P∉G′ (w2→r/res BTheory.► x₂ BTheory.► tr') x ()
  C4 (m→w2/dat2 BTheory.► w2→r/res BTheory.► BTheory.■) U P∉G′ BTheory.■ () x₁
  C4 (m→w2/dat2 BTheory.► w2→r/res BTheory.► BTheory.■) U P∉G′ (x₂ BTheory.► tr') x ()
  C4 (m→w2/dat2 BTheory.► w2→r/res BTheory.► r→m/cont BTheory.► m→w1/dat BTheory.► tr) () P∉G′ tr' x x₁
  C4 (m→w2/dat2 BTheory.► w2→r/res BTheory.► r→m/stop BTheory.► m→w1/stop BTheory.► tr) () P∉G′ tr' x x₁

  A4 : Active? s1b (sender ((f2 ⟶ f1 # s/w-r) , result))
  A4 BTheory.■ x = Active (m→w2/dat2 _~~>_.► w2→r/res _~~>_.► r→m/cont _~~>_.► _~~>_.■)
  A4 (m→w2/dat2 BTheory.► BTheory.■) x = Active (w2→r/res _~~>_.► r→m/cont _~~>_.► _~~>_.■)
  A4 (m→w2/dat2 BTheory.► w2→r/res BTheory.► BTheory.■) x = Active (r→m/cont _~~>_.► _~~>_.■)
  A4 (m→w2/dat2 BTheory.► w2→r/res BTheory.► r→m/cont BTheory.► BTheory.■) x = Active _~~>_.■
  A4 (m→w2/dat2 BTheory.► w2→r/res BTheory.► r→m/cont BTheory.► m→w1/dat BTheory.► tr) ()
  A4 (m→w2/dat2 BTheory.► w2→r/res BTheory.► r→m/stop BTheory.► BTheory.■) x = Active _~~>_.■
  A4 (m→w2/dat2 BTheory.► w2→r/res BTheory.► r→m/stop BTheory.► m→w1/stop BTheory.► tr) ()

  t/W1 : [] & [] / s0 ↑ W1 ⊢p< ng > p/W
  t/W1 = t/recv R[ m→w1/dat ] (λ{ m→w1/dat →
         t/rec rt/refl
         (t/send w1→r/res1 (te/val tv/nat)
         (dt/skip M C4 A4 λ{
           (m→w2/dat2 BTheory.► w2→r/res BTheory.► r→m/cont BTheory.► BTheory.■) →
             t/recv R[ m→w1/dat ] (λ{ m→w1/dat → t/var ~refl (_~~>_.■ , tt) })
         ; (m→w2/dat2 BTheory.► w2→r/res BTheory.► r→m/stop BTheory.► BTheory.■) →
             t/recv R[ m→w1/stop ] (λ{ m→w1/stop → t/end (λ{ (BTheory.in/α m→w2/stop (∈S ())) ; (BTheory.in/α m→w2/stop (∈R ())) ; (BTheory.in/later m→w2/stop (BTheory.in/α () x₁)) ; (BTheory.in/later m→w2/stop (BTheory.in/later () x₁)) })})
         }))})

  C5 : Causal? s0 W2 M
  C5 BTheory.■ U P∉G′ BTheory.■ () x₁
  C5 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
  C5 (m→w1/dat BTheory.► w1→r/res1 BTheory.► m→w2/dat2 BTheory.► BTheory.■) U () tr' x x₁
  C5 (m→w1/dat BTheory.► w1→r/res1 BTheory.► m→w2/dat2 BTheory.► x₂ BTheory.► tr) () P∉G′ tr' x x₁

  U5 : Active? s0 W2
  U5 BTheory.■ x = Active (m→w1/dat _~~>_.► _~~>_.■)
  U5 (m→w1/dat BTheory.► BTheory.■) x = Active _~~>_.■
  U5 (m→w1/dat BTheory.► w1→r/res1 BTheory.► BTheory.■) x = Active _~~>_.■
  U5 (m→w1/dat BTheory.► w1→r/res1 BTheory.► m→w2/dat2 BTheory.► tr) ()

  C6 : Causal? s1a f3 R
  C6 BTheory.■ U P∉G′ BTheory.■ () x₁
  C6 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
  C6 (w1→r/res2 BTheory.► w2→r/res BTheory.► _) () P∉G′ tr' x x₁

  A6 : Active? s1a f3
  A6 BTheory.■ x = Active (w1→r/res2 _~~>_.► _~~>_.■)
  A6 (w1→r/res2 BTheory.► BTheory.■) x = Active _~~>_.■
  A6 (w1→r/res2 BTheory.► w2→r/res BTheory.► tr) ()

  C7 : Causal? s3 (sender ((f3 ⟶ f1 # s/w-r) , result)) M
  C7 BTheory.■ U P∉G′ BTheory.■ () x₁
  C7 BTheory.■ U P∉G′ (x₂ BTheory.► tr') x ()
  C7 (r→m/cont BTheory.► BTheory.■) U P∉G′ BTheory.■ () x₁
  C7 (r→m/cont BTheory.► BTheory.■) U P∉G′ (x₂ BTheory.► tr') x ()
  C7 (r→m/cont BTheory.► m→w1/dat BTheory.► w1→r/res1 BTheory.► m→w2/dat2 BTheory.► BTheory.■) U () tr' x x₁
  C7 (r→m/cont BTheory.► m→w1/dat BTheory.► w1→r/res1 BTheory.► m→w2/dat2 BTheory.► x₂ BTheory.► tr) () P∉G′ tr' x x₁
  C7 (r→m/stop BTheory.► BTheory.■) U P∉G′ BTheory.■ () x₁
  C7 (r→m/stop BTheory.► BTheory.■) U P∉G′ (x₂ BTheory.► tr') x ()
  C7 (r→m/stop BTheory.► m→w1/stop BTheory.► m→w2/stop BTheory.► BTheory.■) () P∉G′ tr' x x₁
  C7 (r→m/stop BTheory.► m→w1/stop BTheory.► m→w2/stop BTheory.► x₂ BTheory.► tr) () P∉G′ tr' x x₁

  A7 : Active? s3 (sender ((f3 ⟶ f1 # s/w-r) , result))
  A7 BTheory.■ x = Active (r→m/cont _~~>_.► m→w1/dat _~~>_.► _~~>_.■)
  A7 (r→m/cont BTheory.► BTheory.■) x = Active (m→w1/dat _~~>_.► _~~>_.■)
  A7 (r→m/cont BTheory.► m→w1/dat BTheory.► BTheory.■) x = Active _~~>_.■
  A7 (r→m/cont BTheory.► m→w1/dat BTheory.► w1→r/res1 BTheory.► BTheory.■) x = Active _~~>_.■
  A7 (r→m/cont BTheory.► m→w1/dat BTheory.► w1→r/res1 BTheory.► m→w2/dat2 BTheory.► tr) ()
  A7 (r→m/stop BTheory.► BTheory.■) x = Active (m→w1/stop ► ■)
  A7 (r→m/stop BTheory.► m→w1/stop BTheory.► BTheory.■) x = Active ■
  A7 (r→m/stop BTheory.► m→w1/stop BTheory.► m→w2/stop BTheory.► tr) ()

  t/W2 : [] & [] / s0 ↑ W2 ⊢p< ng > p/W
  t/W2 = dt/skip M C5 U5 λ{
    (m→w1/dat BTheory.► BTheory.■) → t/recv R[ m→w2/dat1 ]
    (λ{ m→w2/dat1 → t/rec _=[_]=>ᵣ_.rt/refl (dt/skip R C6 A6 λ{ (w1→r/res2 BTheory.► BTheory.■) →
    t/send w2→r/res (te/val tv/nat) (dt/skip M C7 A7 λ{
      (r→m/cont BTheory.► m→w1/dat BTheory.► BTheory.■) → t/recv R[ m→w2/dat1 ] λ{ m→w2/dat1 → t/var ~refl (_~~>_.■ , tt) }
    ; (r→m/stop BTheory.► m→w1/stop BTheory.► BTheory.■) → t/recv R[ m→w2/stop ] λ{ m→w2/stop →
                           t/end λ{ (BTheory.in/α () x₁) ; (BTheory.in/later () x₄) }}
    })
    })
    })}
