{-# OPTIONS --guardedness #-}
open import Level using (Level) renaming (suc to lsuc)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤ ; tt)
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Fin hiding (_+_ ; _-_) renaming (_≟_ to _≟f_)
open import Data.Vec hiding ([_]) renaming (lookup to lu; removeAt to _-_)
open import Data.Vec.Relation.Unary.Any
open import Data.Product
open import Data.Sum
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Empty using (⊥)
-- open import Data.Unit using (⊤)
open import Function using (_∘_)
open import Relation.Unary using (Pred ; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl ; subst ; sym)
open import Relation.Nullary using (Dec; yes; no ; ¬_)
open import Relation.Nullary.Negation using (contraposition)
open import Utils

module Definitions where

open import Definitions.Expr public
open import Definitions.Guard public
open import Definitions.Behav public

-- Processes

module MPST {N : ℕ}{B : BTheory N}(BP : BT-Prop B) where
  -- N is the number of participants in the session
  open BTheory B public
  open BT-Prop BP

  private
    variable
      γ δ ξ : ℕ

  open import Definitions.Common (N) public
  open import Definitions.Proc (N) public
  open Subst
  open import Definitions.Actions (N) public
  open HeadAct

  data is-comm {γ δ} : Part → Proc γ δ → Set where
    is-send : ∀ {Q ℓ E Pr} → is-comm Q (Q ! ℓ < E >∙ Pr)
    is-recv : ∀ {Q I}{S : Vec Sort (suc I)}{B} → is-comm Q (Σ Q ？[ S ]· B)

  open _~_

  record Pskip P Q G (Pr : Proc δ γ) : Set where
    constructor [_&_&_&_]
    field
      s-iscomm : is-comm Q Pr
      s-nonact : ∀ {α G'} → G -< α >-> G' → P ∉α α -- P is not currently enabled
      {s-aG} : Behav
      s-activ : G ~~> s-aG
      s-skippable : skippable P s-activ -- P will be enabled in the future

  data _&_&_/_↑_⊢p<_>_
    (Γ : Vec Sort γ)
    (Δ : Vec Behav δ)
    (Ξ : Vec Behav ξ)
    (G : Behav) : Part → (g : Guard) -> Proc γ δ -> Set where
    t/send : ∀{g P Q I i G'}{Pr : Proc γ δ}{E : Exp γ}{S : Vec Sort (suc I)}
      → (gr : G -< P ⟶ Q # S , i >-> G')
      → (etd : Γ ⊢e E ∶ lu S i)
      → (td : Γ & Δ & [] / G' ↑ P ⊢p< ng > Pr)
      → Γ & Δ & Ξ / G ↑ P ⊢p< g > (Q ! _ , i < E >∙ Pr)

    t/recv : ∀{g P Q I i G' Br}{S : Vec Sort (suc I)}
      → (gr : G -< P ⟶ Q # S , i >-> G')
      → (conts : ∀ {i G'}
          → G -< P ⟶ Q # S , i >-> G'
          → (lu S i ∷ Γ) & Δ & [] / G' ↑ Q ⊢p< ng > (lu Br i))
      → Γ & Δ & Ξ / G ↑ Q ⊢p< g > (Σ P ？[ S ]· Br)

    t/skip-next : ∀ {g P Q Pr}
      → Pskip P Q G Pr
      → (ktd : ∀ {G' α} → G -< α >-> G' → Γ & Δ & G ∷ Ξ / G' ↑ P ⊢p< g > Pr)
      → Γ & Δ & Ξ / G ↑ P ⊢p< g > Pr

    t/skip-close : ∀ {g P Q Pr}
      → Pskip P Q G Pr -- not needed!!! TODO: remove
      → Any (G ~_) Ξ
      → Γ & Δ & Ξ / G ↑ P ⊢p< g > Pr

    t/if : ∀{P E Pr Pr' g}
      → (etd : Γ ⊢e E ∶ s/bool)
      → (ttd : Γ & Δ & [] / G ↑ P ⊢p< g > Pr)
      → (ftd : Γ & Δ & [] / G ↑ P ⊢p< g > Pr')
      → Γ & Δ & Ξ / G ↑ P ⊢p< g > (ifp E then Pr else Pr')

    t/rec : ∀{P Pr Gr}
      → Gr =<¬ P >=>ᵣ G
      → Γ & (Gr ∷ Δ) & [] / Gr ↑ P ⊢p< mg > Pr
      → Γ & Δ & Ξ / G ↑ P ⊢p< ng > rec Pr

    t/var : ∀{P X Gr}
      → Gr ~ lu Δ X
      → Gr =<¬ P >=> G
      → Γ & Δ & Ξ / G ↑ P ⊢p< ng > v X

    t/end : ∀ {P}
      → ¬ (P ∈T G)
      → Γ & Δ & Ξ / G ↑ P ⊢p< ng > ∅

  data _~~_ : ∀ {δ δ'} → Vec Behav δ → Vec Behav δ' → Set where
    ~~-cons : ∀ {G G' δ δ'} {Δ : Vec Behav δ} {Δ' : Vec Behav δ'}
      → G ~ G' → Δ ~~ Δ' → (G ∷ Δ) ~~ (G' ∷ Δ')
    ~~-nil : [] ~~ []

  ~~-refl : ∀ {δ} {Δ : Vec Behav δ} → Δ ~~ Δ
  ~~-refl {Δ = []} = ~~-nil
  ~~-refl {Δ = x ∷ Δ} = ~~-cons ~refl ~~-refl

  t/lu/bisim : ∀ {G : Behav}
               {Δ Δ' : Vec Behav δ} (x : Δ ~~ Δ')
               (X : Fin δ) (y : G ~ lu Δ X) →
             G ~ lu Δ' X
  t/lu/bisim (~~-cons x y) zero z = ~trans z x
  t/lu/bisim (~~-cons x y) (suc X) z = t/lu/bisim y X z

  Any~ : ∀ {ξ ξ'}{Ξ : Vec Behav ξ}{Ξ' : Vec Behav ξ'}{B B'}
    → B ~ B' → Ξ ~~ Ξ' → Any (B ~_) Ξ → Any (B' ~_) Ξ'
  Any~ B~B' (~~-cons x Ξ~Ξ') (here px) = here (~trans (~sym B~B') (~trans px x))
  Any~ B~B' (~~-cons x Ξ~Ξ') (there a) = there (Any~ B~B' Ξ~Ξ' a)

  open Pskip
  Pskip~ : ∀ {P Q G G' δ γ}{Pr : Proc δ γ}
    → G ~ G' → Pskip P Q G Pr → Pskip P Q G' Pr
  Pskip~ G~G' [ s-ic & s-na & s-a & s-sk ] .s-iscomm = s-ic
  Pskip~ G~G' [ s-ic & s-na & s-a & s-sk ] .s-nonact = s-na ∘ ~R→ G~G'
  Pskip~ G~G' [ s-ic & s-na & s-a & s-sk ] .s-aG = _
  Pskip~ G~G' [ s-ic & s-na & s-a & s-sk ] .s-activ = ~~>~→ G~G' s-a
  Pskip~ G~G' [ s-ic & s-na & s-a & s-sk ] .s-skippable
    = skippable~ G~G' s-a s-sk

  td/bisim : ∀ {Γ : Vec Sort γ}{Δ Δ' : Vec Behav δ}{Ξ Ξ' : Vec Behav ξ}
    → ∀ {G G' P Pr g}
    → G ~ G' → Δ ~~ Δ' → Ξ ~~ Ξ'
    → Γ & Δ  & Ξ  / G  ↑ P ⊢p< g > Pr
    → Γ & Δ' & Ξ' / G' ↑ P ⊢p< g > Pr
  td/bisim G~G' Δ~Δ' Ξ~Ξ' (t/send gr etd td)
    = t/send (~L→ G~G' gr) etd (td/bisim (~L→~ G~G' gr) Δ~Δ' ~~-nil td)
  td/bisim G~G' Δ~Δ' Ξ~Ξ' (t/recv gr conts)
    = t/recv (~L→ G~G' gr)
             λ gr → td/bisim (~R→~ G~G' gr) Δ~Δ' ~~-nil (conts (~R→ G~G' gr))
  td/bisim G~G' Δ~Δ' Ξ~Ξ' (t/skip-next s ktd)
    = t/skip-next (Pskip~ G~G' s)
                  λ gr → td/bisim (~R→~ G~G' gr) Δ~Δ' (~~-cons G~G' Ξ~Ξ')
                                  (ktd (~R→ G~G' gr))
  td/bisim G~G' Δ~Δ' Ξ~Ξ' (t/skip-close s ∈Ξ)
    = t/skip-close (Pskip~ G~G' s)
                   (Any~ G~G' Ξ~Ξ' ∈Ξ)
  td/bisim G~G' Δ~Δ' Ξ~Ξ' (t/if etd td td₁)
    = t/if etd (td/bisim G~G' Δ~Δ' ~~-nil td) (td/bisim G~G' Δ~Δ' ~~-nil td₁)
  td/bisim G~G' Δ~Δ' Ξ~Ξ' (t/rec gr td)
    = t/rec (~tb→ G~G' gr)
            (td/bisim (~tb~ G~G' gr) (~~-cons (~tb~ G~G' gr) Δ~Δ') ~~-nil td)
  td/bisim G~G' Δ~Δ' Ξ~Ξ' (t/var x gr)
    = t/var (t/lu/bisim Δ~Δ' _ (~trans (~sym (~tbl~ G~G' gr)) x))
            (~tbl→ G~G' gr)
  td/bisim G~G' Δ~Δ' Ξ~Ξ' (t/end p∉g)
    = t/end (contraposition (∈~ (~sym G~G')) p∉g)

  t/bisim : ∀ {Γ : Vec Sort γ}{Δ : Vec Behav δ}{Ξ : Vec Behav ξ}
    → ∀ {G G' P Pr g}
    → G ~ G'
    → Γ & Δ & Ξ / G  ↑ P ⊢p< g > Pr
    → Γ & Δ & Ξ / G' ↑ P ⊢p< g > Pr
  t/bisim G~G' td = td/bisim G~G' ~~-refl ~~-refl td

  -- FIXME: refactor
  Any/insert : ∀ {G G' ξ ξ'}{Ξ : Vec Behav ξ}{Ξ' : Vec Behav ξ'}
    → Any (_~_ G') (Ξ' ++ G ∷ Ξ) → G' ~ G ⊎ Any (G' ~_) (Ξ' ++ Ξ)
  Any/insert {Ξ' = []} (here px) = inj₁ px
  Any/insert {Ξ' = []} (there a) = inj₂ a
  Any/insert {Ξ' = x ∷ Ξ'} (here px) = inj₂ (here px)
  Any/insert {Ξ' = x ∷ Ξ'} (there a) with Any/insert a
  ... | inj₁ x₁ = inj₁ x₁
  ... | inj₂ y = inj₂ (there y)

  Any/swap : ∀ {Ξ : Vec Behav ξ} {G : Behav} {ξ'} {Ξ' : Vec Behav ξ'}
             {G' G'' : Behav} (x₂ : Any (_~_ G') (Ξ' ++ G'' ∷ G ∷ Ξ)) →
           Any (_~_ G') (Ξ' ++ G ∷ G'' ∷ Ξ)
  Any/swap {Ξ' = []} (here px) = there (here px)
  Any/swap {Ξ' = []} (there (here px)) = here px
  Any/swap {Ξ' = []} (there (there x)) = there (there x)
  Any/swap {Ξ' = x₁ ∷ Ξ'} (here px) = here px
  Any/swap {Ξ' = x₁ ∷ Ξ'} (there x) = there (Any/swap x)

  Any/float : ∀ {Ξ : Vec Behav ξ} {G : Behav} {ξ'}
              {Ξ' : Vec Behav ξ'} {G' : Behav}
              (x₂ : Any (_~_ G') (Ξ' ++ G ∷ Ξ)) →
            Any (_~_ G') (G ∷ Ξ' ++ Ξ)
  Any/float {Ξ' = []} x = x
  Any/float {Ξ' = x₁ ∷ Ξ'} (here px) = there (here px)
  Any/float {Ξ' = x₁ ∷ Ξ'} (there x)
    = Any/swap {Ξ' = []} (there (Any/float {Ξ' = Ξ'} x))

  -- a session is well typed if all its participants follow the global type
  ⊢s_∶_ : (M : Session) -> (G : Behav) -> Set
  ⊢s M ∶ G = (P : Part) -> [] & [] & [] / G ↑ P ⊢p< ng > (M [ P ]s)

  swap/visited : ∀ {Γ : Vec Sort γ} {Δ : Vec Behav δ}
                 {Ξ : Vec Behav ξ} {G : Behav} {P : Part} {g} {Pr : Proc γ δ} {ξ'}
                 {Ξ' : Vec Behav ξ'} {G' G'' : Behav} →
               Γ & Δ & Ξ' ++ G'' ∷ G ∷ Ξ / G' ↑ P ⊢p< g > Pr →
               Γ & Δ & Ξ' ++ G ∷ G'' ∷ Ξ / G' ↑ P ⊢p< g > Pr
  swap/visited (t/send gr etd td) = t/send gr etd td
  swap/visited (t/recv x conts) = t/recv x conts
  swap/visited (t/if etd td td₁) = t/if etd td td₁
  swap/visited (t/rec x td) = t/rec x td
  swap/visited (t/var x x₁) = t/var x x₁
  swap/visited (t/end x) = t/end x
  swap/visited {Ξ' = Ξ'} (t/skip-next sk ktd)
    = t/skip-next sk (swap/visited {Ξ' = _ ∷ Ξ'} ∘ ktd)
  swap/visited (t/skip-close sk x₂) = t/skip-close sk (Any/swap x₂)

  float/visited : ∀ {Γ : Vec Sort γ} {Δ : Vec Behav δ}
                 {Ξ : Vec Behav ξ} {G : Behav} {P : Part} {g} {Pr : Proc γ δ} {ξ'}
                 {Ξ' : Vec Behav ξ'} {G' : Behav} →
               Γ & Δ & Ξ' ++ G ∷ Ξ / G' ↑ P ⊢p< g > Pr →
               Γ & Δ & G ∷ Ξ' ++ Ξ / G' ↑ P ⊢p< g > Pr
  float/visited (t/send gr etd td) = t/send gr etd td
  float/visited (t/recv x conts) = t/recv x conts
  float/visited (t/if etd td td₁) = t/if etd td td₁
  float/visited (t/rec x td) = t/rec x td
  float/visited (t/var x x₁) = t/var x x₁
  float/visited (t/end x) = t/end x
  float/visited {Ξ' = Ξ} (t/skip-next sk ktd)
    = t/skip-next sk (swap/visited {Ξ' = []} ∘ float/visited {Ξ' = _ ∷ Ξ} ∘ ktd)
  float/visited (t/skip-close sk x₂)
    = t/skip-close sk (Any/float x₂)

  str/Any : ∀ {Ξ : Vec Behav ξ} {G : Behav} {ξ'} {Ξ' : Vec Behav ξ'}
            (x₂ : Any (_~_ G) Ξ) →
          Any (_~_ G) (Ξ' ++ Ξ)
  str/Any {Ξ' = []} x₂ = x₂
  str/Any {Ξ' = x ∷ Ξ'} x₂ = there (str/Any x₂)

  strengthen/visited : ∀ {Γ : Vec Sort γ} {Δ : Vec Behav δ}
                 {Ξ : Vec Behav ξ} {G : Behav} {P : Part} {g} {Pr : Proc γ δ}
                 {ξ'} →
               (Ξ' : Vec Behav ξ') →
               Γ & Δ & Ξ / G ↑ P ⊢p< g > Pr →
               Γ & Δ & Ξ' ++ Ξ / G ↑ P ⊢p< g > Pr
  strengthen/visited Ξ' (t/send gr etd td) = t/send gr etd td
  strengthen/visited Ξ' (t/recv x conts) = t/recv x conts
  strengthen/visited Ξ' (t/if etd td td₁) = t/if etd td td₁
  strengthen/visited Ξ' (t/rec x td) = t/rec x td
  strengthen/visited Ξ' (t/var x x₁) = t/var x x₁
  strengthen/visited Ξ' (t/end x) = t/end x
  strengthen/visited Ξ' (t/skip-next sk ktd)
    = t/skip-next sk (float/visited ∘ strengthen/visited Ξ' ∘ ktd)
  strengthen/visited Ξ' (t/skip-close sk x₂)
    = t/skip-close sk (str/Any x₂)

  unfold/tskip : ∀ {Γ : Vec Sort γ} {Δ : Vec Behav δ}
                 {Ξ : Vec Behav ξ} {G : Behav} {P : Part} {g} {Pr : Proc γ δ}
                 {ξ'} {G' : Behav} →
               (Ξ' : Vec Behav ξ') →
               Γ & Δ & Ξ / G ↑ P ⊢p< g > Pr →
               Γ & Δ & Ξ' ++ G ∷ Ξ / G' ↑ P ⊢p< g > Pr →
               Γ & Δ & Ξ' ++ Ξ / G' ↑ P ⊢p< g > Pr
  unfold/tskip Ξ' otd (t/send gr etd td) = t/send gr etd td
  unfold/tskip Ξ' otd (t/recv x conts) = t/recv x conts
  unfold/tskip Ξ' otd (t/if etd td td₁) = t/if etd td td₁
  unfold/tskip Ξ' otd (t/rec x td) = t/rec x td
  unfold/tskip Ξ' otd (t/var x x₁) = t/var x x₁
  unfold/tskip Ξ' otd (t/end x) = t/end x
  unfold/tskip Ξ' otd (t/skip-next sk ktd)
    = t/skip-next sk (unfold/tskip (_ ∷ Ξ') otd ∘ ktd)
  unfold/tskip Ξ' otd (t/skip-close sk x₂) with Any/insert x₂
  ... | inj₁ x₃ = t/bisim (~sym x₃) (strengthen/visited Ξ' otd)
  ... | inj₂ y = t/skip-close sk y

  unrelated/step : ∀{Γ : Vec Sort γ}{Δ : Vec Behav δ}{G P g Pr}
    → (td : Γ & Δ & [] / G  ↑ P ⊢p< g > Pr)
    → ∀ {α G'} → (rt : G -< α >-> G')
    → (nS : P ∉α α)
    -----------------------------------------------------------------------
    → Γ & Δ & [] / G' ↑ P ⊢p< g > Pr
  unrelated/step (t/send gr etd td) rt nS =
    let _ , (rt' , rt'') = diamond rt gr (send-act-indep rt gr nS)
    in t/send rt' etd (unrelated/step td rt'' nS)
  unrelated/step (t/recv {P = P} rt K){α = α} gr nS
    with P ≟f receiver α
  ... | yes refl rewrite recv-act-eq gr rt (∈S refl) = ⊥-elim (nS (∈R refl))
  ... | no ¬eq with recv-act-indep rt gr nS ¬eq
  ... | ii = t/recv (◇-r rt gr ii) λ {i = i} x →
    let _ , rX = cond-comm ii gr rt x
        dd = ◇-r rX gr ii
        rw = step-det (◇-r rX gr ii) x
    in unrelated/step (K rX) (subst (_ -< _ >->_) rw (◇-l rX gr ii)) nS
  unrelated/step (t/if etd td td₁) rt nS =
    t/if etd (unrelated/step td rt nS) (unrelated/step td₁ rt nS)
  unrelated/step (t/end p∉g) rt nS = t/end (∉B-step rt p∉g)
  unrelated/step (t/rec gr td) rt nS
    = t/rec (rt/trans gr (rt , nS)) td
  unrelated/step (t/var b gr) rt nS
    = t/var b (tr/cat gr ([ rt , nS ]► (■ , tt)))
  unrelated/step (t/skip-next sk ktd) rt nS
    = unfold/tskip [] (t/skip-next sk ktd) (ktd rt)
  unrelated/step (t/skip-close sk ()) rt nS

  unrelated/trace : ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{G P g Pr}
    → (td : Γ & Δ & [] / G  ↑ P ⊢p< g > Pr)
    → ∀ {G'} → (rt : G =<¬ P >=> G')
    -----------------------------------------------------------------------
    → Γ & Δ & [] / G' ↑ P ⊢p< g > Pr
  unrelated/trace td (■ , P∉tr) = td
  unrelated/trace td ((x ► tr) , P∉x , P∉tr)
    = unrelated/trace (unrelated/step td x P∉x) (tr , P∉tr)

  unrelated/skippable/trace : ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{G P g Pr}
    → (td : Γ & Δ & [] / G  ↑ P ⊢p< g > Pr)
    → ∀ {G'} → (rt : G ~< P >~> G')
    -----------------------------------------------------------------------
    → Γ & Δ & [] / G' ↑ P ⊢p< g > Pr
  unrelated/skippable/trace td (■ , P∉tr) = td
  unrelated/skippable/trace td ((x ► tr) , P∉x , P∉tr)
    = unrelated/skippable/trace (unrelated/step td x λ z → P∉x (∈-tr x z)) (tr , P∉tr)

  t/> : ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{Ξ : Vec Behav ξ} {G P Pr}
    -> Γ & Δ & Ξ / G ↑ P ⊢p< mg > Pr
    -> Γ & Δ & Ξ / G ↑ P ⊢p< ng > Pr
  t/> (t/send gr x etd) = t/send gr x etd
  t/> (t/recv x conts) = t/recv x conts
  t/> (t/skip-next sk conts) = t/skip-next sk (t/> ∘ conts)
  t/> (t/skip-close sk d) = t/skip-close sk d
  t/> (t/if etd x x₁) = t/if etd (t/> x) (t/> x₁)

module MPST-Extra {N : ℕ}{B : BTheory N}(BP : BT-Prop B)(BE : BT-Extra B) where -- N is the number of participants in the session
  open import Relation.Nullary using (True; False; fromWitness; toWitness; toWitnessFalse; fromWitnessFalse)

  open MPST BP
  open BT-Extra BE

  is-comm? : ∀ {δ γ} Q (Pr : Proc δ γ) → Dec (is-comm Q Pr)
  is-comm? Q (x ! x₁ < x₂ >∙ Pr) with x ≟f Q
  ... | yes refl = yes is-send
  ... | no ¬p = no (λ{ MPST.is-send → ¬p refl })
  is-comm? Q (Σ x ？[ x₁ ]· x₂) with x ≟f Q
  ... | yes refl = yes is-recv
  ... | no ¬p = no (λ{ MPST.is-recv → ¬p refl })
  is-comm? Q (ifp x then Pr else Pr₁) = no λ ()
  is-comm? Q (rec Pr) = no λ ()
  is-comm? Q (v x) = no λ ()
  is-comm? Q ∅ = no λ ()

  ∃is-comm? : ∀ {δ γ} (Pr : Proc δ γ) → Dec (∃[ Q ] is-comm Q Pr)
  ∃is-comm? (Q ! _ < _ >∙ _) = yes (Q , is-send)
  ∃is-comm? (Σ Q ？[ _ ]· _) = yes (Q , is-recv)
  ∃is-comm? (ifp x then pr else pr₁) = no (λ ())
  ∃is-comm? (rec pr) = no (λ ())
  ∃is-comm? (v x) = no (λ ())
  ∃is-comm? ∅ = no (λ ())

  open _∈tr_
  non-act? : ∀ P G → Dec (∀ {α G'} → G -< α >-> G' → P ∉α α)
  non-act? P G with can-step? P G
  ... | yes pr = no (λ z → z (∈-step pr) (∈-prf pr))
  ... | no ¬pr = yes (λ z → ¬pr ∘ ∈-tr z)

  -- TODO: come up with good helper for "skipping"
  -- t/skip : ∀ {γ δ ξ g P Pr G α G'}
  --   → {Γ : Vec Sort γ}{Δ : Vec Behav δ}{Ξ : Vec Behav ξ}
  --   → {ic : True (∃is-comm? Pr)}
  --   → (gr : G -< α >-> G')
  --   → {na : True (non-act? P G)}
  --   → (ktd : ∀ {G' α} → G -< α >-> G' → Γ & Δ & G ∷ Ξ / G' ↑ P ⊢p< g > Pr)
  --   → Γ & Δ & Ξ / G ↑ P ⊢p< g > Pr
  -- t/skip {ic = ic} gr {na = na} ktd
  --   = t/skip-next [ toWitness ic .proj₂ & gr & toWitness na ] ktd
