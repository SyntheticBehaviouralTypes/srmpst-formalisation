{-# OPTIONS --guardedness #-}
open import Level using (Level) renaming (suc to lsuc)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤ ; tt)
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Fin hiding (_+_ ; _-_) renaming (_≟_ to _≟f_)
open import Data.Vec hiding ([_]) renaming (lookup to lu; removeAt to _-_)
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
      γ δ : ℕ

  open import Definitions.Common (N) public
  open import Definitions.Proc (N) public
  open Subst
  open import Definitions.Actions (N) public
  open HeadAct

  data is-comm {γ δ} : Part → Proc γ δ → Set where
    is-send : ∀ {Q ℓ E Pr} → is-comm Q (Q ! ℓ < E >∙ Pr)
    is-recv : ∀ {Q I}{S : Vec Sort (suc I)}{B} → is-comm Q (Σ Q ？[ S ]· B)

  still-active : Behav → Part → Set
  still-active G P = ∀ {G′} → G =<¬ P >=> G′ → ∃[ G″ ] G′ ~< P >~> G″

  sa~ : ∀ {G G′ P} → G ~ G′ → still-active G P → still-active G′ P
  sa~ {P = P} b a tr with a (~⇒trace (~sym b) tr)
  ... | G″ , trα = _ , (~>~→ (~sym (~⇒~ (~sym b) tr)) trα)

  Causal : Behav → Part → Part → Set
  Causal G P Q
    = ∀ {G′} → G =<¬ P >=> G′ → P ∉tr G′ → ∀{G″} → ¬ G′ ~< P ∧ Q >~> G″

  ntac-step : ∀{G G′ P Q} → G =<¬ P >=> G′
    → Causal G P Q → Causal G′ P Q
  ntac-step tr f tr′ g = f (tr/cat tr tr′) g

  record must-skip (G : Behav) (P Q : Part) : Set where
    constructor SK[_,_,_]
    field
      ms-sound : Causal G P Q
      ms-noact : P ∉tr G
      ms-activ : still-active G P

  thin-air/~ : ∀{G G' P Q}
    → G ~ G' → Causal G P Q → Causal G' P Q
  thin-air/~ {P = P} b f tr g trPQ
    = f (~⇒trace (~sym b) tr) (∉tr~ (~⇒~ (~sym b) tr) g)
        (itrace~ (~⇒~ (~sym b) tr) trPQ .proj₂ .proj₁)

  open _~_
  must-skip/~ : ∀{G G' P Q}
    → G ~ G' → must-skip G P Q → must-skip G' P Q
  must-skip/~ {P = P}{Q = Q} b SK[ f , g , a ]
    = SK[ thin-air/~ {P = P} {Q = Q} b f
        , g ∘ ∈tr~ (~sym b)
        , sa~ b a
        ]

  data _&_/_↑_⊢p<_>_
    (Γ : Vec Sort γ)
    (Δ : Vec Behav δ)
    (G : Behav) : Part → (g : Guard) -> Proc γ δ -> Set where
    t/send : ∀{g α G'}{Pr : Proc γ δ}{E : Exp γ} ->
      (gr : G -< α >-> G') ->
      (etd : Γ ⊢e E ∶ α/sort α) ->
      (td : Γ & Δ / G' ↑ sender α ⊢p< ng > Pr) ->
      Γ & Δ / G ↑ sender α ⊢p< g > (receiver α ! label α < E >∙ Pr)

    t/recv : ∀{g p Br} ->
      p [R] G ->
      (conts : ∀ {i G'}
        -> G -< p , i >-> G'
        -> (α/sort (p , i) ∷ Γ) & Δ / G' ↑ preceiver p ⊢p< ng > (lu Br i)) ->
      Γ & Δ / G ↑ preceiver p ⊢p< g > (Σ psender p ？[ sorts p ]· Br)

    t/skip : ∀ {g P Q Pr} ->
      is-comm Q Pr →
      must-skip G P Q →
      (conts : ∀ {G'} → G ~< P >~> G' → Γ & Δ / G' ↑ P ⊢p< g > Pr) ->
      Γ & Δ / G ↑ P ⊢p< g > Pr

    t/if : ∀{P E Pr Pr' g} ->
      (etd : Γ ⊢e E ∶ s/bool) ->
      (ttd : Γ & Δ / G ↑ P ⊢p< g > Pr) -> (ftd : Γ & Δ / G ↑ P ⊢p< g > Pr') ->
      Γ & Δ / G ↑ P ⊢p< g > (ifp E then Pr else Pr')

    t/rec : ∀{P Pr Gr} →
      Gr =<¬ P >=>ᵣ G →
      Γ & (Gr ∷ Δ) / Gr ↑ P ⊢p< mg > Pr →
      Γ & Δ / G ↑ P ⊢p< ng > rec Pr

    t/var : ∀{P X Gr} ->
      Gr ~ lu Δ X →
      Gr =<¬ P >=> G →
      Γ & Δ / G ↑ P ⊢p< ng > v X

    t/end :
      ∀ {P} → ¬ (P ∈T G) ->
      Γ & Δ / G ↑ P ⊢p< ng > ∅

  data _~~_ : ∀ {δ} → Vec Behav δ → Vec Behav δ → Set where
    ~~-cons : ∀ {G G' δ} {Δ Δ' : Vec Behav δ}
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

  t/Δ/bisim : ∀ {G P g γ δ}{Γ : Vec Sort γ}{Pr : Proc γ δ}{Δ Δ' : Vec Behav δ} →
    Δ ~~ Δ' →
    Γ & Δ  / G ↑ P ⊢p< g > Pr →
    Γ & Δ' / G ↑ P ⊢p< g > Pr
  t/Δ/bisim x (t/send gr etd y) = t/send gr etd (t/Δ/bisim x y)
  t/Δ/bisim x (t/recv cr conts) =
    t/recv cr λ gr → t/Δ/bisim x (conts gr)
  t/Δ/bisim x (t/skip y p conts) = t/skip y p λ gr → t/Δ/bisim x (conts gr)
  t/Δ/bisim x (t/if etd y y₁) = t/if etd (t/Δ/bisim x y) (t/Δ/bisim x y₁)
  t/Δ/bisim x (t/rec gr y) = t/rec gr (t/Δ/bisim (~~-cons ~refl x) y)
  t/Δ/bisim x (t/var y gr) = t/var (t/lu/bisim x _ y) gr
  t/Δ/bisim x (t/end p∉g) = t/end p∉g

  t/bisim : ∀ {Γ : Vec Sort γ}{Δ : Vec Behav δ}{G G' P Pr g} →
    G ~ G' →
    Γ & Δ / G  ↑ P ⊢p< g > Pr ->
    Γ & Δ / G' ↑ P ⊢p< g > Pr
  t/bisim x (t/send gr etd x₁) =
    let _ , gr' , bn = ~L x gr
    in t/send gr' etd (t/bisim bn x₁)
  t/bisim x (t/recv R[ rt ] conts) =
    let _ , rt' , _ = ~L x rt
    in t/recv R[ rt' ] (λ gr →
         let _ , gr' , bn = ~R x gr
         in t/bisim bn (conts gr'))
  t/bisim x (t/skip ic p conts) =
    t/skip ic (must-skip/~ x p)
         λ gr → let _ , gr' , bn = ~>~ (~sym x) gr
                in t/bisim (~sym bn) (conts gr')
  t/bisim x (t/if etd x₁ x₂) =
    t/if etd (t/bisim x x₁) (t/bisim x x₂)
  t/bisim x (t/rec gr x₁) =
    let Gr' , x' , gr' = ~traceback x gr
    in t/rec gr' (t/Δ/bisim (~~-cons x' ~~-refl) (t/bisim x' x₁))
  t/bisim x (t/var x₁ gr)
    = let _ , bb , gr' = ~traceback/l x gr
      in t/var (~trans (~sym bb) x₁) gr'
  t/bisim x (t/end p∉g) = t/end (contraposition (∈~ (~sym x)) p∉g)

  -- a session is well typed if all its participants follow the global type
  ⊢s_∶_ : (M : Session) -> (G : Behav) -> Set
  ⊢s M ∶ G = (P : Part) -> [] & [] / G ↑ P ⊢p< ng > (M [ P ]s)

  t/> : ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ} {G P Pr}
    -> Γ & Δ / G ↑ P ⊢p< mg > Pr
    -> Γ & Δ / G ↑ P ⊢p< ng > Pr
  t/> (t/send gr x etd) = t/send gr x etd
  t/> (t/recv x conts) = t/recv x conts
  t/> (t/skip x x₃ conts) = t/skip x x₃ λ x₃ → t/> (conts x₃)
  t/> (t/if etd x x₁) = t/if etd (t/> x) (t/> x₁)


  unrelated/step : ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{G P g Pr}
    → (td : Γ & Δ / G  ↑ P ⊢p< g > Pr)
    → ∀ {α G'} → (rt : G -< α >-> G')
    → (nS : P ∉α α)
    -----------------------------------------------------------------------
    → Γ & Δ / G' ↑ P ⊢p< g > Pr
  unrelated/step (t/send gr etd td) rt nS =
    let _ , (rt' , rt'') = diamond rt gr (send-act-indep rt gr nS)
    in t/send rt' etd (unrelated/step td rt'' nS)
  unrelated/step (t/recv {p = p} (R[ rt ]) K){α = α} gr nS
    with psender p ≟f receiver α
  ... | yes refl rewrite recv-act-eq gr rt (∈S refl) = ⊥-elim (nS (∈R refl))
  ... | no ¬eq with recv-act-indep rt gr nS ¬eq
  ... | ii = t/recv R[ ◇-r rt gr ii ] λ {i = i} x →
    let _ , rX = cond-comm ii gr rt x
        dd = ◇-r rX gr ii
        rw = step-det (◇-r rX gr ii) x
    in unrelated/step (K rX) (subst (λ X → _ -< _ >-> X) rw (◇-l rX gr ii)) nS
  unrelated/step (t/skip rt SK[ p , f , a ] K) {α = α} gr nS
    with a ((gr ► ■ , nS , tt))
  ... | _ , ■ , sk = K (gr ► ■ , f , sk)
  ... | _ , (x ► tr) , skₓ , skₜ
    = t/skip rt SK[ (λ x₁ x₂ x₃ → p ([ gr , nS ]► x₁) x₂ x₃) , skₓ
                  , a ∘ [ gr , nS ]► ] (K ∘ [ gr , f ]►)
  unrelated/step (t/if etd td td₁) rt nS =
    t/if etd (unrelated/step td rt nS) (unrelated/step td₁ rt nS)
  unrelated/step (t/end p∉g) rt nS = t/end (∉B-step rt p∉g)
  unrelated/step (t/rec gr td) rt nS
    = t/rec (rt/trans gr (rt , nS)) td
  unrelated/step (t/var b gr) rt nS
    = t/var b (tr/cat gr ([ rt , nS ]► (■ , tt)))

  unrelated/trace : ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{G P g Pr}
    → (td : Γ & Δ / G  ↑ P ⊢p< g > Pr)
    → ∀ {G'} → (rt : G =<¬ P >=> G')
    -----------------------------------------------------------------------
    → Γ & Δ / G' ↑ P ⊢p< g > Pr
  unrelated/trace td (■ , P∉tr) = td
  unrelated/trace td ((x ► tr) , P∉x , P∉tr)
    = unrelated/trace (unrelated/step td x P∉x) (tr , P∉tr)


module MPST-Extra {N : ℕ}{B : BTheory N}(BP : BT-Prop B)(BE : BT-Extra B) where -- N is the number of participants in the session
  open import Relation.Nullary using (True; False; fromWitness; toWitness; toWitnessFalse; fromWitnessFalse)

  open MPST BP
  open BT-Extra BE

  record SkippableTrace P B : Set where
    pattern
    constructor SKT
    field
      {skip-B} : Behav
      skip-Tr : B ~~> skip-B
      skip-P : True (skippable? P skip-Tr)

  pattern Active x = SKT x tt

  from-SKT : ∀ {P B} → SkippableTrace P B → ∃[ B′ ] B ~< P >~> B′
  from-SKT x .proj₁ = SkippableTrace.skip-B x
  from-SKT x .proj₂
    = SkippableTrace.skip-Tr x , toWitness (SkippableTrace.skip-P x)

  Causal? : Behav → Part → Part → Set
  Causal? G P Q
    = ∀ {G′} → (tr : G ~~> G′)
        → (U : True (unrelated? P tr)) → (P∉G′ : False (can-step? P G′))
        → ∀{G″} → (tr' : G′ ~~> G″)
        → True (skippable? P tr')
        → True (skippable? Q tr') → ⊥

  causal? : ∀{B P Q} → Causal? B P Q → Causal B P Q
  causal? f (tr , Ptr) x₁ (tr' , Ptr' , Qtr')
    = f tr (fromWitness Ptr) (fromWitnessFalse x₁) tr'
        (fromWitness Ptr') (fromWitness Qtr')

  Active? : Behav → Part → Set
  Active? B P =
    ∀ {B′} → (tr : B ~~> B′) → (True (unrelated? P tr))
         → SkippableTrace P B′

  active? : ∀{B} P
    → Active? B P
    → still-active B P
  active? P f (tr , Ptr) = from-SKT (f tr (fromWitness Ptr))

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

  dt/skip : ∀ {γ δ G g P} Q {Pr}{Γ : Vec Sort γ}{Δ : Vec Behav δ} ->
      {ic : True (is-comm? Q Pr)} →
      Causal? G P Q →
      {no-step : False (can-step? P G)} →
      Active? G P →
      (conts : ∀ {G'} (tr : G ~~> G') → {sk : True (skippable? P tr)}
        → Γ & Δ / G' ↑ P ⊢p< g > Pr) →
      Γ & Δ / G ↑ P ⊢p< g > Pr
  dt/skip {P = P} Q {ic = x} c {no-step = ns} a conts
    = t/skip (toWitness x) SK[ causal? c , toWitnessFalse ns , active? P a ]
      λ (x₂ , x₃) → conts x₂ {sk = fromWitness x₃}
