{-# OPTIONS --guardedness #-}
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤ ; tt)
open import Data.Fin using (Fin; zero; suc)
  renaming (_≟_ to _≟f_)
open import Data.Nat using (ℕ ; zero; suc)
  renaming (_+_ to _+ℕ_)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec ; []; _∷_; lookup ; map; tabulate; _[_]≔_)
open import Data.Vec.Properties using (lookup-map; lookup∘update;
  lookup∘update′; lookup∘tabulate)
open import Function  using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong;
  cong₂; sym; subst; ≢-sym)
open import Relation.Nullary using (Dec; ¬_; ¬?; yes; no; contraposition)

open import Definitions.Guard
open import Definitions.Expr

module Definitions.Behav where

  import Definitions.Common
  import Definitions.Actions

  record BTheory (N : ℕ) : Set₁ where
    open Definitions.Common(N)
    open Definitions.Actions(N)
    field
      Behav : Set
      _-<_>->_ : Behav → Action → Behav → Set

    record _[R]_ (α : HeadAct) (G : Behav) : Set where
      constructor R[_]
      field
        {nextG} : Behav
        {someI} : choice α
        rdyTr : G -< α , someI >-> nextG

    _-<_∣_>->_ : Behav → Action → (Action → Set) → Behav → Set
    G -< α ∣ P >-> G' = (G -< α >-> G') × P α

    _-<_∌_>->_ : Behav → Action → Part → Behav → Set
    G -< α ∌ P >-> G' = G -< α ∣ P ∉α_ >-> G'

    _-<_∥i_>->_ : Behav → Action → Action → Behav → Set
    G -< α ∥i α' >-> G' = G -< α ∣ _∥ α' >-> G'

    _-<_∋_>->_ : Behav → Action → Part → Behav → Set
    G -< α ∋ P >-> G' = G -< α ∣ P ∈α_ >-> G'

    data _=[_]=>ᵣ_ (G : Behav) (ϕ : Action → Set) : Behav → Set where
      rt/refl : G =[ ϕ ]=>ᵣ G
      rt/trans : ∀{α Gi Gf} → G =[ ϕ ]=>ᵣ Gi → Gi -< α ∣ ϕ >-> Gf → G =[ ϕ ]=>ᵣ Gf

    rt/trans' : ∀{G α Gi Gf ϕ}
      → G -< α ∣ ϕ >-> Gi → Gi =[ ϕ ]=>ᵣ Gf → G =[ ϕ ]=>ᵣ Gf
    rt/trans' x rt/refl = rt/trans rt/refl x
    rt/trans' x (rt/trans tr x₁) = rt/trans (rt/trans' x tr) x₁

    rt/cat : ∀{G Gi Gf P} → G =[ P ]=>ᵣ Gi → Gi =[ P ]=>ᵣ Gf → G =[ P ]=>ᵣ Gf
    rt/cat tr rt/refl = tr
    rt/cat tr (rt/trans tr' x) = rt/trans (rt/cat tr tr') x

    _=<¬_>=>ᵣ_ : Behav → Part → Behav → Set
    G =<¬ P >=>ᵣ G' = G =[ P ∉α_ ]=>ᵣ G'

    weaken : ∀ {G P Q G'} → (∀ p → P p → Q p) → G =[ P ]=>ᵣ G' → G =[ Q ]=>ᵣ G'
    weaken f rt/refl = rt/refl
    weaken f (rt/trans x y) = rt/trans (weaken f x) (y .proj₁ , f _ (y .proj₂))

    record _∈tr_ (P : Part) (G : Behav) : Set where
      pattern
      constructor ∈-tr
      field
        {∈-G′} : Behav
        {∈-α}  : Action
        ∈-step : G -< ∈-α >-> ∈-G′
        ∈-prf : P ∈α ∈-α

    _∉tr_ : Part → Behav → Set
    P ∉tr G = ¬ (P ∈tr G)

    data _~~>_ : Behav → Behav → Set where
      ■ : ∀ {G} → G ~~> G
      _►_ : ∀ {G α G′ G″} → G -< α >-> G′ → G′ ~~> G″ → G ~~> G″

    infixr 5 _►_

    until : ∀ {G G′} → G ~~> G′
      → (φ : (G : Behav) → (α : Action) → Set) → (ψ : Set) →  Set
    until ■ φ ψ = ψ
    until (_►_ {G = G} {α = α} x tr) φ ψ = φ G α × until tr φ ψ

    _=[_]=>_ : ∀ (G : Behav) (φ : Action → Set) (G′ : Behav) → Set
    G =[ φ ]=> G′ = Σ[ tr ∈ G ~~> G′ ] until tr (λ _ α → φ α) ⊤

    skippable : ∀ {G G'} → Part → G ~~> G' → Set
    skippable {G' = G} P tr = until tr (λ G _ → P ∉tr G) (P ∈tr G)

    _~<_>~>_ : Behav → Part → Behav → Set
    G ~< P >~> G' = Σ[ tr ∈ G ~~> G' ] skippable P tr --  × causal tr

    _~<_∧_>~>_ : Behav → Part → Part → Behav → Set
    G ~< P ∧ Q >~> G' = Σ[ tr ∈ G ~~> G' ] skippable P tr × skippable Q tr --  × causal tr

    [_,_]► : ∀ {G α G′ G″ φ ψ}
      → G -< α >-> G′ → φ G α
      → Σ[ tr ∈ G′ ~~> G″ ] until tr φ ψ
      → Σ[ tr ∈ G ~~> G″ ] until tr φ ψ
    [ gr , P∉G ]► (tr , P∉tr) = (gr ► tr , (P∉G , P∉tr ))

    open _∈tr_
    ~>α : ∀ {G P G′} → G ~< P >~> G′ → Action
    ~>α (■ , ∈G) = ∈-α ∈G
    ~>α ((x ► tr) , (_ , sk)) = ~>α (tr , sk)

    ~>G : ∀ {G P G′} → G ~< P >~> G′ → Behav
    ~>G (■ , ∈G) = ∈-G′ ∈G
    ~>G ((x ► tr) , (_ , sk)) = ~>G (tr , sk)

    ~> : ∀ {G P G′} → (rt : G ~< P >~> G′) → G′ -< ~>α rt ∋ P >-> ~>G rt
    ~> (■ , ∈G) = ∈-step ∈G , ∈-prf ∈G
    ~> ((x ► fst) , (_ , sk)) = ~> (fst , sk)

    tr/cat : ∀{G Gi Gf P} → G =[ P ]=> Gi → Gi =[ P ]=> Gf → G =[ P ]=> Gf
    tr/cat (■ , tt)            tr = tr
    tr/cat (gr ► tr′ , φα , φ) tr = let (tr″ , φ') = tr/cat (tr′ , φ) tr
                                    in (gr ► tr″) , φα , φ'

    _=<¬_>=>_ : Behav → Part → Behav → Set
    G =<¬ P >=> G' = G =[ P ∉α_ ]=> G'

    _===>_ : Behav → Behav → Set
    G ===> G' = G =[ (λ _ → ⊤) ]=> G'

    _=<∥_>=>_ : Behav → Action → Behav → Set
    G =<∥ α >=> G' = G =[ _∥ α ]=> G'

    tr/first : ∀ {G P G'} → G ~< P >~> G' →  ∃[ α ] ∃[ G'' ] G -< α >-> G''
    tr/first (■ , ∈-tr sk _) = _ , _ , sk
    tr/first ((x ► tr) , sk , c) = _ , _ , x

    data _∈T_ P : Behav → Set where
      in/α : ∀ {G G′ α} → G -< α >-> G′ → P ∈α α → P ∈T G
      in/later : ∀ {G G′ α} → G -< α >-> G′ → P ∈T G′ → P ∈T G

    in/send : ∀{G α G'} (st : G -< α >-> G') → sender α ∈T G
    in/send st = in/α st (∈S refl)

    in/recv : ∀{G α G'} (st : G -< α >-> G') → receiver α ∈T G
    in/recv st = in/α st (∈R refl)

    ended : Behav → Set
    ended B = ∀ (P : Part) → ¬ (P ∈T B)

    _∉T_ : Part → Behav → Set
    P ∉T G = ¬ (P ∈T G)

    record _~_ (G G′ : Behav) : Set where
      coinductive
      field
        ~L : ∀ {α G″} → G  -< α >-> G″ → ∃[ G‴ ] G′ -< α >-> G‴ × G″ ~ G‴
        ~R : ∀ {α G‴} → G′ -< α >-> G‴ → ∃[ G″ ] G  -< α >-> G″ × G″ ~ G‴

    open _~_
    ~refl : ∀ {G} → G ~ G
    ~L ~refl x = _ , x , ~refl
    ~R ~refl x = _ , x , ~refl

    ~sym : ∀ {G₁ G₂} → G₁ ~ G₂ → G₂ ~ G₁
    ~sym x .~L x₁ = let _ , tr , b = ~R x x₁ in  _ , tr , ~sym b
    ~sym x .~R x₁ = let _ , tr , b = ~L x x₁ in  _ , tr , ~sym b

    ~trans : ∀ {G₁ G₂ G₃} → G₁ ~ G₂ → G₂ ~ G₃ → G₁ ~ G₃
    ~trans x y .~L z
      = let _ , nT , nB = ~L x z
            _ , tr , b = ~L y nT
        in _ , tr , ~trans nB b
    ~trans x y .~R z
      = let _ , nT , nB = ~R y z
            _ , tr , b = ~R x nT
        in _ , tr , ~trans b nB

    ~L→G : ∀ {G₁ G₂ G₃ α} → G₁ ~ G₂ → G₁ -< α >-> G₃ → Behav
    ~L→G b gr = ~L b gr .proj₁

    ~L→ : ∀ {G₁ G₂ G₃ α} (b : G₁ ~ G₂) (r : G₁ -< α >-> G₃)
      → G₂ -< α >-> ~L→G b r
    ~L→ b gr = ~L b gr .proj₂ .proj₁

    ~L→~ : ∀ {G₁ G₂ G₃ α} (b : G₁ ~ G₂) (r : G₁ -< α >-> G₃) → G₃ ~ ~L→G b r
    ~L→~ b gr = ~L b gr .proj₂ .proj₂

    ~R→G : ∀ {G₁ G₂ G₃ α} → G₁ ~ G₂ → G₂ -< α >-> G₃ → Behav
    ~R→G b gr = ~R b gr .proj₁

    ~R→ : ∀ {G₁ G₂ G₃ α} (b : G₁ ~ G₂) (r : G₂ -< α >-> G₃)
      → G₁ -< α >-> ~R→G b r
    ~R→ b gr = ~R b gr .proj₂ .proj₁

    ~R→~ : ∀ {G₁ G₂ G₃ α} (b : G₁ ~ G₂) (r : G₂ -< α >-> G₃) → ~R→G b r ~ G₃
    ~R→~ b gr = ~R b gr .proj₂ .proj₂

    ~→ : ∀ {G₁ G₂ G₃ α P} (b : G₁ ~ G₂) (gr : G₁ -< α ∣ P >-> G₃)
      → G₂ -< α ∣ P >-> ~L→G b (gr .proj₁)
    ~→ b gr = ~L→ b (gr .proj₁) , gr .proj₂

    ~⇒ᵣ : ∀ {Gi Gi' Go Inv}  → Gi ~ Gi' → Gi =[ Inv ]=>ᵣ Go
      → ∃[ Go' ] (Gi' =[ Inv ]=>ᵣ Go') × (Go ~ Go')
    ~⇒ᵣ b rt/refl = _ , rt/refl , b
    ~⇒ᵣ b (rt/trans x gr)
      = let _ , x'  , b'  = ~⇒ᵣ b x
            _ , gr' , b'' = ~L b' (proj₁ gr)
        in _ , rt/trans x' (gr' , proj₂ gr) , b''

    ~⇒ᵣG : ∀ {Gi Gi' Go Inv}  → Gi ~ Gi' → Gi =[ Inv ]=>ᵣ Go → Behav
    ~⇒ᵣG b tr = proj₁ (~⇒ᵣ b tr)

    ~⇒ᵣtrace : ∀ {Gi Gi' Go Inv} (b : Gi ~ Gi') (tr : Gi =[ Inv ]=>ᵣ Go)
      → Gi' =[ Inv ]=>ᵣ ~⇒ᵣG b tr
    ~⇒ᵣtrace b tr = proj₁ (proj₂ (~⇒ᵣ b tr))

    ~⇒ᵣ~ : ∀ {Gi Gi' Go Inv} (b : Gi ~ Gi') (tr : Gi =[ Inv ]=>ᵣ Go)
      → Go ~ ~⇒ᵣG b tr
    ~⇒ᵣ~ b tr = proj₂ (proj₂ (~⇒ᵣ b tr))

    ~⇒ : ∀ {Gi Gi' Go Inv}  → Gi ~ Gi' → Gi =[ Inv ]=> Go
      → ∃[ Go' ] (Gi' =[ Inv ]=> Go') × (Go ~ Go')
    ~⇒ b (■ , p) = _ , (■ , p) , b
    ~⇒ b (gr ► x , p , px)
      = let _ , (x' , px')  , b'  = ~⇒ (~L→~ b gr) (x , px)
        in _ , (~L→ b gr ► x' , p , px') , b'

    ~⇒G : ∀ {Gi Gi' Go Inv}  → Gi ~ Gi' → Gi =[ Inv ]=> Go → Behav
    ~⇒G b tr = proj₁ (~⇒ b tr)

    ~⇒trace : ∀ {Gi Gi' Go Inv} (b : Gi ~ Gi') (tr : Gi =[ Inv ]=> Go)
      → Gi' =[ Inv ]=> ~⇒G b tr
    ~⇒trace b tr = proj₁ (proj₂ (~⇒ b tr))

    ~⇒~ : ∀ {Gi Gi' Go Inv} (b : Gi ~ Gi') (tr : Gi =[ Inv ]=> Go)
      → Go ~ ~⇒G b tr
    ~⇒~ b tr = proj₂ (proj₂ (~⇒ b tr))

    ∉tr~ : {G G' : Behav} {P : Part} (b : G ~ G') (y : P ∉tr G) → P ∉tr G'
    ∉tr~ b y (∈-tr x z) = y (∈-tr (~L→ (~sym b) x) z)

    ~~>~ : ∀ {Gi Gi' Go} → Gi ~ Gi' → Gi ~~> Go
      → ∃[ Go' ] (Gi' ~~> Go') × (Go ~ Go')
    ~~>~ b ■ = _ , ■ , b
    ~~>~ b (x ► tr) =
      _ , (~L→ b x ► ~~>~ (~L→~ b x) tr .proj₂ .proj₁)
        , ~~>~ (~L→~ b x) tr .proj₂ .proj₂

    ∈tr~ : ∀ {Gi Gi' P} (b : Gi ~ Gi') (x : P ∈tr Gi) → P ∈tr Gi'
    ∈tr~ b (∈-tr ∈-step ∈-prf) = ∈-tr (~L→ b ∈-step) ∈-prf

    skippable~ : ∀ {Gi Gi' Go P} (b : Gi ~ Gi') (tr : Gi ~~> Go)
      → skippable P tr → skippable P (~~>~ b tr .proj₂ .proj₁)
    skippable~ b ■ P∈x = ∈tr~ b P∈x
    skippable~ b (x₁ ► tr) (x , y) = ∉tr~ b x , skippable~ (~L→~ b x₁) tr y

    ~>~ : ∀ {Gi Gi' Go P} → Gi ~ Gi' → Gi ~< P >~> Go
      → ∃[ Go' ] (Gi' ~< P >~> Go') × (Go ~ Go')
    ~>~ b (tr , sk)
      = _ , (~~>~ b tr .proj₂ .proj₁ , skippable~ b tr sk)
          , ~~>~ b tr .proj₂ .proj₂

    ~>~G : ∀ {Gi Gi' Go P} → Gi ~ Gi' → Gi ~< P >~> Go
      → Behav
    ~>~G b x = ~>~ b x .proj₁

    ~>~→ : ∀ {Gi Gi' Go P} (b : Gi ~ Gi') (x : Gi ~< P >~> Go)
      → Gi' ~< P >~> ~>~G b x
    ~>~→ b x = ~>~ b x .proj₂ .proj₁

    ~>~~ : ∀ {Gi Gi' Go P} (b : Gi ~ Gi') (x : Gi ~< P >~> Go) → Go ~ ~>~G b x
    ~>~~ b x = ~>~ b x .proj₂ .proj₂

    -- _=<¬_∧_>~>_ : Behav → Part → Part → Behav → Set
    -- G =<¬ P ∧ Q >~> G′
    --   = (G =[ (λ α → P ∉α α × Q ∉α α) ]=> G′)
    --   × ∃[ G″ ] ∃[ α ] (G′ -< α ∣ (λ α → P ∈α α × Q ∈α α) >-> G″)

    disj? : ∀ {G₁ G₂ G₃ G₄ α₁ α₂} → G₁ -< α₁ >-> G₂ → G₃ -< α₂ >-> G₄
      → Dec (proj₁ α₁ ⋏ proj₁ α₂)
    disj? {α₁ = α₁} {α₂ = α₂} _ _ = proj₁ α₁ ⋏? proj₁ α₂

    -- mk-itrace : ∀{G P Q G′} → G =[ (λ α → P ∉α α × Q ∉α α) ]=> G′
    --   → ∀ {G″ α} → P ∈α α → Q ∈α α → G′ -< α >-> G″ → G =<¬ P ∧ Q >~> G′
    -- mk-itrace x x₁ x₂ x₃ = x , _ , _ , x₃ , x₁ , x₂

    itrace-trans : ∀ {G P Q G′ G″ α} → G -< α >-> G′ → P ∉tr G → Q ∉tr G
      → G′ ~< P ∧ Q >~> G″ → G ~< P ∧ Q >~> G″
    itrace-trans gr p q (tr , φP , φQ) = gr ► tr , (p , φP) , q , φQ

    itrace~ : ∀ {G₁ G₁' G₂ P Q} → G₁ ~ G₁' → G₁ ~< P ∧ Q >~> G₂
      → ∃[ G₂' ] (G₁' ~< P ∧ Q >~> G₂') × (G₂ ~ G₂')
    itrace~ b (■ , φx , φy) = _ , (■ , ∈tr~ b φx , ∈tr~ b φy) , b
    itrace~ b ((x ► tr) , (φP , φPt) , (φQ , φQt))
      = let _ , (tr' , φP' , φQ') , b'  = itrace~ (~L→~ b x) (tr , φPt , φQt)
        in _ , ( ~L→ b x ► tr'
               , (φP ∘ ∈tr~ (~sym b) , φP')
               ,  φQ ∘ ∈tr~ (~sym b) , φQ')
             , b'

    ∈~ : ∀ {P G G'} (b : G ~ G') → P ∈T G → P ∈T G'
    ∈~ b (in/α x x₁) = in/α (~L→ b x) x₁
    ∈~ b (in/later x x₁) = in/later (~L→ b x) (∈~ (~L→~ b x) x₁)

    ∈-skip : ∀ {G P G'} → G =<¬ P >=> G' → P ∈T G' → P ∈T G
    ∈-skip (■ , snd) x₁ = x₁
    ∈-skip ((x ► tr) , _ , φ) x₁ = in/later x (∈-skip (tr , φ) x₁)

    ∈-last : ∀ {G P G'} → G ~< P >~> G' → P ∈T G
    ∈-last (■ , ∈-tr x sk) = in/α x sk
    ∈-last ((x ► tr) , (_ , sk))
      = in/later x (∈-last (tr , sk))

  record BT-Prop {N : ℕ}(B : BTheory N) : Set₁ where
    open Definitions.Common(N)
    open Definitions.Actions(N)
    open BTheory B
    field

      -- -- If a participant can appear in a trace, it must be in the specification,
      -- -- and viceversa.
      -- ∈T-∈B : ∀ {P G} → P ∈T G → P ∈B G
      -- ∈B-∈T : ∀ {P G} → P ∈B G → P ∈T G

      -- We need to be able to determine if two actions are independent or not.
      -- ATM (with our definition of Actions.agda), two actions are independent
      -- if they do not involve the same participants, and if they are not
      -- independent, they should have the same header. This may be too
      -- restrictive ...
      recv-act-eq : ∀ {G α α' G' G''} → G -< α >-> G' → G -< α' >-> G''
        → receiver α ∈α α' → proj₁ α ≡ proj₁ α'

      -- The sender cannot be the same as the receiver.
      -- Probably easy to generalise or remove.
      snd≢rcv : ∀{G G' α} → G -< α >-> G' → sender α ≢ receiver α

      -- Stepping with the same action leads to the same protocol state.
      step-det : ∀ {G α G' G''} → G -< α >-> G' → G -< α >-> G'' → G' ≡ G''

      -- If the protocol steps with an action to a state that has a bisimilar
      -- state, we must be able to construct a bisimilar protocol that
      -- transitions with this action to this bisimilar state.
      ~stepback : ∀ {α G0 G1 G1'}
        → G1 ~ G1' → G0 -< α >-> G1 → ∃[ G0' ] (G0 ~ G0') × (G0' -< α >-> G1')

      -- Diamond property.
      diamond : ∀ {G α G₁ α' G₂} → G -< α >-> G₁ → G -< α' >-> G₂
        → α ∥ α' → ∃[ G' ] (G₁ -< α' >-> G' × G₂ -< α >-> G')

      -- Conditional commutativity
      cond-comm : ∀ {hα i j α' G G' Gᵢ Gⱼ'} → hα ∥ₕ (proj₁ α')
        → G -< α' >-> G' → G -< hα , i >-> Gᵢ → G' -< hα , j >-> Gⱼ'
        → ∃[ Gⱼ ] G -< hα , j >-> Gⱼ

    send-act-indep : {G : Behav} {α α' : Action} {G' G'' : Behav} →
             G -< α >-> G' → G -< α' >-> G'' → sender α' ∉α α → α ∥ α'
    send-act-indep {_}{α}{α'} gr1 gr2 f with receiver α' ∈α? α
    send-act-indep {_}{α}{α'} gr1 gr2 f | yes pr with recv-act-eq gr2 gr1 pr
    ... | refl = ⊥-elim (f (∈S refl))
    send-act-indep {_}{α}{α'} gr1 gr2 f | no ¬pr
      = ii-disj λ{ (inj₁ (∈S refl)) → f (∈S refl)
                ; (inj₁ (∈R refl)) → ¬pr (∈S refl)
                ; (inj₂ (∈S refl)) → f (∈R refl)
                ; (inj₂ (∈R refl)) → ¬pr (∈R refl) }

    recv-act-indep : ∀ {G α α' G' G''} → G -< α >-> G' → G -< α' >-> G''
        → receiver α ∉α α' → sender α ≢ receiver α' → α ∥ α'
    recv-act-indep {α = α} {α' = α'} gr gr' R∉ S≢R
      with sender α ≟f sender α'
    ... | yes eq = ii-≡snd eq λ x → R∉ (∈R (sym x))
    ... | no ¬eq = ii-disj λ{ (inj₁ (∈S refl)) → ¬eq refl
                            ; (inj₁ (∈R refl)) → S≢R refl
                            ; (inj₂ x) → R∉ x }

    indep? : ∀ {G₁ G₂ G₃ α₁ α₂} → G₁ -< α₁ >-> G₂ → G₁ -< α₂ >-> G₃
      → (α₁ ∥ α₂) ⊎ (proj₁ α₁ ≡ proj₁ α₂)
    indep? {α₁ = α₁} {α₂ = α₂} x y with disj? x y
    ... | no ¬d = inj₁ (ii-disj ¬d)
    ... | yes (inj₂ y₁) rewrite recv-act-eq x y y₁ = inj₂ refl
    ... | yes (inj₁ (∈R refl)) rewrite recv-act-eq y x (∈S refl) = inj₂ refl
    ... | yes (inj₁ (∈S p)) with receiver α₁ ≟f receiver α₂
    ... | yes refl rewrite recv-act-eq x y (∈R refl) = inj₂ refl
    ... | no  R∉ = inj₁ (ii-≡snd (sym p) R∉)

    ◇-join : ∀ {G α G₁ α' G₂} → G -< α >-> G₁ → G -< α' >-> G₂
        → α ∥ α' → Behav
    ◇-join gr gr′ ii = proj₁ (diamond gr gr′ ii)

    ◇-l : ∀ {G α G₁ α' G₂} (gr : G -< α >-> G₁) (gr' : G -< α' >-> G₂)
        → (ii : α ∥ α') → G₁ -< α' >-> ◇-join gr gr' ii
    ◇-l gr gr′ ii = proj₁ (proj₂ (diamond gr gr′ ii))

    ◇-r : ∀ {G α G₁ α' G₂} (gr : G -< α >-> G₁) (gr' : G -< α' >-> G₂)
        → (ii : α ∥ α') → G₂ -< α >-> ◇-join gr gr' ii
    ◇-r gr gr′ ii = proj₂ (proj₂ (diamond gr gr′ ii))

    ∉B-step : ∀ {G α G' P} → G -< α >-> G' → ¬ P ∈T G → ¬ P ∈T G'
    ∉B-step st = contraposition (in/later st)

    ~traceback : ∀ {P G G' Gi} → G ~ G' → Gi =<¬ P >=>ᵣ G
      → ∃[ Gi' ] (Gi ~ Gi') × Gi' =<¬ P >=>ᵣ G'
    ~traceback b rt/refl = _ , b , rt/refl
    ~traceback b (rt/trans gr (x , nP))
      = let Gii , bG , y = ~stepback b x
            Gi' , bR , gr' = ~traceback bG gr
        in _ , bR , rt/trans gr' (y , nP)

    ~traceback/l : ∀ {P G G' Gi} → G ~ G' → Gi =<¬ P >=> G
      → ∃[ Gi' ] (Gi ~ Gi') × Gi' =<¬ P >=> G'
    ~traceback/l b (■ , tt) = _ , b , (■ , tt)
    ~traceback/l b ((x ► tr) , P∉x , P∉tr)
      = let Gii , bG , tr' , P∉tr'  = ~traceback/l b (tr , P∉tr)
            Gi' , bR , x' = ~stepback bG x
        in _ , bR , (x' ► tr') , P∉x ,  P∉tr'


  record BT-Extra {N : ℕ}(B : BTheory N) : Set₁ where
    open Definitions.Common(N)
    open Definitions.Actions(N)
    open BTheory B
    field

      can-step? : ∀ P B → Dec (P ∈tr B)

    skippable? : ∀ {Bi Bo} P → (tr : Bi ~~> Bo) → Dec (skippable P tr)
    skippable? {Bi = B} P ■ = can-step? P B
    skippable? {Bi = B} P (x BTheory.► tr) with can-step? P B
    ... | yes p = no (λ z → z .proj₁ p)
    ... | no ¬p with skippable? P tr
    ... | yes sk = yes (¬p , sk)
    ... | no ¬sk = no (λ z → ¬sk (z .proj₂))

    unrelated? : ∀ {Bi Bo} P → (tr : Bi ~~> Bo)
      → Dec (until tr (λ _ α → P ∉α α) ⊤)
    unrelated? {Bi = B} P ■ = yes tt
    unrelated? {Bi = B} P (_►_ {α = α} x tr) with P ∈α? α
    ... | yes f = no λ z → z .proj₁ f
    ... | no ¬p with unrelated? P tr
    ... | yes p = yes (¬p , p)
    ... | no ¬p = no (λ z → ¬p (z .proj₂))


