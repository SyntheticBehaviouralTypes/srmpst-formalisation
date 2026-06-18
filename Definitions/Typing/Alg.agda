{-# OPTIONS --guardedness #-}

-- The algorithmic judgment `Γ ⊢a P ◂ Pr ∶ 𝒮`, on a set of states.  A
-- state carries its `rec` anchors (`State δ`).  Liveness is `Wait`, a
-- finite tree with ancestor cycles; no reachability condition can replace
-- it (`Tests/WaitNotSkip.agda`).

import Level
open Level using (0ℓ)

open import Data.Nat using (ℕ; suc)

open import Data.Fin using (Fin)

open import Data.Vec
  using (Vec; _∷_)
  renaming (lookup to lu)

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_)

open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)

open import Data.Empty using (⊥; ⊥-elim)

open import Function using (_∘_)

open import Relation.Nullary using (¬_)

open import Relation.Unary using (Pred; _∈_; _⊆_; _∩_; Satisfiable)

open import Data.Fin.Subset using () renaming (_∈_ to _∈ˢ_)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)

open import Definitions.Typing

module Definitions.Typing.Alg {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  open MPST wb

  -- ══════════════════════════════════════════════════════════════════
  --  `Wait`: the finite tree, over single states
  -- ══════════════════════════════════════════════════════════════════

  -- Sets of behaviours.
  Behavs : Set₁
  Behavs = Pred Behav 0ℓ

  Closed : ∀ {ℓ} → Pred Behav ℓ → Set ℓ
  Closed 𝒮 = ∀ {G H} → G ~ H → 𝒮 G → 𝒮 H

  -- A `⊢skip` visited vector, read as a set, up to `~`.
  Vof : ∀ {ξ} → Vec Behav ξ → Behavs
  Vof Ξ s = ∃[ X ] (lu Ξ X ~ s)

  -- A finite tree of `P`-idle steps down to leaves in `L`; `V` is the set
  -- of visited states, which `wv/cycle` may close back to.
  data WaitV (P : PartSet)(L : Behavs) : Behavs → Behav → Set₁ where

    wv/leaf :
      ∀ {V s}
      → L s
      → WaitV P L V s

    wv/cycle :
      ∀ {V s}
      → (anc : ∃[ a ] V a × (a ~ s))
      → (inT : P ∈T s)
      → WaitV P L V s

    wv/step :
      ∀ {V s α t}
      → (na : P not-active-in s)
      → (gr : s -< α >-> t)
      → (k  : ∀ {β u} → s -< β >-> u → WaitV P L (λ v → V v ⊎ (s ~ v)) u)
      → WaitV P L V s

  waitV/mono :
    ∀ {P}{L V V′ : Behavs}
    → V ⊆ V′
    → ∀ {s} → WaitV P L V s → WaitV P L V′ s

  waitV/mono f (wv/leaf x) =
    wv/leaf x

  waitV/mono f (wv/cycle (a , a∈ , a~s) inT) =
    wv/cycle (a , f a∈ , a~s) inT

  waitV/mono f (wv/step na gr k) =
    wv/step na gr
      (λ gr′ →
        waitV/mono
          (λ { (inj₁ x)   → inj₁ (f x)
             ; (inj₂ s~v) → inj₂ s~v })
          (k gr′))

  waitV/leaf-mono :
    ∀ {P}{L L′ V : Behavs}
    → L ⊆ L′
    → ∀ {s} → WaitV P L V s → WaitV P L′ V s

  waitV/leaf-mono f (wv/leaf x)       = wv/leaf (f x)
  waitV/leaf-mono f (wv/cycle a inT)  = wv/cycle a inT
  waitV/leaf-mono f (wv/step na gr k) =
    wv/step na gr (λ gr′ → waitV/leaf-mono f (k gr′))

  -- `~`-closure.
  wait/~ :
    ∀ {P}{L : Behavs}
    → Closed L
    → ∀ {V : Behavs}
    → Closed (WaitV P L V)

  wait/~ c G~H (wv/leaf x) =
    wv/leaf (c G~H x)

  wait/~ c G~H (wv/cycle (a , a∈ , a~G) inT) =
    wv/cycle (a , a∈ , ~trans a~G G~H) (∈~ G~H inT)

  wait/~ c G~H (wv/step na gr k) =
    wv/step
      (na-bisim G~H na)
      (~L→ G~H gr)
      (λ gr′ →
        waitV/mono
          (λ { (inj₁ x)   → inj₁ x
             ; (inj₂ G~v) → inj₂ (~trans (~sym G~H) G~v) })
          (wait/~ c (~R→~ G~H gr′) (k (~R→ G~H gr′))))

  -- If every leaf makes `P` active, so does the root.
  waitActive :
    ∀ {P}{L V : Behavs}{s}
    → (∀ {u} → L u → P ∈T u)
    → WaitV P L V s
    → P ∈T s

  waitActive f (wv/leaf x)        = f x
  waitActive f (wv/cycle _ inT)   = inT
  waitActive f (wv/step _ gr k)   = in/later gr (waitActive f (k gr))

  -- At a root where `P` is ACTIVE, the tree is a leaf.
  waitLeaf :
    ∀ {P}{L : Behavs}{s α t}
    → s -< α >-> t
    → P ∈αˢ α
    → WaitV P L (λ _ → ⊥) s
    → L s

  waitLeaf _  _  (wv/leaf x)             = x
  waitLeaf _  _  (wv/cycle (_ , () , _) _)
  waitLeaf {P} {α = α} gr px (wv/step na _ _) =
    ⊥-elim (∉αˢ→¬∈αˢ {P} {α} (na gr) px)

  -- Re-rooting: each cycle back to the top `G` becomes `G`'s own tree.  The
  -- inclusion is a function so the recursion stays structural.
  waitV/unfold-top :
    ∀ {P}{L : Behavs}
    → Closed L
    → ∀ {G}
    → WaitV P L (λ _ → ⊥) G
    → ∀ {V W : Behavs}
    → (∀ {v} → W v → V v ⊎ (G ~ v))
    → ∀ {u}
    → WaitV P L W u
    → WaitV P L V u

  waitV/unfold-top c top f (wv/leaf x) =
    wv/leaf x

  waitV/unfold-top c top f (wv/cycle (a , wa , a~u) inT)
    with f wa
  ... | inj₁ va  = wv/cycle (a , va , a~u) inT
  ... | inj₂ G~a = waitV/mono (λ ()) (wait/~ c (~trans G~a a~u) top)

  waitV/unfold-top c top f (wv/step na gr k) =
    wv/step na gr
      (λ gr′ →
        waitV/unfold-top c top
          (λ { (inj₁ w)   → [ (λ v → inj₁ (inj₁ v)) , inj₂ ]′ (f w)
             ; (inj₂ u~v) → inj₁ (inj₂ u~v) })
          (k gr′))

  -- ══════════════════════════════════════════════════════════════════
  --  States and sets of states
  -- ══════════════════════════════════════════════════════════════════
  --
  -- A state is the anchors of the enclosing `rec`s and a behaviour.

  State : ℕ → Set
  State δ = Vec Behav δ × Behav

  States : ℕ → Set₁
  States δ = Pred (State δ) 0ℓ

  private
    variable
      γ δ : ℕ

  -- Successors by `step`; anchors stay.
  PostBy : (Behav → Behav → Set) → States δ → States δ
  PostBy step 𝒮 (ws , t) = ∃[ s ] (ws , s) ∈ 𝒮 × step s t

  -- Successors by a step whose event at `P` is `e`.
  Post : Part → Event → States δ → States δ
  Post P e = PostBy (_-<[ P ↦ e ]>->_)

  -- Successors by a receive with event `e` at `R`, sent from outside `Q`.
  Postᴿ : PartSet → Part → Event → States δ → States δ
  Postᴿ Q R e = PostBy (_-<[ Q ∣ R ↦ e ]>->_)

  -- `P` acts at `Q` only, and a step with event `e` at `Q` is enabled.
  Dom : PartSet → Part → Event → States δ
  Dom P Q e (_ , s) = Focus P Q s × ∃[ t ] s -<[ Q ↦ e ]>-> t

  -- A role of `P` can act.
  Active : PartSet → Behav → Set
  Active P s = ∃[ α ] ∃[ t ] s -< α >-> t × P ∈αˢ α

  Act : PartSet → States δ
  Act P (_ , s) = Active P s

  -- Role `R` of `Q` can receive from outsider `P`, at arity `suc I`.
  Offers : PartSet → Part → Part → ℕ → States δ
  Offers Q P R I (_ , s) =
    Focus Q R s
    × Σ[ j ∈ Fin (suc I) ] ∃[ U ] ∃[ t ] s -<[ Q ∣ R ↦ (？ P) # j < U > ]>-> t

  -- `P` never acts again.
  Ended : PartSet → States δ
  Ended P (_ , s) = ¬ P ∈T s

  -- One step out of a `P`-idle state.
  _⇝[_]_ : Behav → PartSet → Behav → Set
  s ⇝[ P ] t = P not-active-in s × ∃[ β ] s -< β >-> t

  -- Idle-reachable states: `Post*` of `_⇝[ P ]_`.
  Reach : PartSet → States δ → States δ
  Reach P 𝒮 (ws , t) = ∃[ s ] (ws , s) ∈ 𝒮 × Star (_⇝[ P ]_) s t

  -- Where the idle walk stops: the first states at which `P` acts.
  Front : PartSet → States δ → States δ
  Front P 𝒮 = Reach P 𝒮 ∩ Act P

  -- Every leaf of a tree is idle-reachable from its root.
  waitV/walk :
    ∀ {P}{L V : Behavs}{s}
    → WaitV P L V s
    → WaitV P (λ u → L u × Star (_⇝[ P ]_) s u) V s

  waitV/walk (wv/leaf x)       = wv/leaf (x , ε)
  waitV/walk (wv/cycle a inT)  = wv/cycle a inT
  waitV/walk (wv/step na gr k) =
    wv/step na gr
      (λ gr′ →
        waitV/leaf-mono
          (λ { (x , run) → x , (na , _ , gr′) ◅ run })
          (waitV/walk (k gr′)))

  -- `Wait`, lifted to states: the anchors ride along.
  Wait : PartSet → States δ → Pred (State δ) (Level.suc 0ℓ)
  Wait P L (ws , s) = WaitV P (λ t → (ws , t) ∈ L) (λ _ → ⊥) s

  -- Forward along `¬P` runs, up to `~` (`t/unskip`); unlike `Reach`, these
  -- may pass `P`-active states.
  Unskip : PartSet → States δ → States δ
  Unskip P 𝒜 (ws , s) =
    ∃[ a ] (ws , a) ∈ 𝒜 × ∃[ s′ ] a -[¬ P ]->* s′ × s′ ~ s

  -- The anchor of variable `X`, up to `~`.
  Var : Fin δ → States δ
  Var X (ws , s) = lu ws X ~ s

  -- `rec` entry: the new anchor is the state `rec` was entered at.
  Diag : States δ → States (suc δ)
  Diag 𝒜 (W ∷ ws , s) = (ws , W) ∈ 𝒜 × W ~ s

  -- The continuation set of `a/send`/`a/recv` is monotone.
  after/mono :
    ∀ {P step}{𝒮 𝒮′ : States δ}
    → 𝒮′ ⊆ 𝒮 → PostBy step (Front P 𝒮′) ⊆ PostBy step (Front P 𝒮)
  after/mono f {ws , _} (s , ((a , a∈ , run) , act) , gr) =
    s , ((a , f {ws , a} a∈ , run) , act) , gr

  -- ══════════════════════════════════════════════════════════════════
  --  The judgment
  -- ══════════════════════════════════════════════════════════════════

  infix 4 _⊢a_∶_

  data _⊢a_∶_ (Γ : Vec Sort γ) : NProc γ δ → States δ → Set₁ where

    -- The process `P` waits; its role `Q` sends.
    a/send :
      ∀ {P Q Qs I}{i : Fin (suc I)}{S E Pr}{𝒮 : States δ}
      → let e = (! Qs) # i < S > in
        (Q∈  : Q ∈ˢ P)
      → (etd : Γ ⊢e E ∶ S)
      → (rdy : 𝒮 ⊆ Wait P (Dom P Q e))
      → (td  : Γ ⊢a P ◂ Pr ∶ Post Q e (Front P 𝒮))
      → Γ ⊢a P ◂ Q ⇒ Qs ! i < E >∙ Pr ∶ 𝒮

    -- Every offered branch `(j , U)` is typed; unoffered ones need not be.
    a/recv :
      ∀ {P Q R I}{Br : Vec (Proc (suc γ) δ) (suc I)}{𝒮 : States δ}
      → (R∈    : R ∈ˢ Q)
      → (rdy   : 𝒮 ⊆ Wait Q (Offers Q P R I))
      → (conts : ∀ {j U} → let e = (？ P) # j < U > in
                 Satisfiable (Postᴿ Q R e (Front Q 𝒮))
               → (U ∷ Γ) ⊢a Q ◂ lu Br j ∶ Postᴿ Q R e (Front Q 𝒮))
      → Γ ⊢a Q ◂ R ⇐ P ？· Br ∶ 𝒮

    a/if :
      ∀ {P E A B}{𝒮 : States δ}
      → (etd : Γ ⊢e E ∶ s/bool)
      → (ttd : Γ ⊢a P ◂ A ∶ 𝒮)
      → (ftd : Γ ⊢a P ◂ B ∶ 𝒮)
      → Γ ⊢a P ◂ ifp E then A else B ∶ 𝒮

    a/end :
      ∀ {P}{𝒮 : States δ}
      → (done : 𝒮 ⊆ Ended P)
      → Γ ⊢a P ◂ ∅ ∶ 𝒮

    a/var :
      ∀ {P X}{𝒮 : States δ}
      → (rdy : 𝒮 ⊆ Wait P (Unskip P (Var X)))
      → Γ ⊢a P ◂ v X ∶ 𝒮

    -- `𝒜`: the states `rec` is entered at.
    a/rec :
      ∀ {P Pr}{𝒮 𝒜 : States δ}
      → (guarded : MessageGuarded Pr)
      → (td      : Γ ⊢a P ◂ Pr ∶ Diag 𝒜)
      → (rdy     : 𝒮 ⊆ Wait P (Unskip P 𝒜))
      → Γ ⊢a P ◂ rec Pr ∶ 𝒮

  -- Downward closure of `𝒮`.
  alg/mono :
    ∀ {Γ : Vec Sort γ}{PPr : NProc γ δ}{𝒮 𝒮′}
    → 𝒮′ ⊆ 𝒮
    → Γ ⊢a PPr ∶ 𝒮
    → Γ ⊢a PPr ∶ 𝒮′

  alg/mono {𝒮 = 𝒮}{𝒮′} f (a/send {Q = Q}{Qs}{i = i}{S} Q∈ etd rdy td) =
    a/send Q∈ etd (rdy ∘ f)
      (alg/mono (after/mono {step = _-<[ Q ↦ (! Qs) # i < S > ]>->_}
                  {𝒮 = 𝒮}{𝒮′} f)
        td)

  alg/mono {𝒮 = 𝒮}{𝒮′} f (a/recv {P = P}{Q}{R} R∈ rdy conts) =
    a/recv R∈ (rdy ∘ f)
      (λ { {j}{U} (x , x∈) →
           let mono = after/mono {step = _-<[ Q ∣ R ↦ (？ P) # j < U > ]>->_}
                        {𝒮 = 𝒮}{𝒮′} f
           in alg/mono mono (conts (x , mono {x} x∈)) })

  alg/mono f (a/if etd ttd ftd) =
    a/if etd (alg/mono f ttd) (alg/mono f ftd)

  alg/mono f (a/end done)            = a/end (done ∘ f)
  alg/mono f (a/var rdy)             = a/var (rdy ∘ f)
  alg/mono f (a/rec guarded td rdy)  = a/rec guarded td (rdy ∘ f)

  -- ══════════════════════════════════════════════════════════════════
  --  Typed at a state
  -- ══════════════════════════════════════════════════════════════════

  infix 4 _⊢at_∶_

  _⊢at_∶_ : Vec Sort γ → NProc γ δ → State δ → Set₁
  Γ ⊢at PPr ∶ x = Σ[ 𝒮 ∈ States _ ] (Γ ⊢a PPr ∶ 𝒮) × x ∈ 𝒮

  at/if-inv :
    ∀ {Γ : Vec Sort γ}{P E}{A B : Proc γ δ}{x}
    → Γ ⊢at P ◂ ifp E then A else B ∶ x
    → (Γ ⊢e E ∶ s/bool) × (Γ ⊢at P ◂ A ∶ x) × (Γ ⊢at P ◂ B ∶ x)

  at/if-inv (𝒮 , a/if etd ttd ftd , x∈) =
    etd , (𝒮 , ttd , x∈) , (𝒮 , ftd , x∈)

  -- A send: the sort, the `Wait`, and the continuation after any idle walk
  -- followed by the send.
  at/send-inv :
    ∀ {Γ : Vec Sort γ}{P Q Qs I}{i : Fin (suc I)}{E}{Pr : Proc γ δ}{ws G}
    → Γ ⊢at P ◂ Q ⇒ Qs ! i < E >∙ Pr ∶ (ws , G)
    → ∃[ S ] let e = (! Qs) # i < S > in
        (Γ ⊢e E ∶ S)
      × (ws , G) ∈ Wait P (Dom P Q e)
      × (∀ {u t} → Star (_⇝[ P ]_) G u → u -<[ Q ↦ e ]>-> t
                 → Γ ⊢at P ◂ Pr ∶ (ws , t))

  at/send-inv {ws = ws}{G} (_ , a/send Q∈ etd rdy td , mem) =
    _ , etd , rdy {ws , G} mem ,
    λ { run (α , eq , g) →
          _ , td ,
          ( _ , ((G , mem , run) , (α , _ , g , (_ , Q∈ , _ , eq)))
          , (α , eq , g)) }

  -- A receive: the `Wait`, and every offered branch after any idle walk.
  at/recv-inv :
    ∀ {Γ : Vec Sort γ}{P Q R I}{Br : Vec (Proc (suc γ) δ) (suc I)}{ws G}
    → Γ ⊢at Q ◂ R ⇐ P ？· Br ∶ (ws , G)
    → (ws , G) ∈ Wait Q (Offers Q P R I)
    × (∀ {u j U t} → Star (_⇝[ Q ]_) G u
                   → u -<[ Q ∣ R ↦ (？ P) # j < U > ]>-> t
                   → (U ∷ Γ) ⊢at Q ◂ lu Br j ∶ (ws , t))

  at/recv-inv {ws = ws}{G} (_ , a/recv R∈ rdy conts , mem) =
    rdy {ws , G} mem ,
    λ { run (α , eq , g , fr) →
          let x∈ = _ , ((G , mem , run) , (α , _ , g , (_ , R∈ , _ , eq)))
                     , (α , eq , g , fr)
          in _ , conts (_ , x∈) , x∈ }

  at/rec-guarded :
    ∀ {Γ : Vec Sort γ}{P}{Pr : Proc γ (suc δ)}{x}
    → Γ ⊢at P ◂ rec Pr ∶ x
    → MessageGuarded Pr

  at/rec-guarded (_ , a/rec guarded _ _ , _) = guarded
