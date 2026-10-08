{-# OPTIONS --guardedness #-}

-- `⊢p → ⊢a` (`typing⇒alg`), by recursion on the process.
--
-- A `⊢p` derivation is first converted to a `WaitV` tree over a leaf family
-- carrying the facts its rule needs, and the facts are read off with
-- `waitFind`.  Reading them off `⊢p` directly is not structural: `t/skip`'s
-- leaves are `⊢p` derivations again.  Each family is `~`-closed and advances
-- along `¬P` steps.

open import Data.Bool using (Bool; true; false; if_then_else_)

open import Data.Nat using (ℕ; suc)

open import Data.Fin using (Fin; zero; suc)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_)

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Empty using (⊥)

open import Data.Unit using (⊤; tt)

open import Data.List.Relation.Unary.Any using (here; there)

open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality using (refl)

open import Relation.Unary using (_∈_; _⊆_)

open import Data.Fin.Subset using () renaming (_∈_ to _∈ˢ_)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)

open import Definitions.Typing.Declarative

module Definitions.Typing.AlgNorm
  {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where

  open MPST wb

  open import Definitions.Typing.Alg wb
  open import Definitions.Typing.Properties wb using (td/bisim)
  open import Definitions.Typing.MainLeaf wb using (waitFind)

  private
    variable
      γ δ ξ : ℕ

  -- ══════════════════════════════════════════════════════════════════
  --  The canonical set: `⊢p`-typeability
  -- ══════════════════════════════════════════════════════════════════

  Typ : Vec Sort γ → Vec Behav δ → NProc γ δ → Behavs
  Typ Γ Δ PPr G = Γ & Δ ⊢p PPr ∶ G

  typ/closed :
    ∀ {Γ : Vec Sort γ}{Δ : Vec Behav δ}{P}{Pr : Proc γ δ}
    → Closed (Typ Γ Δ (P ◂ Pr))
  typ/closed = td/bisim ~ᵛ-refl

  -- ══════════════════════════════════════════════════════════════════
  --  Following a `¬P` run with a `Wait`
  -- ══════════════════════════════════════════════════════════════════
  --
  -- A `wv/step` node re-roots (`waitV/unfold-top`), a leaf advances by
  -- `adv`; no cycle occurs, as the visited set is empty.

  Advances : PartSet → Behavs → Set
  Advances P 𝒮 = ∀ {u α v} → 𝒮 u → u -< α >-> v → P ∉αˢ α → 𝒮 v

  waitStep1 :
    ∀ {P}{𝒮 : Behavs}
    → Closed 𝒮
    → Advances P 𝒮
    → ∀ {u α v}
    → WaitV P 𝒮 (λ _ → ⊥) u
    → u -< α >-> v
    → P ∉αˢ α
    → WaitV P 𝒮 (λ _ → ⊥) v

  waitStep1 c adv (wv/leaf x) gr P∉α =
    wv/leaf (adv x gr P∉α)

  waitStep1 c adv (wv/cycle (_ , () , _) _) _ _

  waitStep1 c adv top@(wv/step _ _ k) gr _ =
    waitV/unfold-top c top (λ w → w) (k gr)

  waitFollow :
    ∀ {P}{𝒮 : Behavs}
    → Closed 𝒮
    → Advances P 𝒮
    → ∀ {G s}
    → WaitV P 𝒮 (λ _ → ⊥) G
    → G -[¬ P ]->* s
    → WaitV P 𝒮 (λ _ → ⊥) s

  waitFollow c adv w ([] , tr/refl , []) = w
  waitFollow c adv w (_ ∷ αs , tr/step gr tr , P∉α ∷ allP) =
    waitFollow c adv (waitStep1 c adv w gr P∉α) (αs , tr , allP)

  idle⇒unskip : ∀ {P s t} → Star (_⇝[ P ]_) s t → s -[¬ P ]->* t
  idle⇒unskip ε                   = skip/refl
  idle⇒unskip ((na , _ , gr) ◅ run) = tr¬/step gr (na gr) (idle⇒unskip run)

  -- States a `¬P` run reaches from `𝒜`, up to `~` (`a/var`, `a/rec`).
  Unskipped : PartSet → Behavs → Behavs
  Unskipped P 𝒜 s = ∃[ a ] 𝒜 a × ∃[ s′ ] a -[¬ P ]->* s′ × s′ ~ s

  unskipped/~ : ∀ {P}{𝒜 : Behavs} → Closed (Unskipped P 𝒜)
  unskipped/~ G~H (a , a∈ , _ , tr , eq) =
    a , a∈ , _ , tr , ~trans eq G~H

  -- ══════════════════════════════════════════════════════════════════
  --  Visited vectors as sets (`Vof`, `Typing/Alg.agda`)
  -- ══════════════════════════════════════════════════════════════════

  vof/cons :
    ∀ {ξ}{Ξ : Vec Behav ξ}{A s} → Vof (A ∷ Ξ) s → Vof Ξ s ⊎ (A ~ s)
  vof/cons (zero  , eq) = inj₂ eq
  vof/cons (suc X , eq) = inj₁ (X , eq)

  vof/nil : ∀ {s} → Vof [] s → ⊥
  vof/nil (() , _)

  -- `∅`'s leaf family.  Families not mentioning `Γ`/`Δ` live outside the
  -- block below, where those would be unsolvable phantom parameters.
  EndL : PartSet → Behavs
  EndL P u = ¬ P ∈T u

  endL/closed : ∀ {P} → Closed (EndL P)
  endL/closed G~H x inT = x (∈~ (~sym G~H) inT)

  endL/adv : ∀ {P} → Advances P (EndL P)
  endL/adv x gr _ inT = x (in/later gr inT)

  ---------------------------------------------------------------------
  -- `a/end` needs `¬ P ∈T` at the root itself: chase the `P ∈T` run down
  -- the tree until a leaf refutes it.
  ---------------------------------------------------------------------

  endChase :
    ∀ {P}{G}
    → P ∈T G
    → WaitV P (EndL P) (λ _ → ⊥) G
    → ⊥

  endChase inT (wv/leaf x) = x inT
  endChase _ (wv/cycle (_ , () , _) _)
  endChase (_ , _ , tr/refl , ()) (wv/step _ _ _)
  endChase {P = P} (_ , _ , tr/step {α = α} gr₁ _ , here p)
           (wv/step na _ _) =
    ∉αˢ→¬∈αˢ {P} {α} (na gr₁) p
  endChase (_ , _ , tr/step gr₁ tr , there mem) top@(wv/step na _ _) =
    endChase (_ , _ , tr , mem)
      (waitStep1 endL/closed endL/adv top gr₁ (na gr₁))

  -- ══════════════════════════════════════════════════════════════════
  --  The leaf families
  -- ══════════════════════════════════════════════════════════════════

  unskipped/adv : ∀ {P}{𝒜 : Behavs} → Advances P (Unskipped P 𝒜)
  unskipped/adv (a , a∈ , _ , tr , eq) grα P∉α =
    let _ , gr′ , eq′ = ~R eq grα
    in a , a∈ , _ , skip/cat tr (skip/one gr′ P∉α) , eq′

  -- `rec`'s guardedness, a state-free fact kept out of `RecA`.
  RecG : ∀ {γ δ} → Proc γ (suc δ) → Behavs
  RecG Pr _ = MessageGuarded Pr

  recG/closed : ∀ {γ δ}{Pr : Proc γ (suc δ)} → Closed (RecG Pr)
  recG/closed _ guarded = guarded

  recG/adv : ∀ {γ δ}{P}{Pr : Proc γ (suc δ)} → Advances P (RecG Pr)
  recG/adv guarded _ _ = guarded

  -- `if`'s guard typing, constant in the state.
  module _ {γ}{Γ : Vec Sort γ} where

    IfE : Exp γ → Behavs
    IfE E _ = Γ ⊢e E ∶ s/bool

    ifE/closed : ∀ {E} → Closed (IfE E)
    ifE/closed _ etd = etd

    ifE/adv : ∀ {P}{E} → Advances P (IfE E)
    ifE/adv etd _ _ = etd

  module _ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ} where

    ---------------------------------------------------------------------
    -- send
    ---------------------------------------------------------------------

    -- Role `Q` of `P` sends.
    SendL :
      ∀ {I} → PartSet → Part → PartSet → Fin (suc I) → Sort → Proc γ δ
      → Behavs
    SendL P Q Qs i S Pr u =
      Q ∈ˢ P × Focus P Q u
      × ∃[ u′ ] (u -<[ Q ↦ (! Qs) # i < S > ]>-> u′) × Typ Γ Δ (P ◂ Pr) u′

    sendL/closed :
      ∀ {I P Q Qs}{i : Fin (suc I)}{S}{Pr} → Closed (SendL P Q Qs i S Pr)
    sendL/closed G~H (Q∈ , foc , _ , (α , eq , gr) , td) =
      Q∈ , focus/~ G~H foc , _ , (α , eq , ~L→ G~H gr)
      , typ/closed (~L→~ G~H gr) td

    sendL/adv :
      ∀ {I P Q Qs}{i : Fin (suc I)}{S}{Pr} → Advances P (SendL P Q Qs i S Pr)
    sendL/adv {P = P} (Q∈ , foc , _ , (α , eq , gr) , td) grα P∉α
      with skip/advance {P = P} (skip/one {P = P} grα P∉α) gr
             (_ , Q∈ , _ , eq)
    ... | _ , gr′ , _ , tr , Z~ =
      Q∈ , focus/skip foc (skip/one {P = P} grα P∉α) , _ , (α , eq , gr′)
      , t/unskip tr Z~ td

    ---------------------------------------------------------------------
    -- recv
    ---------------------------------------------------------------------

    -- Role `R` of `Q` receives from `P`.
    RecvL :
      ∀ {I} → Part → PartSet → Part → Vec (Proc (suc γ) δ) (suc I) → Behavs
    RecvL {I} P Q R Br u =
      R ∈ˢ Q × Focus Q R u
      × (Σ[ j ∈ Fin (suc I) ] ∃[ U ] ∃[ t ]
           (u -<[ Q ∣ R ↦ (？ P) # j < U > ]>-> t))
      × (∀ {j U t} → u -<[ Q ∣ R ↦ (？ P) # j < U > ]>-> t
                   → Typ (U ∷ Γ) Δ (Q ◂ lu Br j) t)

    recvL/closed :
      ∀ {I P Q R}{Br : Vec (Proc (suc γ) δ) (suc I)} → Closed (RecvL P Q R Br)
    recvL/closed G~H (R∈ , foc , (j , U , _ , (α , eq , gr , fr)) , k) =
      R∈ , focus/~ G~H foc , (j , U , _ , (α , eq , ~L→ G~H gr , fr)) ,
      λ { (α′ , eq′ , gr′ , fr′) →
          typ/closed (~R→~ G~H gr′) (k (α′ , eq′ , ~R→ G~H gr′ , fr′)) }

    -- A branch offered after a `¬Q` step was offered before it.
    recvL/adv :
      ∀ {I P Q R}{Br : Vec (Proc (suc γ) δ) (suc I)}
      → Advances Q (RecvL P Q R Br)
    recvL/adv {Q = Q} (R∈ , foc , (j , U , _ , (α , eq , gr , fr)) , k) grα Q∉α
      with skip/advance {P = Q} (skip/one {P = Q} grα Q∉α) gr
             (_ , R∈ , _ , eq)
    ... | _ , gr′ , _ =
      R∈ , focus/skip foc (skip/one {P = Q} grα Q∉α)
      , (j , U , _ , (α , eq , gr′ , fr)) ,
      λ { (α″ , eq″ , gr″ , fr″) →
          let tr  = skip/one {P = Q} grα Q∉α
              ceq = recv/same-comm tr R∈ gr (_ , _ , eq) gr″ (_ , _ , eq″)
              _ , gr₀ , _ , tr₀ , H~ =
                branch/before tr R∈ (_ , _ , eq) gr gr″ ceq
          in t/unskip tr₀ H~ (k (α″ , eq″ , gr₀ , fr″)) }

    ---------------------------------------------------------------------
    -- rec
    ---------------------------------------------------------------------

    -- `a/rec`'s anchor set: the body typed at its own anchor.
    RecA : ∀ {P} → Proc γ (suc δ) → Behavs
    RecA {P = P} Pr W = Typ Γ (W ∷ Δ) (P ◂ Pr) W

    recA/closed :
      ∀ {P}{Pr : Proc γ (suc δ)} → Closed (RecA {P = P} Pr)
    recA/closed W~W′ td =
      td/bisim (~ᵛ/∷ W~W′ ~ᵛ-refl) W~W′ td

    ---------------------------------------------------------------------
    ---------------------------------------------------------------------

    -- The send's sort, found once before `sendWait` runs at it.
    SendE :
      ∀ {I} → PartSet → Part → PartSet → Fin (suc I) → Exp γ → Proc γ δ
      → Behavs
    SendE P Q Qs i E Pr u =
      Q ∈ˢ P
      × Σ[ S ∈ Sort ]
          ∃[ u′ ] (Γ ⊢e E ∶ S) × (u -<[ Q ↦ (! Qs) # i < S > ]>-> u′)
                × Typ Γ Δ (P ◂ Pr) u′

    sendE/closed :
      ∀ {I P Q Qs}{i : Fin (suc I)}{E}{Pr} → Closed (SendE P Q Qs i E Pr)
    sendE/closed G~H (Q∈ , S , _ , etd , (α , eq , gr) , td) =
      Q∈ , S , _ , etd , (α , eq , ~L→ G~H gr) , typ/closed (~L→~ G~H gr) td

    sendE/adv :
      ∀ {I P Q Qs}{i : Fin (suc I)}{E}{Pr} → Advances P (SendE P Q Qs i E Pr)
    sendE/adv {P = P} (Q∈ , S , _ , etd , (α , eq , gr) , td) grα P∉α
      with skip/advance {P = P} (skip/one {P = P} grα P∉α) gr
             (_ , Q∈ , _ , eq)
    ... | _ , gr′ , _ , tr , Z~ =
      Q∈ , S , _ , etd , (α , eq , gr′) , t/unskip tr Z~ td

  -- ══════════════════════════════════════════════════════════════════
  --  `⊢p` derivation ⟶ `Wait`, for every leaf family at once
  -- ══════════════════════════════════════════════════════════════════
  --
  -- Only `base` differs between families.  It is a module parameter, not
  -- a mutually recursive function, so the recursion stays structural.

  Base : ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{PPr G} → Γ & Δ ⊢p PPr ∶ G → Set
  Base (t/skip _)       = ⊥
  Base (t/unskip _ _ _) = ⊥
  Base _                = ⊤

  module Walk
    {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{P}{Pr : Proc γ δ}
    (L : Behavs)(c : Closed L)(adv : Advances P L)
    (base : ∀ {G}(td : Γ & Δ ⊢p P ◂ Pr ∶ G) → Base td → L G)
    where

    mutual

      walk : ∀ {G} → Γ & Δ ⊢p P ◂ Pr ∶ G → WaitV P L (λ _ → ⊥) G
      walk (t/unskip tr eq td) = wait/~ c eq (waitFollow c adv (walk td) tr)
      walk (t/skip std)        = waitV/mono vof/nil (tree std)
      walk td@(t/send _ _ _ _ _) = wv/leaf (base td tt)
      walk td@(t/recv _ _ _ _)   = wv/leaf (base td tt)
      walk td@(t/if _ _ _)     = wv/leaf (base td tt)
      walk td@(t/rec _ _)      = wv/leaf (base td tt)
      walk td@(t/var _)        = wv/leaf (base td tt)
      walk td@(t/end _)        = wv/leaf (base td tt)

      tree :
        ∀ {ξ}{Ξ : Vec Behav ξ}{G}
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ Pr ∶ G
        → WaitV P L (Vof Ξ) G
      tree (skip/main td)              = waitV/mono (λ ()) (walk td)
      tree (skip/step gr na ktd)       =
        wv/step na gr (λ gr′ → waitV/mono vof/cons (tree (ktd gr′)))
      tree (skip/cycle {X = X} eq inT) = wv/cycle (_ , (X , ~refl) , eq) inT

  module _ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Behav δ} where

    sendWait :
      ∀ {I P Q Qs}{i : Fin (suc I)}{S E}{Pr : Proc γ δ}{G}
      → Γ ⊢e E ∶ S
      → Γ & Δ ⊢p P ◂ Q ⇒ Qs ! i < E >∙ Pr ∶ G
      → WaitV P (SendL {Γ = Γ} {Δ = Δ} P Q Qs i S Pr) (λ _ → ⊥) G
    sendWait etd = Walk.walk _ sendL/closed sendL/adv base
      where
        base :
          ∀ {G}(td : Γ & Δ ⊢p _ ◂ _ ∶ G) → Base td → SendL _ _ _ _ _ _ G
        base (t/send Q∈ foc gr etd′ td) _ with ⊢e-unique etd′ etd
        ... | refl = Q∈ , foc , _ , gr , td

    recvWait :
      ∀ {I P Q R}{Br : Vec (Proc (suc γ) δ) (suc I)}{G}
      → Γ & Δ ⊢p Q ◂ R ⇐ P ？· Br ∶ G
      → WaitV Q (RecvL {Γ = Γ} {Δ = Δ} P Q R Br) (λ _ → ⊥) G
    recvWait {Br = Br} =
      Walk.walk _ (recvL/closed {Br = Br}) (recvL/adv {Br = Br})
        λ { (t/recv R∈ foc gr conts) _ → R∈ , foc , (_ , _ , _ , gr) , conts }

    varWait :
      ∀ {P}{X : Fin δ}{G}
      → Γ & Δ ⊢p P ◂ v X ∶ G
      → WaitV P (Unskipped P (lu Δ X ~_)) (λ _ → ⊥) G
    varWait =
      Walk.walk _ unskipped/~ unskipped/adv
        λ { (t/var eq) _ → _ , eq , _ , skip/refl , ~refl }

    recWait :
      ∀ {P}{Pr : Proc γ (suc δ)}{G}
      → Γ & Δ ⊢p P ◂ rec Pr ∶ G
      → WaitV P (Unskipped P (RecA {Γ = Γ} {Δ = Δ} {P = P} Pr)) (λ _ → ⊥) G
    recWait {P = P} {Pr = Pr} =
      Walk.walk _ unskipped/~ unskipped/adv
        λ { (t/rec _ td) _ → _ , td , _ , skip/refl , ~refl }

    sendEWait :
      ∀ {I P Q Qs}{i : Fin (suc I)}{E}{Pr : Proc γ δ}{G}
      → Γ & Δ ⊢p P ◂ Q ⇒ Qs ! i < E >∙ Pr ∶ G
      → WaitV P (SendE {Γ = Γ} {Δ = Δ} P Q Qs i E Pr) (λ _ → ⊥) G
    sendEWait =
      Walk.walk _ sendE/closed sendE/adv
        λ { (t/send Q∈ _ gr etd td) _ → Q∈ , _ , _ , etd , gr , td }

    recGWait :
      ∀ {P}{Pr : Proc γ (suc δ)}{G}
      → Γ & Δ ⊢p P ◂ rec Pr ∶ G
      → WaitV P (RecG Pr) (λ _ → ⊥) G
    recGWait = Walk.walk _ recG/closed recG/adv λ { (t/rec guarded _) _ → guarded }

    ifEWait :
      ∀ {P E}{A B : Proc γ δ}{G}
      → Γ & Δ ⊢p P ◂ ifp E then A else B ∶ G
      → WaitV P (IfE {Γ = Γ} E) (λ _ → ⊥) G
    ifEWait = Walk.walk _ ifE/closed ifE/adv λ { (t/if etd _ _) _ → etd }

    endWait :
      ∀ {P}{G}
      → Γ & Δ ⊢p P ◂ ∅ ∶ G
      → WaitV P (EndL P) (λ _ → ⊥) G
    endWait = Walk.walk _ endL/closed endL/adv λ { (t/end done) _ → done }

    ---------------------------------------------------------------------
    -- An `if` derivation gives each branch's, at the same state.
    ---------------------------------------------------------------------

    mutual

      ifBranch :
        ∀ (b : Bool){P E}{A B : Proc γ δ}{G}
        → Γ & Δ ⊢p P ◂ ifp E then A else B ∶ G
        → Γ & Δ ⊢p P ◂ (if b then A else B) ∶ G

      ifBranch true  (t/if _ ttd _)    = ttd
      ifBranch false (t/if _ _ ftd)    = ftd
      ifBranch b (t/unskip tr eq td)   = t/unskip tr eq (ifBranch b td)
      ifBranch b (t/skip std)          = t/skip (ifBranchTree b std)

      ifBranchTree :
        ∀ (b : Bool){ξ}{Ξ : Vec Behav ξ}{P E}{A B : Proc γ δ}{G}
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ ifp E then A else B ∶ G
        → (Γ & Δ ⊢p_∶_) & Ξ ⊢skip P ◂ (if b then A else B) ∶ G

      ifBranchTree b (skip/main td) = skip/main (ifBranch b td)
      ifBranchTree b (skip/step gr na ktd) =
        skip/step gr na (λ gr′ → ifBranchTree b (ktd gr′))
      ifBranchTree b (skip/cycle eq inT) = skip/cycle eq inT


    endNotin :
      ∀ {P}{G}
      → Γ & Δ ⊢p P ◂ ∅ ∶ G
      → ¬ P ∈T G

    endNotin td inT = endChase inT (endWait td)

  -- ══════════════════════════════════════════════════════════════════
  --  `⊢p` ⟶ `⊢a`, at the largest set
  -- ══════════════════════════════════════════════════════════════════
  --
  -- Stated at the largest set, `Typed`; `alg/mono` gives every smaller one.
  -- Recursion on the process; `typBr` makes `lu Br j` structural.

  Typed : ∀ {γ δ} → Vec Sort γ → NProc γ δ → States δ
  Typed Γ PPr (ws , G) = Γ & ws ⊢p PPr ∶ G

  -- `a/rec`'s entry set: the body typed at its own anchor.
  Entry : ∀ {γ δ} → Vec Sort γ → PartSet → Proc γ (suc δ) → States δ
  Entry Γ P Pr (ws , W) = Γ & (W ∷ ws) ⊢p P ◂ Pr ∶ W

  recvAt :
    ∀ {γ δ}{Γ : Vec Sort γ}{I P Q R}{Br : Vec (Proc (suc γ) δ) (suc I)}{j U}
    → Postᴿ Q R ((？ P) # j < U >) (Front Q (Typed Γ (Q ◂ R ⇐ P ？· Br)))
      ⊆ Typed (U ∷ Γ) (Q ◂ lu Br j)

  recvAt {P = P}{Q}{R}{Br}{j}{U}{ws , t}
         (_ , ((_ , td , run) , _) , (α , eq , gr , fr))
    with waitFind (recvWait td)
  ... | _ , R∈ , _
    with waitLeaf {Q} gr (_ , R∈ , _ , eq)
           (waitFollow (recvL/closed {Br = Br}) (recvL/adv {Br = Br})
              (recvWait td) (idle⇒unskip run))
  ... | _ , _ , _ , k = k (α , eq , gr , fr)

  -- `bal`: `a/send` types the continuation after every step with `P`'s
  -- event, `t/send` after one; `send-det` makes them the same.
  module _ (bal : Balanced B) where
    open Balanced bal using (send-det)

    sendAt :
      ∀ {γ δ}{Γ : Vec Sort γ}{I P Q Qs}{i : Fin (suc I)}{S E}{Pr : Proc γ δ}
      → Γ ⊢e E ∶ S
      → Post Q ((! Qs) # i < S >)
          (Front P (Typed Γ (P ◂ Q ⇒ Qs ! i < E >∙ Pr)))
        ⊆ Typed Γ (P ◂ Pr)

    sendAt {P = P}{Q}{Qs}{i = i}{E = E}{Pr} etd {ws , t}
      (_ , ((_ , td , run) , _) , (α , eq , gr))
      with waitFind (sendWait etd td)
    ... | _ , Q∈ , _
      with waitLeaf {P} gr (_ , Q∈ , _ , eq)
             (waitFollow sendL/closed sendL/adv (sendWait etd td)
               (idle⇒unskip run))
    ... | _ , _ , _ , (α′ , eq′ , gr′) , td′
      with send-det gr gr′ eq eq′
    ...   | refl = typ/closed (step-deterministic gr′ gr) td′

    mutual

      typing⇒alg :
        ∀ {γ δ}{Γ : Vec Sort γ}{P}(Pr : Proc γ δ){ws G}
        → Γ & ws ⊢p P ◂ Pr ∶ G
        → Γ ⊢a P ◂ Pr ∶ Typed Γ (P ◂ Pr)

      typing⇒alg (Q ⇒ Qs ! i < E >∙ Pr) td
        with waitFind (sendEWait td)
      ... | _ , Q∈ , _ , _ , etd , _ , cont =
        a/send Q∈ etd
          (λ td′ → waitV/leaf-mono (λ { (_ , foc , _ , gr , _) → foc , _ , gr })
                     (sendWait etd td′))
          (alg/mono (sendAt etd) (typing⇒alg Pr cont))

      typing⇒alg (R ⇐ P ？· Br) td
        with waitFind (recvWait td)
      ... | _ , R∈ , _ =
        a/recv R∈
          (λ td′ → waitV/leaf-mono (λ { (_ , foc , off , _) → foc , off })
                     (recvWait td′))
          (λ { {j} (_ , x∈) →
               alg/mono (recvAt {Br = Br})
                 (typBr Br j (recvAt {Br = Br} x∈)) })

      typing⇒alg (ifp E then A else B) td
        with waitFind (ifEWait td)
      ... | _ , etd =
        a/if etd
          (alg/mono (ifBranch true)  (typing⇒alg A (ifBranch true td)))
          (alg/mono (ifBranch false) (typing⇒alg B (ifBranch false td)))

      typing⇒alg ∅ td = a/end endNotin

      typing⇒alg (v X) td = a/var varWait

      typing⇒alg {Γ = Γ}{P} (rec Pr) td
        with waitFind (recGWait td) | waitFind (recWait td)
      ... | _ , guarded | _ , _ , aW , _ =
        a/rec {𝒜 = Entry Γ P Pr} guarded
          (alg/mono (λ { {_ ∷ _ , _} (aW′ , W~s) → typ/closed W~s aW′ })
                    (typing⇒alg Pr aW))
          recWait

      typBr :
        ∀ {γ δ n}{Γ : Vec Sort γ}{Q}
          (Br : Vec (Proc (suc γ) δ) n)(j : Fin n){U ws t}
        → (U ∷ Γ) & ws ⊢p Q ◂ lu Br j ∶ t
        → (U ∷ Γ) ⊢a Q ◂ lu Br j ∶ Typed (U ∷ Γ) (Q ◂ lu Br j)

      typBr (B ∷ Bs) zero    w = typing⇒alg B w
      typBr (B ∷ Bs) (suc j) w = typBr Bs j w

    -- ════════════════════════════════════════════════════════════════
    --  The boundary `Safety/` uses
    -- ════════════════════════════════════════════════════════════════

    td⇒at :
      ∀ {γ δ}{Γ : Vec Sort γ}{P}{Pr : Proc γ δ}{ws G}
      → Γ & ws ⊢p P ◂ Pr ∶ G
      → Γ ⊢at P ◂ Pr ∶ (ws , G)

    td⇒at {Pr = Pr} td = _ , typing⇒alg Pr td , td
