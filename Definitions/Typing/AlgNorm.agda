{-# OPTIONS --guardedness #-}

-- `⊢ → ⊢a` (`typing⇒alg`), by recursion on the process.
--
-- A derivation of the paper's judgement at the class of a state is first
-- converted to a `WaitV` tree over a leaf family carrying the facts its
-- rule needs, and the facts are read off with `waitFind`.  Reading them
-- off the derivation directly is not structural: `skip`'s leaves are
-- derivations again.  Each family is `~`-closed and advances along `¬P`
-- steps.

open import Data.Bool using (Bool; true; false; if_then_else_)

open import Data.Nat using (ℕ; suc)

open import Data.Fin using (Fin; zero; suc)

open import Data.Vec
  using (Vec; []; _∷_)
  renaming (lookup to lu)

open import Data.Vec.Properties using (lookup-map)

open import Data.Vec.Relation.Unary.Any using () renaming (here to hereᵛ; there to thereᵛ)

import Data.Vec.Relation.Binary.Pointwise.Inductive as Pointwise

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)

open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_)

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Empty using (⊥)
open import Relation.Unary using () renaming (∅ to ∅S)

open import Data.Unit using (⊤; tt)

open import Data.List.Relation.Unary.Any using (here; there)

open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality using (refl; sym; subst; cong)

open import Relation.Unary using (_∈_; _⊆_)

open import Data.Fin.Subset using () renaming (_∈_ to _∈ˢ_; _∉_ to _∉ˢ_)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_; _◅◅_)

open import Data.Maybe using (Maybe; just)

open import Definitions.Typing.Declarative
open import Utils.Family using (_∋_↦_; here; there; ∋-functional)

module Definitions.Typing.AlgNorm
  {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where

  open MPST wb

  open import Definitions.Typing.Alg wb
  open import Definitions.Typing.Properties wb using (td/≐; ≐ᵛ-refl)
  open import Definitions.Typing.MainLeaf wb using (waitFind)

  private
    variable
      γ δ ξ : ℕ

  -- ══════════════════════════════════════════════════════════════════
  --  The canonical set: typeability at the class
  -- ══════════════════════════════════════════════════════════════════

  Typ : Vec Sort γ → Vec Cls δ → PartSet → Proc γ δ → Behavs
  Typ Γ Δ R Pr g = Γ & Δ ⊢[ R ] Pr ∶ [ g ]

  typ/closed :
    ∀ {Γ : Vec Sort γ}{Δ : Vec Cls δ}{R}{Pr : Proc γ δ}
    → Closed (Typ Γ Δ R Pr)
  typ/closed g~h = td/≐ ≐ᵛ-refl g~h

  -- Along a `¬R` run, then `~`.
  typ/unskip :
    ∀ {Γ : Vec Sort γ}{Δ : Vec Cls δ}{R}{Pr : Proc γ δ}{g z h}
    → Typ Γ Δ R Pr g → g -[¬ R ]->* z → z ~ h → Typ Γ Δ R Pr h
  typ/unskip td run z~h = td/≐ ≐ᵛ-refl z~h (forward td (run⇒ᶜ run))

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
    → WaitV P 𝒮 ∅S u
    → u -< α >-> v
    → P ∉αˢ α
    → WaitV P 𝒮 ∅S v

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
    → WaitV P 𝒮 ∅S G
    → G -[¬ P ]->* s
    → WaitV P 𝒮 ∅S s

  waitFollow c adv w ε                       = w
  waitFollow c adv w ((_ , gr , P∉α) ◅ run) =
    waitFollow c adv (waitStep1 c adv w gr P∉α) run

  idle⇒unskip : ∀ {P s t} → Star (_⇝[ P ]_) s t → s -[¬ P ]->* t
  idle⇒unskip ε                     = ε
  idle⇒unskip ((na , _ , gr) ◅ run) = (_ , gr , ¬act⇒∉ na gr) ◅ idle⇒unskip run

  -- States a `¬P` run reaches from `𝒜`, up to `~` (`a/var`, `a/rec`).
  Unskipped : PartSet → Behavs → Behavs
  Unskipped P 𝒜 s = ∃[ a ] 𝒜 a × ∃[ s′ ] a -[¬ P ]->* s′ × s′ ~ s

  unskipped/~ : ∀ {P}{𝒜 : Behavs} → Closed (Unskipped P 𝒜)
  unskipped/~ G~H (a , a∈ , _ , tr , eq) =
    a , a∈ , _ , tr , ~trans eq G~H

  -- ══════════════════════════════════════════════════════════════════
  --  Visited vectors of classes as sets
  -- ══════════════════════════════════════════════════════════════════

  Vofᶜ : Vec Cls ξ → Behavs
  Vofᶜ Ξ s = ∃[ X ] rep (lu Ξ X) ~ s

  vofᶜ/cons :
    ∀ {ξ}{Ξ : Vec Cls ξ}{A s} → Vofᶜ (A ∷ Ξ) s → Vofᶜ Ξ s ⊎ (rep A ~ s)
  vofᶜ/cons (zero  , eq) = inj₂ eq
  vofᶜ/cons (suc X , eq) = inj₁ (X , eq)

  vofᶜ/nil : ∀ {s} → Vofᶜ [] s → ⊥
  vofᶜ/nil (() , _)

  ∈ᵛ⇒vofᶜ : ∀ {ξ}{Ξ : Vec Cls ξ}{G} → G ∈ᵛ Ξ → ∃[ X ] lu Ξ X ≐ G
  ∈ᵛ⇒vofᶜ (hereᵛ x)  = zero , x
  ∈ᵛ⇒vofᶜ (thereᵛ a) = let X , e = ∈ᵛ⇒vofᶜ a in suc X , e

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
    ∀ {P}{G H}
    → G -→* H → H -⟨ P ⟩->
    → WaitV P (EndL P) ∅S G
    → ⊥

  endChase run act (wv/leaf x) = x (_ , run , act)
  endChase _ _ (wv/cycle (_ , () , _) _)
  endChase ε act (wv/step na _ _) = na act
  endChase ((_ , gr₁) ◅ run) act top@(wv/step na _ _) =
    endChase run act
      (waitStep1 endL/closed endL/adv top gr₁ (¬act⇒∉ na gr₁))

  -- ══════════════════════════════════════════════════════════════════
  --  The leaf families
  -- ══════════════════════════════════════════════════════════════════

  unskipped/adv : ∀ {P}{𝒜 : Behavs} → Advances P (Unskipped P 𝒜)
  unskipped/adv (a , a∈ , _ , tr , eq) grα P∉α =
    let _ , gr′ , eq′ = ~R eq grα
    in a , a∈ , _ , tr ◅◅ skip/one gr′ P∉α , eq′

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

    -- `let`'s expression typing, constant in the state.
    LetE : Exp γ → Behavs
    LetE E _ = ∃[ S ] Γ ⊢e E ∶ S

    letE/closed : ∀ {E} → Closed (LetE E)
    letE/closed _ etd = etd

    letE/adv : ∀ {P}{E} → Advances P (LetE E)
    letE/adv etd _ _ = etd

  module _ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Cls δ} where

    ---------------------------------------------------------------------
    -- send
    ---------------------------------------------------------------------

    -- Role `Q` of `P` sends.
    SendL :
      PartSet → Part → PartSet → ℕ → Sort → Proc γ δ
      → Behavs
    SendL P Q Qs i S Pr u =
      Q first-in (P , u)
      × ∃[ u′ ] (u -<[ Q ↦ (! Qs) # i < S > ]>-> u′) × Typ Γ Δ P Pr u′

    sendL/closed :
      ∀ {P Q Qs}{i : ℕ}{S}{Pr} → Closed (SendL P Q Qs i S Pr)
    sendL/closed G~H (fi , _ , (α , eq , gr) , td) =
      first-in/~ G~H fi , _ , (α , eq , ~L→ G~H gr)
      , typ/closed (~L→~ G~H gr) td

    sendL/adv :
      ∀ {P Q Qs}{i : ℕ}{S}{Pr} → Advances P (SendL P Q Qs i S Pr)
    sendL/adv {P = P} (fi@(Q∈ , _) , _ , (α , eq , gr) , td) grα P∉α
      with skip/advance {P = P} (skip/one {P = P} grα P∉α) gr
             (_ , Q∈ , _ , eq)
    ... | _ , gr′ , _ , tr , Z~ =
      first-in/skip fi (skip/one {P = P} grα P∉α) , _ , (α , eq , gr′)
      , typ/unskip td tr Z~

    ---------------------------------------------------------------------
    -- recv
    ---------------------------------------------------------------------

    -- Role `R` of `Q` receives from `P`.
    RecvL :
      ∀ {n} → Part → PartSet → Part → Vec (Maybe (Proc (suc γ) δ)) n → Behavs
    RecvL P Q R Br u =
      R first-in (Q , u)
      × (P ∉ˢ Q × ∃[ ℓ ] ∃[ U ] ∃[ t ] u -<[ R ↦ (？ P) # ℓ < U > ]>-> t)
      × (∀ {ℓ U t} → u -<[ R ↦ (？ P) # ℓ < U > ]>-> t
                   → ∃[ Pr ] Br ∋ ℓ ↦ Pr × Typ (U ∷ Γ) Δ Q Pr t)

    recvL/closed :
      ∀ {n P Q R}{Br : Vec (Maybe (Proc (suc γ) δ)) n} → Closed (RecvL P Q R Br)
    recvL/closed G~H (fi , (P∉ , ℓ , U , _ , (α , eq , gr)) , k) =
      first-in/~ G~H fi , (P∉ , ℓ , U , _ , (α , eq , ~L→ G~H gr)) ,
      λ { (α′ , eq′ , gr′) →
          let Pr , br , td = k (α′ , eq′ , ~R→ G~H gr′)
          in Pr , br , typ/closed (~R→~ G~H gr′) td }

    -- A branch offered after a `¬Q` step was offered before it.
    recvL/adv :
      ∀ {n P Q R}{Br : Vec (Maybe (Proc (suc γ) δ)) n}
      → Advances Q (RecvL P Q R Br)
    recvL/adv {Q = Q} (fi@(R∈ , _) , (P∉ , ℓ , U , _ , (α , eq , gr)) , k) grα Q∉α
      with skip/advance {P = Q} (skip/one {P = Q} grα Q∉α) gr
             (_ , R∈ , _ , eq)
    ... | _ , gr′ , _ =
      first-in/skip fi (skip/one {P = Q} grα Q∉α)
      , (P∉ , ℓ , U , _ , (α , eq , gr′)) ,
      λ { (α″ , eq″ , gr″) →
          let tr  = skip/one {P = Q} grα Q∉α
              ceq = recv/same-comm tr R∈ gr (_ , _ , eq) gr″ (_ , _ , eq″)
              _ , gr₀ , _ , tr₀ , H~ =
                branch/before tr R∈ (_ , _ , eq) gr gr″ ceq
              Pr , br , td = k (α″ , eq″ , gr₀)
          in Pr , br , typ/unskip td tr₀ H~ }

    ---------------------------------------------------------------------
    -- rec
    ---------------------------------------------------------------------

    -- `a/rec`'s anchor set: the body typed at its own anchor.
    RecA : ∀ {P} → Proc γ (suc δ) → Behavs
    RecA {P = P} Pr W = Γ & ([ W ] ∷ Δ) ⊢[ P ] Pr ∶ [ W ]

    recA/closed :
      ∀ {P}{Pr : Proc γ (suc δ)} → Closed (RecA {P = P} Pr)
    recA/closed W~W′ td =
      td/≐ (W~W′ Pointwise.∷ ≐ᵛ-refl) W~W′ td

    ---------------------------------------------------------------------
    ---------------------------------------------------------------------

    -- The send's sort, found once before `sendWait` runs at it.
    SendE :
      PartSet → Part → PartSet → ℕ → Exp γ → Proc γ δ
      → Behavs
    SendE P Q Qs i E Pr u =
      Q ∈ˢ P
      × Σ[ S ∈ Sort ]
          ∃[ u′ ] (Γ ⊢e E ∶ S) × (u -<[ Q ↦ (! Qs) # i < S > ]>-> u′)
                × Typ Γ Δ P Pr u′

    sendE/closed :
      ∀ {P Q Qs}{i : ℕ}{E}{Pr} → Closed (SendE P Q Qs i E Pr)
    sendE/closed G~H (Q∈ , S , _ , etd , (α , eq , gr) , td) =
      Q∈ , S , _ , etd , (α , eq , ~L→ G~H gr) , typ/closed (~L→~ G~H gr) td

    sendE/adv :
      ∀ {P Q Qs}{i : ℕ}{E}{Pr} → Advances P (SendE P Q Qs i E Pr)
    sendE/adv {P = P} (Q∈ , S , _ , etd , (α , eq , gr) , td) grα P∉α
      with skip/advance {P = P} (skip/one {P = P} grα P∉α) gr
             (_ , Q∈ , _ , eq)
    ... | _ , gr′ , _ , tr , Z~ =
      Q∈ , S , _ , etd , (α , eq , gr′) , typ/unskip td tr Z~

  -- ══════════════════════════════════════════════════════════════════
  --  Derivation ⟶ `Wait`, for every leaf family at once
  -- ══════════════════════════════════════════════════════════════════
  --
  -- Only `base` differs between families.  It is a module parameter, not
  -- a mutually recursive function, so the recursion stays structural.

  Base :
    ∀ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Cls δ}{R}{Pr : Proc γ δ}{G}
    → Γ & Δ ⊢[ R ] Pr ∶ G → Set
  Base (skip _)      = ⊥
  Base (forward _ _) = ⊥
  Base _             = ⊤

  module Walk
    {γ δ}{Γ : Vec Sort γ}{Δ : Vec Cls δ}{R}{Pr : Proc γ δ}
    (L : Behavs)(c : Closed L)(adv : Advances R L)
    (base : ∀ {G}(td : Γ & Δ ⊢[ R ] Pr ∶ G) → Base td → L (rep G))
    where

    mutual

      walk : ∀ {G} → Γ & Δ ⊢[ R ] Pr ∶ G → WaitV R L ∅S (rep G)
      walk (forward td run) =
        let h , run′ , h~ = runᶜ⇒ run
        in wait/~ c h~ (waitFollow c adv (walk td) run′)
      walk (skip std)              = waitV/mono vofᶜ/nil (tree std)
      walk td@(send _ _ _ _)       = wv/leaf (base td tt)
      walk td@(recv _ _ _ _)       = wv/leaf (base td tt)
      walk td@(let′ _ _)           = wv/leaf (base td tt)
      walk td@(if _ _ _)           = wv/leaf (base td tt)
      walk td@(rec _ _)            = wv/leaf (base td tt)
      walk td@(var _)              = wv/leaf (base td tt)
      walk td@(end _)              = wv/leaf (base td tt)

      tree :
        ∀ {ξ}{Ξ : Vec Cls ξ}{G}
        → Γ & Δ & Ξ ⊢[ R ] Pr ∶ G
        → WaitV R L (Vofᶜ Ξ) (rep G)
      tree (skip-main td) = waitV/mono (λ ()) (walk td)
      tree (skip-step (_ , _ , st) ¬act k) =
        let _ , gr , _ = stepᶜ⇒ st
        in wv/step (λ act → ¬act (act⇒ᶜ act)) gr
             (λ gr′ → waitV/mono vofᶜ/cons (tree (k (step⇒ᶜ gr′))))
      tree (skip-cycle mem inT) =
        let X , e = ∈ᵛ⇒vofᶜ mem
        in wv/cycle (_ , (X , ~refl) , e) (∈Tᶜ⇒ inT)

  module _ {γ δ}{Γ : Vec Sort γ}{Δ : Vec Cls δ} where

    sendWait :
      ∀ {P Q Qs}{i : ℕ}{S E}{Pr : Proc γ δ}{G}
      → Γ ⊢e E ∶ S
      → Γ & Δ ⊢[ P ] Q ⇒ Qs ! i < E >∙ Pr ∶ [ G ]
      → WaitV P (SendL {Γ = Γ} {Δ = Δ} P Q Qs i S Pr) ∅S G
    sendWait etd = Walk.walk _ sendL/closed sendL/adv base
      where
        base :
          ∀ {G}(td : Γ & Δ ⊢[ _ ] _ ∶ G) → Base td → SendL _ _ _ _ _ _ (rep G)
        base (send fi gr etd′ td) _ with ⊢e-unique etd′ etd
        ... | refl =
          let u″ , gr′ , u″~ = evᶜ⇒ gr
          in first-inᶜ⇒ fi , u″ , gr′ , td/≐ ≐ᵛ-refl (~sym u″~) td

    recvWait :
      ∀ {n P Q R}{Br : Vec (Maybe (Proc (suc γ) δ)) n}{G}
      → Γ & Δ ⊢[ Q ] R ⇐ P ？· Br ∶ [ G ]
      → WaitV Q (RecvL {Γ = Γ} {Δ = Δ} P Q R Br) ∅S G
    recvWait {Br = Br} =
      Walk.walk _ (recvL/closed {Br = Br}) (recvL/adv {Br = Br})
        λ { (recv fi P∉ (c , _ , ex) conts) _ →
              let _ , gr , _ = evᶜ⇒ ex
              in first-inᶜ⇒ fi , (P∉ , _ , _ , _ , gr)
               , λ gr′ → conts (ev⇒ᶜ gr′) }

    varWait :
      ∀ {P}{X : Fin δ}{G}
      → Γ & Δ ⊢[ P ] v X ∶ [ G ]
      → WaitV P (Unskipped P (rep (lu Δ X) ~_)) ∅S G
    varWait =
      Walk.walk _ unskipped/~ unskipped/adv
        λ { (var eq) _ → _ , eq , _ , ε , ~refl }

    recWait :
      ∀ {P}{Pr : Proc γ (suc δ)}{G}
      → Γ & Δ ⊢[ P ] rec Pr ∶ [ G ]
      → WaitV P (Unskipped P (RecA {Γ = Γ} {Δ = Δ} {P = P} Pr)) ∅S G
    recWait {P = P} {Pr = Pr} =
      Walk.walk _ unskipped/~ unskipped/adv
        λ { (rec td _) _ → _ , td , _ , ε , ~refl }

    sendEWait :
      ∀ {P Q Qs}{i : ℕ}{E}{Pr : Proc γ δ}{G}
      → Γ & Δ ⊢[ P ] Q ⇒ Qs ! i < E >∙ Pr ∶ [ G ]
      → WaitV P (SendE {Γ = Γ} {Δ = Δ} P Q Qs i E Pr) ∅S G
    sendEWait =
      Walk.walk _ sendE/closed sendE/adv
        λ { (send (r∈ , _) gr etd td) _ →
              let u″ , gr′ , u″~ = evᶜ⇒ gr
              in r∈ , _ , u″ , etd , gr′ , td/≐ ≐ᵛ-refl (~sym u″~) td }

    recGWait :
      ∀ {P}{Pr : Proc γ (suc δ)}{G}
      → Γ & Δ ⊢[ P ] rec Pr ∶ [ G ]
      → WaitV P (RecG Pr) ∅S G
    recGWait = Walk.walk _ recG/closed recG/adv λ { (rec _ guarded) _ → guarded }

    ifEWait :
      ∀ {P E}{A B : Proc γ δ}{G}
      → Γ & Δ ⊢[ P ] ifp E then A else B ∶ [ G ]
      → WaitV P (IfE {Γ = Γ} E) ∅S G
    ifEWait = Walk.walk _ ifE/closed ifE/adv λ { (if etd _ _) _ → etd }

    endWait :
      ∀ {P}{G}
      → Γ & Δ ⊢[ P ] ∅ ∶ [ G ]
      → WaitV P (EndL P) ∅S G
    endWait = Walk.walk _ endL/closed endL/adv λ { (end out) _ → λ inT → out (∈T⇒ᶜ inT) }

    letEWait :
      ∀ {P E}{A : Proc (suc γ) δ}{G}
      → Γ & Δ ⊢[ P ] letp E in′ A ∶ [ G ]
      → WaitV P (LetE {Γ = Γ} E) ∅S G
    letEWait = Walk.walk _ letE/closed letE/adv λ { (let′ etd _) _ → _ , etd }

    ---------------------------------------------------------------------
    -- A `let` derivation gives its body's, at the same class.
    ---------------------------------------------------------------------

    mutual

      letBody :
        ∀ {S P E}{A : Proc (suc γ) δ}{G}
        → Γ ⊢e E ∶ S
        → Γ & Δ ⊢[ P ] letp E in′ A ∶ G
        → (S ∷ Γ) & Δ ⊢[ P ] A ∶ G

      letBody etd (let′ etd′ td) with ⊢e-unique etd′ etd
      ... | refl = td
      letBody etd (forward td run) = forward (letBody etd td) run
      letBody etd (skip std)       = skip (letBodyTree etd std)

      letBodyTree :
        ∀ {S ξ}{Ξ : Vec Cls ξ}{P E}{A : Proc (suc γ) δ}{G}
        → Γ ⊢e E ∶ S
        → Γ & Δ & Ξ ⊢[ P ] letp E in′ A ∶ G
        → (S ∷ Γ) & Δ & Ξ ⊢[ P ] A ∶ G

      letBodyTree etd (skip-main td) = skip-main (letBody etd td)
      letBodyTree etd (skip-step ex na k) =
        skip-step ex na (λ st → letBodyTree etd (k st))
      letBodyTree etd (skip-cycle mem inT) = skip-cycle mem inT

    ---------------------------------------------------------------------
    -- An `if` derivation gives each branch's, at the same class.
    ---------------------------------------------------------------------

    mutual

      ifBranch :
        ∀ (b : Bool){P E}{A B : Proc γ δ}{G}
        → Γ & Δ ⊢[ P ] ifp E then A else B ∶ G
        → Γ & Δ ⊢[ P ] (if b then A else B) ∶ G

      ifBranch true  (if _ ttd _)      = ttd
      ifBranch false (if _ _ ftd)      = ftd
      ifBranch b (forward td run)      = forward (ifBranch b td) run
      ifBranch b (skip std)            = skip (ifBranchTree b std)

      ifBranchTree :
        ∀ (b : Bool){ξ}{Ξ : Vec Cls ξ}{P E}{A B : Proc γ δ}{G}
        → Γ & Δ & Ξ ⊢[ P ] ifp E then A else B ∶ G
        → Γ & Δ & Ξ ⊢[ P ] (if b then A else B) ∶ G

      ifBranchTree b (skip-main td) = skip-main (ifBranch b td)
      ifBranchTree b (skip-step ex na k) =
        skip-step ex na (λ st → ifBranchTree b (k st))
      ifBranchTree b (skip-cycle mem inT) = skip-cycle mem inT


    endNotin :
      ∀ {P}{G}
      → Γ & Δ ⊢[ P ] ∅ ∶ [ G ]
      → ¬ P ∈T G

    endNotin td (_ , run , act) = endChase run act (endWait td)

  -- ══════════════════════════════════════════════════════════════════
  --  `⊢` ⟶ `⊢a`, at the largest set
  -- ══════════════════════════════════════════════════════════════════
  --
  -- Stated at the largest set, `Typed`; `alg/mono` gives every smaller one.
  -- Recursion on the process; `typBr` makes the branch structural.

  Typed : ∀ {γ δ} → Vec Sort γ → NProc γ δ → States δ
  Typed Γ (P ◂ Pr) (ws , G) = Γ & (classes ws) ⊢[ P ] Pr ∶ [ G ]

  -- `a/rec`'s entry set: the body typed at its own anchor.
  Entry : ∀ {γ δ} → Vec Sort γ → PartSet → Proc γ (suc δ) → States δ
  Entry Γ P Pr (ws , W) = Γ & (classes (W ∷ ws)) ⊢[ P ] Pr ∶ [ W ]

  -- A state after the receive of `ℓ`: the branch of `ℓ`, typed there.
  recvBr :
    ∀ {γ δ}{Γ : Vec Sort γ}{n P Q R}{Br : Vec (Maybe (Proc (suc γ) δ)) n}{ℓ U ws t}
    → (ws , t) ∈ Post R ((？ P) # ℓ < U >) (Front Q (Typed Γ (Q ◂ R ⇐ P ？· Br)))
    → ∃[ Pr ] Br ∋ ℓ ↦ Pr × (ws , t) ∈ Typed (U ∷ Γ) (Q ◂ Pr)

  recvBr {P = P}{Q}{R}{Br}
         (_ , ((_ , td , run) , _) , (α , eq , gr))
    with waitFind (recvWait td)
  ... | _ , (R∈ , _) , _
    with waitLeaf {Q} gr (_ , R∈ , _ , eq)
           (waitFollow (recvL/closed {Br = Br}) (recvL/adv {Br = Br})
              (recvWait td) (idle⇒unskip run))
  ... | _ , _ , k = k (α , eq , gr)

  -- Every such state types the same branch.
  recvAt :
    ∀ {γ δ}{Γ : Vec Sort γ}{n P Q R}{Br : Vec (Maybe (Proc (suc γ) δ)) n}{ℓ U Pr}
    → Br ∋ ℓ ↦ Pr
    → Post R ((？ P) # ℓ < U >) (Front Q (Typed Γ (Q ◂ R ⇐ P ？· Br)))
      ⊆ Typed (U ∷ Γ) (Q ◂ Pr)

  recvAt {Γ = Γ}{Q = Q}{U = U} br {ws , t} x∈
    with recvBr x∈
  ... | _ , br′ , td =
    subst (λ X → (ws , t) ∈ Typed (U ∷ Γ) (Q ◂ X)) (sym (∋-functional br br′)) td

  -- `bal`: `a/send` types the continuation after every step with `P`'s
  -- event, `send` after one; `send-det` makes them the same.
  module _ (bal : Balanced B) where
    open Balanced bal using (send-det)

    sendAt :
      ∀ {γ δ}{Γ : Vec Sort γ}{P Q Qs}{i : ℕ}{S E}{Pr : Proc γ δ}
      → Γ ⊢e E ∶ S
      → Post Q ((! Qs) # i < S >)
          (Front P (Typed Γ (P ◂ Q ⇒ Qs ! i < E >∙ Pr)))
        ⊆ Typed Γ (P ◂ Pr)

    sendAt {P = P}{Q}{Qs}{i = i}{E = E}{Pr} etd {ws , t}
      (_ , ((_ , td , run) , _) , (α , eq , gr))
      with waitFind (sendWait etd td)
    ... | _ , (Q∈ , _) , _
      with waitLeaf {P} gr (_ , Q∈ , _ , eq)
             (waitFollow sendL/closed sendL/adv (sendWait etd td)
               (idle⇒unskip run))
    ... | _ , _ , (α′ , eq′ , gr′) , td′
      with send-det gr gr′ eq eq′
    ...   | refl = typ/closed (step-deterministic gr′ gr) td′

    mutual

      typing⇒alg :
        ∀ {γ δ}{Γ : Vec Sort γ}{P}(Pr : Proc γ δ){ws G}
        → Γ & (classes ws) ⊢[ P ] Pr ∶ [ G ]
        → Γ ⊢a P ◂ Pr ∶ Typed Γ (P ◂ Pr)

      typing⇒alg (Q ⇒ Qs ! i < E >∙ Pr) td
        with waitFind (sendEWait td)
      ... | _ , Q∈ , _ , _ , etd , _ , cont =
        a/send Q∈ etd
          (λ td′ → waitV/leaf-mono (λ { (fi , _ , gr , _) → fi , _ , gr })
                     (sendWait etd td′))
          (alg/mono (sendAt etd) (typing⇒alg Pr cont))

      typing⇒alg (R ⇐ P ？· Br) td
        with waitFind (recvWait td)
      ... | _ , (R∈ , _) , _ =
        a/recv R∈
          (λ td′ → waitV/leaf-mono (λ { (fi , off , _) → fi , off })
                     (recvWait td′))
          (λ { (_ , x∈) →
               let Pr , br , w = recvBr {Br = Br} x∈
               in Pr , br , alg/mono (recvAt {Br = Br} br) (typBr Br br w) })

      typing⇒alg (letp E in′ A) td
        with waitFind (letEWait td)
      ... | _ , (S , etd) =
        a/let etd (alg/mono (letBody etd) (typing⇒alg A (letBody etd td)))

      typing⇒alg (ifp E then A else B) td
        with waitFind (ifEWait td)
      ... | _ , etd =
        a/if etd
          (alg/mono (ifBranch true)  (typing⇒alg A (ifBranch true td)))
          (alg/mono (ifBranch false) (typing⇒alg B (ifBranch false td)))

      typing⇒alg ∅ td = a/end endNotin

      typing⇒alg (v X) td =
        a/var λ { {ws , _} td′ →
          waitV/leaf-mono
            (λ { (a , e , rest) →
                 a , subst (_~ a) (cong rep (lookup-map X [_] ws)) e , rest })
            (varWait td′) }

      typing⇒alg {Γ = Γ}{P} (rec Pr) td
        with waitFind (recGWait td) | waitFind (recWait td)
      ... | _ , guarded | _ , _ , aW , _ =
        a/rec {𝒜 = Entry Γ P Pr} guarded
          (alg/mono (λ { {_ ∷ _ , _} (aW′ , W~s) → typ/closed W~s aW′ })
                    (typing⇒alg Pr aW))
          recWait

      typBr :
        ∀ {γ δ n}{Γ : Vec Sort γ}{Q ℓ Pr}
          (Br : Vec (Maybe (Proc (suc γ) δ)) n) → Br ∋ ℓ ↦ Pr → ∀ {U ws t}
        → (U ∷ Γ) & (classes ws) ⊢[ Q ] Pr ∶ [ t ]
        → (U ∷ Γ) ⊢a Q ◂ Pr ∶ Typed (U ∷ Γ) (Q ◂ Pr)

      typBr (just B ∷ Bs) here      w = typing⇒alg B w
      typBr (_ ∷ Bs)      (there p) w = typBr Bs p w

    -- ════════════════════════════════════════════════════════════════
    --  The boundary `Safety/` uses
    -- ════════════════════════════════════════════════════════════════

    td⇒at :
      ∀ {γ δ}{Γ : Vec Sort γ}{P}{Pr : Proc γ δ}{ws G}
      → Γ & (classes ws) ⊢[ P ] Pr ∶ [ G ]
      → Γ ⊢at P ◂ Pr ∶ (ws , G)

    td⇒at {Pr = Pr} td = _ , typing⇒alg Pr td , td
