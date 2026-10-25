{-# OPTIONS --guardedness #-}
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Vec hiding (_++_)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Utils
open import Definitions
open import Relation.Nullary.Decidable
  using (True ; False ; toWitnessFalse ; fromWitnessFalse ; fromWitness ; toWitness)
open import Relation.Nullary using (¬_ ; yes ; no)
open import Data.Maybe using (just ; nothing)
open import Data.Fin.Properties using () renaming (_≟_ to _≟f_)

module Examples.CounterExamples where
  open import Examples.SimpleGT (3)
  A : Part
  A = zero

  B : Part
  B = suc zero

  C : Part
  C = suc (suc zero)

  round : Global 0 mg
  round = A ⟶ B ∶[ 1 , tt ]
            (  s/bool ·· end
            ∷  s/bool ·· >> ( B ⟶ C ∶[ 0 , tt ] ( s/bool ·· end
                                                ∷ [])
                            )
            ∷ [])

  -----------------------------------------------------------------------------

  -- The processes below shoud not type, and they don't
  p/C2 : Proc 0 0
  p/C2 = Σ B ？[ [ s/bool ] ]· (Σ B ？[ [ s/bool ] ]· (∅ ∷ []) ∷ [])

  t/C/bad : [] & [] / >> round ↑ C ⊢p< mg > p/C2 → ⊥
  t/C/bad (t/recv R[ step/tl/I x x₁ ] conts) = ⊥-elim (x (inj₂ (_∈pr_.∈S refl)))
  t/C/bad (t/skip is-recv SK[ _ , _ , ii ] _) with ii ([ step/i zero , (λ{ (∈S ()) ; (∈R ()) }) ]► (■ , tt))
  t/C/bad (MPST.t/skip MPST.is-recv MPST.SK[ _ , _ , _ ] _) | _ , BTheory.■ , ()
  t/C/bad (MPST.t/skip MPST.is-recv MPST.SK[ _ , _ , _ ] _) | _ , (() BTheory.► fst) , snd

  p/C3 : Proc 0 0
  p/C3 = Σ A ？[ s/bool ∷ [] ]· (Σ B ？[ s/bool ∷ [] ]· (∅ ∷ []) ∷ [])

  t/C3/bad : [] & [] / >> round ↑ C ⊢p< mg > p/C3 → ⊥
  t/C3/bad (t/recv R[ step/tl/I x x₁ ] conts) = ⊥-elim (x (inj₁ (_∈pr_.∈S refl)))
  t/C3/bad (t/skip is-recv SK[ _ , _ , ii ] _) with ii (([ step/i zero , (λ{ (∈S ()) ; (∈R ()) }) ]► (■ , tt))) -- (tr/trans (step/i zero) (λ{ (∈S ()) ; (∈R ()) }) tr/refl)
  t/C3/bad (MPST.t/skip MPST.is-recv MPST.SK[ _ , _ , _ ] _) | _ , BTheory.■ , ()
  t/C3/bad (MPST.t/skip MPST.is-recv MPST.SK[ _ , _ , _ ] _) | _ , (() BTheory.► fst) , snd
  -- t/C3/bad (t/skip is-recv _ _) | _ , now () _
  -- t/C3/bad (t/skip is-recv _ _) | _ , [ () , _ ]► _

  p/C4 : Proc 0 0
  p/C4 = rec (v zero)

  td/C2 : [] & [] / >> round ↑ C ⊢p< mg > p/C4 → ⊥
  td/C2 (MPST.t/skip () x₁ conts)

  -----------------------------------------------------------------------------

  -- this can be typed, but it is no longer a problem (see td/C2 above)
  td/C2-bad : [] & >> round ∷ [] / >> round ↑ C ⊢p< ng > v zero
  td/C2-bad = t/var ~refl (■ , tt)

  -----------------------------------------------------------------------------

  -- No session can be typed against the following global type (global types
  -- of the paper, Definitions.GlobalTypesWPar):
  --
  --   G = μt. p → q { m0. r → s { m2. t }
  --                 ; m1. r → s { m2. t ; m3. t } }
  --
  -- Role r cannot be typed: it cannot act before p → q, because the branches
  -- disagree on the choices of r → s (see step/tl/I), and it cannot skip
  -- p → q, because r → s would become enabled out of thin air (Causal).
  module NoSession where
    import Definitions.GlobalTypesWPar (4) as W
    import Definitions.Actions (4) as A4
    open W.PreTypes
      using (μ ; var ; >> ; _⟶_∶[_]_ ; step/i ; step/tl/I ; step/unfold
            ; step/jn ; step/nil)
      renaming (Global to Global′)
    open W.GT-Wrapper using (s-do) renaming (step to step′)
    module T = MPST W.GT-Properties

    p q r s : Fin 4
    p = zero
    q = suc zero
    r = suc (suc zero)
    s = suc (suc (suc zero))

    r≢s : r ≢ s
    r≢s ()

    -- p → q : m0 | m1, and r → s : m2 | m3 (labels are positions)
    S₂ : Vec Sort 2
    S₂ = s/unit ∷ s/unit ∷ []

    G G₁ : Global′ 0 ng
    G = μ (p ⟶ q ∶[ S₂ ]
            ( just (>> (r ⟶ s ∶[ S₂ ] (just (var zero) ∷ nothing ∷ [])))
            ∷ just (>> (r ⟶ s ∶[ S₂ ] (just (var zero) ∷ just (var zero) ∷ [])))
            ∷ []))
    G₁ = >> (r ⟶ s ∶[ S₂ ] (just G ∷ nothing ∷ []))

    G̃ G̃₁ : T.Behav
    G̃  = G , tt
    G̃₁ = G₁ , tt

    -- Every transition involving r is an r → s
    record rs-only (B : T.Behav) : Set where
      constructor rs
      field rs-hd : ∀ {α B′} → B T.-< α >-> B′ → r A4.∈α α
                    → proj₁ α ≡ (r A4.⟶ s # S₂)
    open rs-only

    -- Every transition of G is a p → q
    no-fifth : ∀ h → (p A4.⟶ q # S₂) A4.⋔ h → (r A4.⟶ s # S₂) A4.⋔ h → ⊥
    no-fifth (zero A4.⟶ _ # _) d _ = d (inj₁ (A4.∈S refl))
    no-fifth (suc zero A4.⟶ _ # _) d _ = d (inj₂ (A4.∈S refl))
    no-fifth (suc (suc zero) A4.⟶ _ # _) _ d = d (inj₁ (A4.∈S refl))
    no-fifth (suc (suc (suc zero)) A4.⟶ _ # _) _ d = d (inj₂ (A4.∈S refl))

    G-hd : ∀ {α G′} → step′ G α G′ → proj₁ α ≡ (p A4.⟶ q # S₂)
    G-hd (s-do (step/unfold (step/i _ _))) = refl
    G-hd (s-do (step/unfold (step/tl/I d _ (step/jn (step/tl/I d′ _ _) _))))
      = ⊥-elim (no-fifth _ d d′)
    G-hd (s-do (step/unfold (step/tl/I _ _
      (step/jn (step/i _ _) (step/jn (step/tl/I d _ _) _)))))
      = ⊥-elim (d (inj₁ (A4.∈S refl)))

    ∉pq : ∀ {P} → P ≢ p → P ≢ q → ¬ (P A4.∈pr (p A4.⟶ q # S₂))
    ∉pq P≢p _ (A4.∈S eq) = P≢p (sym eq)
    ∉pq _ P≢q (A4.∈R eq) = P≢q (sym eq)

    r∉G : r T.∉tr G̃
    r∉G (T.∈-tr st r∈) = ∉pq (λ ()) (λ ()) (subst (r A4.∈pr_) (G-hd st) r∈)

    s∉G : s T.∉tr G̃
    s∉G (T.∈-tr st s∈) = ∉pq (λ ()) (λ ()) (subst (s A4.∈pr_) (G-hd st) s∈)

    G→G₁ : G̃ T.-< p A4.⟶ q # S₂ , zero >-> G̃₁
    G→G₁ = s-do (step/unfold (step/i zero tt))

    G₁→G : G̃₁ T.-< r A4.⟶ s # S₂ , zero >-> G̃
    G₁→G = s-do (step/i zero tt)

    G₁-rs : rs-only G̃₁
    G₁-rs = rs (λ {α} {B′} → hd {α} {B′})
      where
        hd : ∀ {α B′} → G̃₁ T.-< α >-> B′ → r A4.∈α α
           → proj₁ α ≡ (r A4.⟶ s # S₂)
        hd (s-do (step/i _ _)) _ = refl
        hd (s-do (step/tl/I d _ _)) r∈ = ⊥-elim (d (inj₁ r∈))

    -- States where r cannot be typed
    record Stuck (B : T.Behav) : Set where
      field
        st-noact  : r T.∉tr B
        st-causal : ¬ T.Causal B r s
        st-next   : Σ[ B′ ∈ T.Behav ] (B T.~< r >~> B′) × rs-only B′
    open Stuck

    stuck-G : Stuck G̃
    stuck-G .st-noact = r∉G
    stuck-G .st-causal c
      = c (T.■ , tt) r∉G
          ((G→G₁ T.► T.■) , (r∉G , T.∈-tr G₁→G (A4.∈S refl))
                      , (s∉G , T.∈-tr G₁→G (A4.∈R refl)))
    stuck-G .st-next = G̃₁ , ((G→G₁ T.► T.■) , (r∉G , T.∈-tr G₁→G (A4.∈S refl))) , G₁-rs

    -- Stuck states are closed under transitions not involving r, backwards
    stuck-back₁ : ∀ {B B₁ α} → B T.-< α >-> B₁ → ¬ r A4.∈α α → Stuck B₁ → Stuck B
    stuck-back₁ {B} {B₁} {α} gr r∉α st = record
      { st-noact  = r∉B
      ; st-causal = λ c → st-causal st (T.ntac-step ((gr T.► T.■) , r∉α , tt) c)
      ; st-next   = next (st-next st)
      }
      where
        r∉B : r T.∉tr B
        r∉B (T.∈-tr {X} gr′ r∈)
          with BT-Prop.indep? W.GT-Properties {G₁ = B} {G₂ = X} {G₃ = B₁} gr′ gr
        ... | inj₁ ii
          = st-noact st
              (T.∈-tr {∈-G′ = BT-Prop.◇-join W.GT-Properties {G = B} {G₁ = X} {G₂ = B₁} gr′ gr ii}
                (BT-Prop.◇-r W.GT-Properties {G = B} {G₁ = X} {G₂ = B₁} gr′ gr ii) r∈)
        ... | inj₂ eq = r∉α (subst (r A4.∈pr_) eq r∈)

        next : Σ[ B′ ∈ T.Behav ] (B₁ T.~< r >~> B′) × rs-only B′
          → Σ[ B′ ∈ T.Behav ] (B T.~< r >~> B′) × rs-only B′
        next (B′ , (tr , sk) , only) = B′ , ((gr T.► tr) , (r∉B , sk)) , only

    stuck-back : ∀ {B B′} → B T.=<¬ r >=> B′ → Stuck B′ → Stuck B
    stuck-back (T.■ , _) st = st
    stuck-back ((gr T.► tr) , r∉α , r∉tr) st
      = stuck-back₁ gr r∉α (stuck-back (tr , r∉tr) st)

    ᵣ→ : ∀ {B B′} → B T.=<¬ r >=>ᵣ B′ → B T.=<¬ r >=> B′
    ᵣ→ T.rt/refl = T.■ , tt
    ᵣ→ (T.rt/trans tr (gr , r∉α)) = T.tr/cat (ᵣ→ tr) ((gr T.► T.■) , r∉α , tt)

    sk-last : ∀ {P B B′} (tr : B T.~~> B′) → T.skippable P tr → P T.∈tr B′
    sk-last T.■ x = x
    sk-last (_ T.► tr) (_ , x) = sk-last tr x

    -- Once r is enabled, it can only interact with s
    comm-only : ∀ {γ δ g P Q B Pr}{Γ : Vec Sort γ}{Δ : Vec T.Behav δ}
      → P ≡ r → r T.∈tr B → rs-only B → T.is-comm Q Pr → Q ≢ s
      → ¬ (Γ T.& Δ / B ↑ P ⊢p< g > Pr)
    comm-only eq _ only T.is-send Q≢s (T.t/send {G' = B′} gr _ _)
      = Q≢s (cong A4.HeadAct.preceiver (rs-hd only {B′ = B′} gr (A4.∈S eq)))
    comm-only eq _ only T.is-recv _ (T.t/recv (T.R[_] {B′} rt) _)
      = r≢s (trans (sym eq)
          (cong A4.HeadAct.preceiver (rs-hd only {B′ = B′} rt (A4.∈R eq))))
    comm-only eq r∈ _ _ _ (T.t/skip _ T.SK[ _ , noact , _ ] _)
      = noact (subst (T._∈tr _) (sym eq) r∈)

    data NoVar : ∀ {δ} → Vec T.Behav δ → Guard → Set where
      nv/mg  : ∀ {δ} {Δ : Vec T.Behav δ} → NoVar Δ mg
      nv/nil : ∀ {g} → NoVar [] g

    stuck : ∀ {γ δ g P B Pr}{Γ : Vec Sort γ}{Δ : Vec T.Behav δ}
      → P ≡ r → Stuck B → NoVar Δ g → ¬ (Γ T.& Δ / B ↑ P ⊢p< g > Pr)
    stuck eq st _ (T.t/send {G' = B′} gr _ _)
      = st-noact st (T.∈-tr {∈-G′ = B′} gr (A4.∈S eq))
    stuck eq st _ (T.t/recv (T.R[_] {B′} rt) _)
      = st-noact st (T.∈-tr {∈-G′ = B′} rt (A4.∈R eq))
    stuck {B = B} eq st _ (T.t/skip {Q = Q} ic T.SK[ caus , _ , _ ] conts)
      with Q ≟f s | st-next st
    ... | yes refl | _ = st-causal st (subst (λ X → T.Causal B X s) eq caus)
    ... | no Q≢s | B′ , tr , only
      = comm-only eq (sk-last (proj₁ tr) (proj₂ tr)) only ic Q≢s
          (conts (subst (λ X → B T.~< X >~> B′) (sym eq) tr))
    stuck eq st nv (T.t/if _ d _) = stuck eq st nv d
    stuck {B = B} eq st _ (T.t/rec tr d)
      = stuck eq (stuck-back (ᵣ→ (subst (λ X → _ T.=<¬ X >=>ᵣ B) eq tr)) st) nv/mg d
    stuck _ _ nv/nil (T.t/var {X = ()} _ _)
    stuck {B = B} eq st _ (T.t/end nP)
      = nP (subst (λ X → X T.∈T B) (sym eq) (T.∈-last (proj₁ (proj₂ (st-next st)))))

    r-untypable : ∀ {Pr} → ¬ ([] T.& [] / G̃ ↑ r ⊢p< ng > Pr)
    r-untypable = stuck refl stuck-G nv/nil

    no-session : ∀ M → ¬ (T.⊢s M ∶ G̃)
    no-session M ⊢M = r-untypable (⊢M r)
