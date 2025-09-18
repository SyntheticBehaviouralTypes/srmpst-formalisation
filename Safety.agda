{-# OPTIONS --guardedness #-}

open import Data.Maybe
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤ ; tt)
open import Data.Bool using (T)
open import Data.Nat renaming (_≟_ to _≟n_ ; _<_ to _<ℕ_ ; _≤_ to _≤ℕ_)
open import Data.Nat.Properties
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Fin hiding (_+_ ; _-_) renaming (_≟_ to _≟f_)
open import Data.Vec hiding (_++_)
open import Data.Vec.Properties
open import Data.Vec.Relation.Unary.Any using (Any; here; there)
open import Data.Product
open import Data.Sum
open import Data.Maybe using (Maybe ; just)
open import Function.Base using (id; _∘_)
open import Induction.WellFounded
open import Relation.Nullary.Decidable using (isYes ; ¬?)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong-app; subst ; ≢-sym)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Relation.Nullary
  using (Dec; yes; no ; ¬_ ; _because_ ; ofʸ ; ofⁿ ; contraposition)
open import Relation.Nullary.Decidable
  using ( True ; False ; toWitness ; fromWitness
        ; fromWitnessFalse ; toWitnessFalse ; ⌊_⌋ ; ¬?
        )

open import Utils
open import Definitions
import SubstitutionProperties

module Safety {N : ℕ}{B : BTheory N}(BP : BT-Prop B) where
  open BT-Prop BP
  open module SP = SubstitutionProperties(BP)
  open SP.M
  open SP.M.Subst

  -- session replacement preserves typing
  session-update-preservation : ∀{M G P Pr} -> ⊢s M ∶ G
    -> [] & [] & [] / G ↑ P ⊢p< ng > Pr -> ⊢s M [ P ]≔ Pr ∶ G
  session-update-preservation {M = M} {P = P}{Pr = Pr} sd pd Q with P ≟f Q
  ... | yes refl rewrite lookup∘update Q M Pr = pd
  ... | no ¬p rewrite lookup∘update′ (≢-sym ¬p) M Pr = sd Q

  _update_<-|_ : ∀{G P Pr} -> (M : Session) -> ⊢s M ∶ G
    -> [] & [] & [] / G ↑ P ⊢p< ng > Pr -> ⊢s M [ P ]≔ Pr ∶ G
  M update std <-| td  = session-update-preservation {M = M} std td

  td/lookup : ∀ {M G P Pr}
    → ⊢s M ∶ G
    → M [ P ]= Pr
    → [] & [] & [] / G ↑ P ⊢p< ng > Pr
  td/lookup {P = P} ts luP with ts P
  ... | ptd rewrite reflect-lookup luP = ptd

  open Pskip
  trecv/first : ∀{ G P Q I}{S : Vec Sort (suc I)}{Br}
    → [] & [] & [] / G ↑ Q ⊢p< ng > (Σ P ？[ S ]· Br)
    → ∀ {α G'} → (gr : G -< α >-> G') → (P∈α : Q ∈α α)
    → P ∈α α
  trecv/first (t/recv x _) gr Q∈α with recv-act-eq x gr Q∈α
  ... | refl = ∈S refl
  trecv/first (t/skip-next s _) gr P∈α = ⊥-elim (s-nonact s gr P∈α)

  trecv/P∉tr : ∀{ G P Q I}{S : Vec Sort (suc I)}{Br}
    → (td : [] & [] & [] / G ↑ Q ⊢p< ng > (Σ P ？[ S ]· Br))
    → P ∉tr G → Q ∉tr G
  trecv/P∉tr td Q∉tr (∈-tr tr n)
    = Q∉tr (∈-tr tr (trecv/first td tr n))

  -- open _∈tr_
  -- tcomm/skip : ∀{ G P Q I}{S : Vec Sort (suc I)}{i E Br Pr G' }
  --   → (∀ {G'} → G ~< Q >~> G' → [] & [] & [] / G' ↑ Q ⊢p< ng > (Σ P ？[ S ]· Br))
  --   → (∀ {G'} → G ~< P >~> G' → [] & [] & [] / G' ↑ P ⊢p< ng > (Q ! I , i < E >∙ Pr))
  --   → (tr : G ~< P >~> G') → skippable Q (tr .proj₁)
  -- tcomm/skip {P = P} Ky Kx (■ , Px) with (Kx (■ , Px))
  -- ... | t/send gr _ _ = ∈-tr gr (∈R refl)
  -- ... | MPST.t/skip-next x ktd = ⊥-elim
  --   (MPST.Pskip.s-nonact x (BTheory._∈tr_.∈-step Px)
  --    (BTheory._∈tr_.∈-prf Px))
  -- tcomm/skip {P = P} Ky Kx (x ► tr , Px , sk) = trecv/P∉tr {!   !} {!   !} , {!   !}
  --   -- = (Py , tcomm/skip (Ky ∘ [ x , Py ]► ) (Kx ∘ [ x , Px ]►) (tr , sk))
  --   -- where
  --     -- Py = trecv/P∉tr (Ky (■ , ∈-tr x (∈-prf {! Px  !}))) Px -- trecv/P∉tr Ky Px

  open HeadAct
  tcomm/sorts/same : ∀{G p S Br i G'}{ξ}{Ξ : Vec Behav ξ}
    → (td : [] & [] & Ξ / G ↑ preceiver p ⊢p< ng > (Σ psender p ？[ S ]· Br) )
    → (gr : G -< p , i >-> G')
    → S ≡ sorts p
  tcomm/sorts/same {p = P ⟶ Q # S'} (t/recv x conts) gr
    with recv-act-eq x gr (∈R refl)
  ... | refl = refl
  tcomm/sorts/same (t/skip-next s _) gr = ⊥-elim (s-nonact s gr (∈R refl))
  tcomm/sorts/same (t/skip-close s _) gr = ⊥-elim (s-nonact s gr (∈R refl))

  next-action : ∀{G G' Q} → (ty : G ~~> G') → skippable Q ty
    → ∃[ α ] ∃[ G' ] G -< α >-> G'
  next-action BTheory.■ (BTheory.∈-tr ∈-step ∈-prf) = _ , _ , ∈-step
  next-action (x BTheory.► ty) sk = _ , _ , x

  skippable-send-recv : ∀{G G' P Q I i E}{S : Vec Sort (suc I)}{Br Pr}
    → (tx : G ~~> G')
    → [] & [] & [] / G ↑ Q ⊢p< ng > (Σ P ？[ S ]· Br)
    → [] & [] & [] / G ↑ P ⊢p< ng > (Q ! I , i < E >∙ Pr)
    → skippable P tx -> ∃[ G″ ] Σ[ ty ∈ G ~~> G″ ] tr-indep (P ⟶ Q # S , i) ty
  skippable-send-recv ■ tdq (t/send gr etd tdp) (∈-tr ∈s ∈p)
    rewrite tcomm/sorts/same tdq gr = _ , ((gr ► ■) , refl)
  skippable-send-recv ■ tdq (t/skip-next x _) (∈-tr ∈s ∈p)
    = ⊥-elim (s-nonact x ∈s ∈p)
  skippable-send-recv (x ► tx) tdq tdp (P∉G , sktx) with trecv/P∉tr tdq P∉G
  ... | Q∉G with skippable-send-recv tx
                   (unrelated/step tdq x (Q∉G ∘ (∈-tr x)))
                   (unrelated/step tdp x (P∉G ∘ (∈-tr x)))
                   sktx
  ... | _ , tr@(_ ► _) , ii
    = _ , x ► tr
    , ii-disj (λ{ (inj₁ p) → P∉G (∈-tr x p)
                ; (inj₂ p) → Q∉G (∈-tr x p) })
    , ii

  open _∥ₕ_
  indep-send-recv : ∀{G P Q I i E}{S : Vec Sort (suc I)}{Br Pr}
    → [] & [] & [] / G ↑ Q ⊢p< ng > (Σ P ？[ S ]· Br)
    → [] & [] & [] / G ↑ P ⊢p< ng > (Q ! I , i < E >∙ Pr)
    → ∀ {G'} (tx : G ~~> G')
    → tr-indep₁ (P ⟶ Q # S , i) tx
    → ∃[ G″ ] Σ[ ty ∈ G' ~~> G″ ] tr-indep (P ⟶ Q # S , i) ty
  indep-send-recv tdq (t/send gr etd tdp) ■ tt
    rewrite tcomm/sorts/same tdq gr = _ , gr ► ■ , refl
  indep-send-recv (t/recv gr conts) (t/skip-next x ktd) ■ tt
    = ⊥-elim (s-nonact x gr (∈S refl))
  indep-send-recv tdx tdy@(t/skip-next [ _ & _ & ty & sn ] _) ■ _
    = skippable-send-recv ty tdx tdy sn
  indep-send-recv tdq (t/send gr etd tdp) (x ► tx)  (ix@(ii-≡snd refl _) , ii)
    rewrite tcomm/sorts/same tdq gr
    = diamond* (◇-r gr x (Indep/gen ix)) tx ii
  indep-send-recv tdq (t/skip-next x₁ ktd) (x ► tx) (ii-≡snd refl nQ , ii)
    = ⊥-elim (s-nonact x₁ x (∈S refl))
  indep-send-recv tdq tdp (x ► tx) (ii-disj ix , ii)
    = indep-send-recv
           (unrelated/step tdq x (ix ∘ inj₂))
           (unrelated/step tdp x (ix ∘ inj₁)) tx ii

  open _∈tr_
  tcomm/steps : ∀{ G P Q I i E Pr S Br }
    → [] & [] & [] / G ↑ P ⊢p< ng > (Q ! I , i < E >∙ Pr)
    → [] & [] & [] / G ↑ Q ⊢p< ng > (Σ P ？[ S ]· Br)
    → ∃[ G' ] G -< P ⟶ Q # S , i >-> G'
  tcomm/steps (t/send gr x etd) td rewrite tcomm/sorts/same td gr = _ , gr
  tcomm/steps (t/skip-next s _) (t/recv x _)
    = ⊥-elim (s-nonact s x (∈S refl))
  tcomm/steps tdx@(t/skip-next [ is-send & nx & tx & sx ] Kx)
              tdy@(t/skip-next [ is-recv & ny & ty & sn ] Ky)
    = ⊥-elim (nx (full-comm (next-action tx sx .proj₂ .proj₂)
                            (indep-send-recv tdy tdx) .proj₂)
                 (∈S refl))
    -- alternatively, just produce the transition -- maybe we can remove te "non-active" requirement?
    -- = full-comm (next-action tx sx .proj₂ .proj₂)
    --             (indep-send-recv tdy tdx)

  -- The syntactic forms that a sending process has
  data TSend/inv P G (Pr : Proc 0 0) : Set where
    TSend/rec : ∀ Pr' → Pr ≡ rec Pr' → TSend/inv P G Pr
    TSend/if : ∀ E Pr' Pr''
      → [] ⊢e E ∶ s/bool → Pr ≡ ifp E then Pr' else Pr'' → TSend/inv P G Pr
    TSend/send : ∀ Q {I S E Pr' G'}{i : Fin (suc I)}
      → [] ⊢e E ∶ lookup S i
      → G -< P ⟶ Q # S , i >-> G'
      → Pr ≡ Q ! I , i < E >∙ Pr' → TSend/inv P G Pr

  tsend/proc/inv : ∀{G G' P Q I S Pr}{i : Fin (suc I)}
    → G -< P ⟶ Q # S , i >-> G'
    → [] & [] & [] / G ↑ P ⊢p< ng > Pr
    → TSend/inv P G Pr
  tsend/proc/inv gr (t/send gr₁ etd td)
    = TSend/send _ etd gr₁ refl
  tsend/proc/inv gr (t/recv gr' _) with recv-act-eq gr' gr (∈S refl)
  ... | refl = ⊥-elim (snd≢rcv gr refl)
  tsend/proc/inv gr (t/if etd td td₁) = TSend/if _ _ _ etd refl
  tsend/proc/inv gr (t/rec _ _) = TSend/rec _ refl
  tsend/proc/inv gr (t/end p∉g)
    = ⊥-elim (p∉g (in/α gr (∈S refl)))
  -- tsend/proc/inv gr (t/skip x₁ SK[ _ , f , _ ] _) = ⊥-elim (f (∈-tr gr (∈S refl)))
  tsend/proc/inv gr (t/skip-next x ktd) = ⊥-elim (s-nonact x gr (∈S refl))

  tsend/inv : ∀{ G G' P Q I i E Pr S }
    → [] & [] & [] / G ↑ P ⊢p< ng > (Q ! I , i < E >∙ Pr)
    → G -< P ⟶ Q # S , i >-> G'
    → ([] ⊢e E ∶ lookup S i) × ([] & [] & [] / G' ↑ P ⊢p< ng > Pr)
  tsend/inv (t/send gr₁ etd td) gr with recv-act-eq gr₁ gr (∈R refl)
  ... | refl rewrite step-det gr gr₁ = etd , td
  tsend/inv (t/skip-next x ktd) gr = ⊥-elim (s-nonact x gr (∈S refl))

  trecv/inv : ∀{ G G' P Q I E Br S}{i : Fin (suc I)}
    → [] & [] & [] / G ↑ Q ⊢p< ng > (Σ P ？[ S ]· Br)
    → [] ⊢e E ∶ lookup S i
    → G -< P ⟶ Q # S , i >-> G'
    → [] & [] & [] / G' ↑ Q ⊢p< ng > ([ E / zero ]e lookup Br i)
  trecv/inv (t/recv x conts)  etd gr = expr-subst-lemma etd (conts gr)
  trecv/inv (t/skip-next x ktd) _ gr = ⊥-elim (s-nonact x gr (∈R refl))

  t/if/inv : ∀{G P g E Pr Pr' Pr''}
    → Pr ≡ ifp E then Pr' else Pr''
    → [] & [] & [] / G ↑ P ⊢p< g > Pr
    → ([] ⊢e E ∶ s/bool)
    × ([] & [] & [] / G ↑ P ⊢p< g > Pr')
    × ([] & [] & [] / G ↑ P ⊢p< g > Pr'')
  t/if/inv refl (t/if e x y) = e , x , y

  -- Why does Agda totality checker accept the below?
  -- I thought we'd need to massage the definitions, do induction on the
  -- sequence of steps before t/rec is used ...
  unfold/pres : ∀ {γ}{Γ : Vec Sort γ}{G P Pr} ->
      (td :  Γ & [] & [] / G ↑ P ⊢p< ng > rec Pr) →
      Γ & [] & [] / G ↑ P ⊢p< mg > ([ rec Pr / zero ]pr Pr)
  unfold/pres (t/rec rt/refl td) = proc-subst-lemma td (t/rec rt/refl td)
  unfold/pres (t/rec (rt/trans br (gR , nP)) td)
    = unrelated/step (unfold/pres (t/rec br td)) gR nP

  upd-pres : ∀{M G P Q Pr Pr'}
    → (∀ R → R ≢ P → R ≢ Q → [] & [] & [] / G ↑ R ⊢p< ng > lookup M R)
    → [] & [] & [] / G ↑ P ⊢p< ng > Pr
    → [] & [] & [] / G ↑ Q ⊢p< ng > Pr'
    → ⊢s M [ P ]≔ Pr [ Q ]≔ Pr' ∶ G
  upd-pres {M}{G}{P}{Q}{Pr}{Pr'} rtd ptd qtd R with R ≟f Q
  ... | yes refl rewrite lookup∘update R (M [ P ]≔ Pr) Pr' = qtd
  ... | no rofl rewrite lookup∘update′ rofl (M [ P ]≔ Pr) Pr' with R ≟f P
  ... | yes refl rewrite lookup∘update R M Pr = ptd
  ... | no  rafl rewrite lookup∘update′ rafl M Pr = rtd R rafl rofl

  safety : ∀{G M M' α}
    → ⊢s M ∶ G -> M [ just α ]⇒ M' → ∃[ G' ] G -< α >-> G' × (⊢s M' ∶ G')
  safety {G = G} {M = M} std (s/comm {S = S}{i = i} P Q Psnd e⇓v Precv) =
    let etd , ptd' = tsend/inv ptd (red .proj₂)
        vtd = exp-pres etd e⇓v
        qtd' = trecv/inv qtd (te/val vtd) (red .proj₂)
        rtd' = td-other (red .proj₂)
    in _ , red .proj₂ , (upd-pres {M = M} rtd' ptd' qtd')
    where
      ptd = td/lookup std Psnd
      qtd = td/lookup std Precv
      red = tcomm/steps ptd qtd
      td-other : ∀ {G'} → (rt : G -< P ⟶ Q # S , i >-> G')
        → ∀ R → R ≢ P → R ≢ Q
        → [] & [] & [] / G' ↑ R ⊢p< ng > lookup M R
      td-other rt R x y
        = unrelated/step (std R) rt
                         (λ{ (∈S z) → x (sym z) ; (∈R z) → y (sym z)})

  preservation : ∀{G M M' } → ⊢s M ∶ G -> M [ nothing ]⇒ M' → ⊢s M' ∶ G
  preservation {G = G} {M = M}{M' = M'} std (s/if/true P Ptt e⇓true)
    with t/if/inv refl (td/lookup std Ptt)
  ... | _ , ptd , _ = M update std <-| ptd
  preservation {G = G} {M = M}{M' = M'} std (s/if/false P Ptt e⇓false)
    with t/if/inv refl (td/lookup std Ptt)
  ... | _ , _ , ptd = M update std <-| ptd
  preservation {G} {M}{M'} std (s/rec P Prec) with std P
  ... | ptd rewrite reflect-lookup Prec
    = M update std <-| t/> (unfold/pres ptd)

  old-preservation : ∀{G M M' α }
    → ⊢s M ∶ G -> M [ α ]⇒ M' → ∃[ G' ] G ===> G' × (⊢s M' ∶ G')
  old-preservation {α = just _} std td with safety std td
  ... | _ , gr , td = _ , ([ gr , tt ]► (■ , tt)) , td
  old-preservation {α = nothing} std td with preservation std td
  ... | td = _ , (■ , tt) , td

  typing/∈T : ∀ {δ}{Δ : Vec Behav δ}{G P Pr}
    → [] & Δ & [] / G ↑ P ⊢p< mg > Pr → P ∈T G
  typing/∈T (t/send gr _ _) = in/α gr (∈S refl)
  typing/∈T (t/recv gr _) = in/α gr (∈R refl)
  typing/∈T (t/if _ x _) = typing/∈T x
  typing/∈T (t/skip-next sk k) = ∈-last (s-activ sk , s-skippable sk)

  tend/done : ∀ {G P Pr} → ¬ (P ∈T G) → [] & [] & [] / G ↑ P ⊢p< ng > Pr
    → done/proc Pr
  tend/done n (t/if etd td td₁) = done-if (tend/done n td) (tend/done n td₁)
  tend/done n (t/end _) = done-∅
  tend/done n (t/send gr td etd)
    = ⊥-elim (n (in/α gr (∈S refl)))
  tend/done n (t/recv gr conts)
    = ⊥-elim (n (in/α gr (∈R refl)))
  -- NOTES: we need to unfold to expose the <mg> derivation with empty
  -- environments
  tend/done n (t/rec x td) = ⊥-elim (n (typing/∈T (unfold/pres (t/rec x td))))
  tend/done n (t/skip-next s K)
    = ⊥-elim (n (∈-last (s-activ s , s-skippable s)))
    -- = ⊥-elim (n (∈-last (a (■ , tt) .proj₂)))

  -- The syntactic forms that a sending process has
  data TRecv/inv P {I} (S : Vec Sort (suc I)) (Pr : Proc 0 0) : Set where
    TRecv/rec : ∀ Pr' → Pr ≡ rec Pr' → TRecv/inv P S Pr
    TRecv/if : ∀ E Pr' Pr'' → [] ⊢e E ∶ s/bool → Pr ≡ ifp E then Pr' else Pr''
      → TRecv/inv P S Pr
    TRecv/recv : ∀ Br → Pr ≡ Σ P ？[ S ]· Br → TRecv/inv P S Pr

  trecv/proc/inv : ∀{G G' P Q I S Pr}{i : Fin (suc I)}
    → G -< P ⟶ Q # S , i >-> G'
    → [] & [] & [] / G ↑ Q ⊢p< ng > Pr
    → TRecv/inv P S Pr
  trecv/proc/inv gr (t/recv gr₁ conts) with recv-act-eq gr gr₁ (∈R refl)
  ... | refl = TRecv/recv _ refl
  trecv/proc/inv gr (t/send gr₁ _ _) with recv-act-eq gr gr₁ (∈S refl)
  ... | refl = ⊥-elim (snd≢rcv gr refl)
  trecv/proc/inv gr (t/if etd td td₁) = TRecv/if _ _ _ etd refl
  trecv/proc/inv gr (t/rec x td) = TRecv/rec _ refl
  trecv/proc/inv gr (t/end p∉g) = ⊥-elim (p∉g (in/α gr (∈R refl)))
  trecv/proc/inv gr (t/skip-next x conts) = ⊥-elim (s-nonact x gr (∈R refl))

  data Inv-td G P Pr : Set where
    td-red : ∀{α G′} → G -< α >-> G′ → Inv-td G P Pr
    td-if : ∀{E}{Pr′ Pr″ : Proc 0 0} → [] ⊢e E ∶ s/bool
      → Pr ≡ ifp E then Pr′ else Pr″ → Inv-td G P Pr
    td-rec : ∀{Pr′} → Pr ≡ rec Pr′ → Inv-td G P Pr
    td-end : P ∉T G → Inv-td G P Pr

  td-inv : ∀{G Pr} P → [] & [] & [] / G ↑ P ⊢p< ng > Pr → Inv-td G P Pr
  td-inv P (t/send x _ _) = td-red x
  td-inv P (t/recv x _) = td-red x
  td-inv P (t/skip-next a _) with s-activ a | s-skippable a
  ... | ■ | ∈-tr x _ = td-red x
  ... | x ► _ | _ = td-red x
  td-inv P (t/if etd x x₁) = td-if etd refl
  td-inv P (t/rec x x₁) = td-rec refl
  td-inv P (t/end x) = td-end x

  data Inv-lv G {I} (Ps : Vec Part I) : Set where
    lv-red : ∀{α G′} → G -< α >-> G′ → Inv-lv G Ps
    lv-end : (∀ i → lookup Ps i ∉T G) → Inv-lv G Ps

  get-mg-act : ∀ {γ δ ξ G} {P : Part}{Γ : Vec Sort γ}{Δ : Vec Behav δ}
               {Ξ : Vec Behav ξ}{Pr} (x : Γ & Δ & Ξ / G ↑ P ⊢p< mg > Pr) →
               ∃-syntax (λ G' → ∃-syntax (λ α → G -< α >-> G'))
  get-mg-act (t/send gr etd x) = _ , _ , gr
  get-mg-act (t/recv x conts) = _ , _ , x
  get-mg-act (t/if etd x x₁) = get-mg-act x
  get-mg-act (MPST.t/skip-next [ _ & _ & ■ & ∈-tr x _ ] _) = _ , _ , x
  get-mg-act (MPST.t/skip-next [ _ & _ & x ► _ & _ ] _) = _ , _ , x
  get-mg-act (MPST.t/skip-close [ _ & _ & ■ & ∈-tr x _ ] _) = _ , _ , x
  get-mg-act (MPST.t/skip-close [ _ & _ & x ► _ & _ ] _) = _ , _ , x

  done-or-step : ∀{γ g P Pr G}{Γ : Vec Sort γ}
    → Γ & [] & [] / G ↑ P ⊢p< g > Pr
    → P ∉T G ⊎ ∃[ G' ] ∃[ α ] G -< α >-> G'
  done-or-step (t/send gr etd x) = inj₂ (_ , _ , gr)
  done-or-step (t/recv x conts) = inj₂ (_ , _ , x)
  done-or-step (t/if etd x x₁) with done-or-step x
  ... | inj₁ x₂ = inj₁ x₂
  ... | inj₂ y  = inj₂ y
  done-or-step td@(t/rec gr x) = inj₂ (get-mg-act (unfold/pres td))
  done-or-step (t/end x) = inj₁ x
  done-or-step (t/skip-next [ _ & _ & ■ & ∈-tr x _ ] ktd) = inj₂ (_ , _ , x)
  done-or-step (t/skip-next [ _ & _ & x ► _ & _ ] ktd) = inj₂ (_ , _ , x)

  lv-inv : ∀{G M I} (Ps : Vec Part I) → ⊢s M ∶ G → Inv-lv G Ps
  lv-inv [] x = lv-end (λ ())
  lv-inv {M = M} (P ∷ Ps) x with done-or-step (x P)
  lv-inv {M = M} (P ∷ Ps) x | inj₁ x₁ with lv-inv {M = M} Ps x
  ... | lv-red x₂ = lv-red x₂
  ... | lv-end x₂ = lv-end λ{ zero → x₁ ; (suc i) → x₂ i }
  lv-inv {M = M} (P ∷ Ps) x | inj₂ y = lv-red (y .proj₂ .proj₂)

  progress : ∀{M G} -> ⊢s M ∶ G -> done M ⊎ ∃[ α ] ∃[ M' ] M [ α ]⇒ M'
  progress {M}{G} td with lv-inv {M = M} (tabulate id) td
  progress {M}{G} td | lv-red {P ⟶ Q # S , i}{G'} gr
    with tsend/proc/inv gr (td P)
  progress {M}{G} td | lv-red {P ⟶ Q # S , i}{G'} gr | TSend/rec Pr' x
    = inj₂ (_ , _ , s/rec P (lookup⇒[]= _ _ x))
  progress {M}{G} td | lv-red {P ⟶ Q # S , i}{G'} gr
    | TSend/if E Pr' Pr'' te x with eval-bool te
  ... | inj₁ ev = inj₂ (_ , _ , s/if/true _ ((lookup⇒[]= _ _ x)) ev)
  ... | inj₂ ev = inj₂ (_ , _ , s/if/false _ ((lookup⇒[]= _ _ x)) ev)
  progress {M}{G} td | lv-red {P ⟶ _ # _ , _}{G'} _
    | TSend/send Q etd gr x with trecv/proc/inv gr (td Q)
  progress {M} {G} td | lv-red {P ⟶ _ # _ , _}{G'} _
    | TSend/send Q etd gr x | TRecv/rec Pr'' y
    = inj₂ (_ , _ , s/rec _ (lookup⇒[]= _ _ y))
  progress {M} {G} td | lv-red {P ⟶ _ # _ , _}{G'} _
    | TSend/send Q etd gr x | TRecv/if E₁ Pr'' Pr''' te y with eval-bool te
  ... | inj₁ ev = inj₂ (_ , _ , s/if/true _ (lookup⇒[]= _ _ y) ev)
  ... | inj₂ ev = inj₂ (_ , _ , s/if/false _ (lookup⇒[]= _ _ y) ev)
  progress {M} {G} td | lv-red {P ⟶ _ # _ , _}{G'} _
    | TSend/send Q etd gr x | TRecv/recv Br y
    = inj₂ (_ , _ , s/comm P Q (lookup⇒[]= _ _ x) (proj₂ (eval-exp etd))
                           (lookup⇒[]= _ _ y))
  progress {_} {G} td | lv-end f = inj₁ (λ P → tend/done (lu-tab f P) (td P))
    where
    lu-tab : (f : ∀ i → lookup (tabulate id) i ∉T G) → ∀ P → ¬ (P ∈T G)
    lu-tab f P x = f P (subst (λ A → A ∈T _) (sym (lookup-allFin P)) x)

  guard-depth-proc-mg : ∀{ G P δ}{Pr : Proc 0 δ}{Δ : Vec Behav δ}
    → [] & Δ & [] / G ↑ P ⊢p< mg > Pr → ℕ
  guard-depth-proc-mg (MPST.t/send gr etd td) = 0
  guard-depth-proc-mg (MPST.t/recv x conts) = 0
  guard-depth-proc-mg (MPST.t/skip-next x conts) = 0
  guard-depth-proc-mg (MPST.t/if etd td td₁)
    = suc (guard-depth-proc-mg td ⊔ guard-depth-proc-mg td₁)

  guard-depth-proc : ∀{ G P g}{Pr : Proc 0 0}
    → [] & [] & [] / G ↑ P ⊢p< g > Pr → ℕ
  guard-depth-proc (t/send gr etd td) = 0
  guard-depth-proc (t/recv x conts) = 0
  guard-depth-proc (t/skip-next x conts) = 0
  guard-depth-proc (t/if etd td td₁)
    = suc ((guard-depth-proc td) ⊔ (guard-depth-proc td₁))
  guard-depth-proc (t/rec x td) = suc (guard-depth-proc-mg td)
  guard-depth-proc (t/end x) = 0

  stepper : ∀{M M'} → M [ nothing ]⇒ M' → Part
  stepper (s/if/true P x x₁) = P
  stepper (s/if/false P x x₁) = P
  stepper (s/rec P x) = P

  guard-G-mg : ∀{ G P}{Pr : Proc 0 0}
    → (td1 : [] & [] & [] / G ↑ P ⊢p< mg > Pr)
    → guard-depth-proc (t/> td1) ≡ guard-depth-proc-mg td1
  guard-G-mg (MPST.t/send gr etd td1) = refl
  guard-G-mg (MPST.t/recv x conts) = refl
  guard-G-mg (MPST.t/skip-next x conts) = refl
  guard-G-mg (MPST.t/if etd td1 td2)
    = cong suc (Eq.cong₂ _⊔_ (guard-G-mg td1) (guard-G-mg td2))

  guard-unr : ∀{ G G' α P}{gr : G -< α >-> G'}{nn : P ∉α α}{Pr : Proc 0 0}
    → (td1 : [] & [] & [] / G ↑ P ⊢p< mg > Pr)
    → guard-depth-proc-mg (unrelated/step td1 gr nn) ≡ guard-depth-proc-mg td1
  guard-unr (MPST.t/send gr etd td1) = refl
  guard-unr {α = α}{gr = rt}{nn = nn} (MPST.t/recv {P = P} x conts)
    with P ≟f receiver α
  ... | yes refl rewrite recv-act-eq rt x (∈S refl) = ⊥-elim (nn (∈R refl))
  ... | no neq = refl
  guard-unr {α = α} {gr = rt} {nn = nn} (MPST.t/skip-next MPST.[ c & n & a & s ] K) 
    with K rt 
  ... | MPST.t/send gr etd td = refl
  ... | MPST.t/recv gr conts = refl
  ... | MPST.t/skip-next x ktd = refl
  ... | MPST.t/skip-close x (here px) = refl
  guard-unr (MPST.t/if etd td1 td2)
    = cong suc (Eq.cong₂ _⊔_ (guard-unr td1) (guard-unr td2))

  guard-subst : ∀{G G' P Pr Pr'}
    → (td' : [] & [] & [] / G' ↑ P ⊢p< ng > Pr')
    → (td : [] & (G' ∷ []) & [] / G ↑ P ⊢p< mg > Pr)
    → guard-depth-proc-mg (proc-subst-lemma {X = zero} td td')
      ≡ guard-depth-proc-mg td
  guard-subst td' (t/send gr etd td) = refl
  guard-subst td' (t/recv x conts) = refl
  guard-subst td' (t/skip-next x conts) = refl
  guard-subst td' (t/if etd td td₁)
    = cong suc (Eq.cong₂ _⊔_ (guard-subst td' td) (guard-subst td' td₁))

  guard-rec : ∀ {G G' Pr P}(gr : G' =<¬ P >=>ᵣ G)
   → (td : [] & (G' ∷ []) & [] / G' ↑ P ⊢p< mg > Pr)
    → guard-depth-proc (t/> (unfold/pres (t/rec gr td)))
      ≡ guard-depth-proc-mg td
  guard-rec {G' = G'} BTheory.rt/refl td
    rewrite guard-G-mg (proc-subst-lemma {X = zero} td (t/rec rt/refl td))
    = guard-subst (t/rec rt/refl td) td
  guard-rec (rt/trans gr (r , n)) td
    rewrite guard-G-mg (unrelated/step (unfold/pres (t/rec gr td)) r n)
    | guard-unr {gr = r}{nn = n}(unfold/pres (t/rec gr td))
    | sym (guard-G-mg (unfold/pres (t/rec gr td)))
    = guard-rec gr td

  less-guard-depth : ∀{M M' G} → (td : ⊢s M ∶ G) → (pr : M [ nothing ]⇒ M')
    → guard-depth-proc (preservation td pr (stepper pr))
      <ℕ guard-depth-proc (td (stepper pr))
  less-guard-depth {M = M} td (s/if/true P Ptt _) with P ≟f P
  less-guard-depth {M = M} td (s/if/true  {Pr = Pr} P Ptt _) | yes refl
    with td P
  ... | tdP
    rewrite lookup∘update P M Pr | reflect-lookup Ptt
    with tdP
  ... | t/if etd tdP₁ tdP₂ = s≤s (m≤n⇒m≤n⊔o _ ≤-refl)
  less-guard-depth {M = M} td (s/if/true P Ptt _) | no ff = ⊥-elim (ff refl)
  less-guard-depth {M = M} td (s/if/false P Ptt _) with P ≟f P
  less-guard-depth {M = M} td (s/if/false {Pr' = Pr'} P Ptt _) | yes refl
    with td P
  ... | tdP
    rewrite lookup∘update P M Pr' | reflect-lookup Ptt
    with tdP
  ... | t/if etd tdP₁ tdP₂ = s≤s (m≤n⇒m≤o⊔n _ ≤-refl)
  less-guard-depth {M = M} td (s/if/false P Ptt _) | no ff = ⊥-elim (ff refl)
  less-guard-depth {M = M} td (s/rec {Pr = Pr} P x) with td P
  ... | tdP
    rewrite reflect-lookup x
    with tdP
  ... | t/rec x₁ tdP₁ with P ≟f P
  ... | yes refl
    rewrite lookup∘update P M (unfold/proc Pr)
      | guard-rec x₁ tdP₁
    = s≤s ≤-refl
  ... | no ff = ⊥-elim (ff refl)

  guard-depth-aux : ∀{M G n} → Vec Part n → (td : ⊢s M ∶ G) → ℕ
  guard-depth-aux [] td = 0
  guard-depth-aux {M = M} (x ∷ ps) td
    = guard-depth-proc (td x) + guard-depth-aux {M = M} ps td

  guard-depth : ∀{M G} → (td : ⊢s M ∶ G) → ℕ
  guard-depth {M = M} td = guard-depth-aux {M = M}(tabulate id) td

  le-guard-depth : ∀{M M' G} P → (td : ⊢s M ∶ G) → (pr : M [ nothing ]⇒ M')
    → guard-depth-proc (preservation td pr P) ≤ℕ guard-depth-proc (td P)
  le-guard-depth {M = M} P td r with P ≟f stepper r
  le-guard-depth {M = M} P td r | yes refl = <⇒≤ (less-guard-depth td r)
  le-guard-depth {M = M} P td (s/if/true {Pr = Pr} P₁ x x₁) | no ¬eq
    with td P₁
  ... | tdP1
    rewrite reflect-lookup x
    with P₁ ≟f P
  ... | yes refl = ⊥-elim (¬eq refl)
  ... | no ne
    rewrite lookup∘update′ (≢-sym ne) M Pr
    = ≤-refl
  le-guard-depth {M = M} P td (s/if/false {Pr' = Pr} P₁ x x₁) | no ¬eq
    with td P₁
  ... | tdP1
    rewrite reflect-lookup x
    with P₁ ≟f P
  ... | yes refl = ⊥-elim (¬eq refl)
  ... | no ne
    rewrite lookup∘update′ (≢-sym ne) M Pr
    = ≤-refl
  le-guard-depth {M = M} P td (s/rec {Pr = Pr} P₁ x) | no ¬eq
    with td P₁
  ... | tdP1
    rewrite reflect-lookup x
    with tdP1
  ... | tdP1 with P₁ ≟f P
  ... | yes refl = ⊥-elim (¬eq refl)
  ... | no ¬q
    rewrite lookup∘update′ (≢-sym ¬q) M (unfold/proc Pr)
    = ≤-refl

  step-may-decrease-guard : ∀{M M' G I} → (ps : Vec Part I) → (td : ⊢s M ∶ G)
    → (pr : M [ nothing ]⇒ M')
    → guard-depth-aux {M = M'} ps (preservation td pr)
      ≤ℕ guard-depth-aux {M = M} ps td
  step-may-decrease-guard [] td pr = z≤n
  step-may-decrease-guard (x ∷ s) td pr
    = +-mono-≤ (le-guard-depth x td pr) (step-may-decrease-guard s td pr)

  step-decr-guard-aux : ∀{M M' G I} i → (ps : Vec Part I) → (td : ⊢s M ∶ G)
    → (pr : M [ nothing ]⇒ M') → (H : lookup ps i ≡ stepper pr)
    → guard-depth-aux {M = M'} ps (preservation td pr)
      <ℕ guard-depth-aux {M = M} ps td
  step-decr-guard-aux zero (x ∷ ps) td pr refl
    = +-mono-<-≤ (less-guard-depth td pr) (step-may-decrease-guard ps td pr)
  step-decr-guard-aux (suc i) (x ∷ ps) td pr H
    = +-mono-≤-< (le-guard-depth x td pr) (step-decr-guard-aux i ps td pr H)

  step-decr-guard : ∀{M M' G} → (td : ⊢s M ∶ G) → (pr : M [ nothing ]⇒ M')
    → guard-depth {M = M'} (preservation td pr) <ℕ guard-depth {M = M} td
  step-decr-guard td pr
    = step-decr-guard-aux (stepper pr) (tabulate id)
                               td pr (lookup∘tabulate id _)

  step-not-done : ∀ {G P MP Q I S G'}{i : Fin (suc I)}
    → (st : G -< (P ⟶ Q # S) , i >-> G') → (td : [] & [] & [] / G ↑ P ⊢p< ng > MP)
    → ¬ done/proc MP
  step-not-done st (MPST.t/end x) done-∅ = x (_∈T_.in/α st (_∈pr_.∈S refl))
  step-not-done st (MPST.t/if etd td td₁) (done-if p p₁)
    = step-not-done st td p

  lv-not-done : ∀{M G α G'} -> ⊢s M ∶ G -> G -< α >-> G' → ¬ done M
  lv-not-done {M = M}{α = P ⟶ Q # S , i} td st x with lookup M P | td P | x P
  ... | MP | td | p = step-not-done st td p

  session-steps : ∀{M G α G'}
    → ⊢s M ∶ G -> G -< α >-> G' → ∃[ α ] ∃[ M' ] M [ α ]⇒ M'
  session-steps {M}{G} td gr with progress {M}{G} td
  ... | inj₁ x = ⊥-elim (lv-not-done {M}{G} td gr x)
  ... | inj₂ y = y


  preservation* : ∀{M M' G} → ⊢s M ∶ G → M τ⇒ M' → ⊢s M' ∶ G
  preservation* td s/zero = td
  preservation* td (s/more x sr) = preservation* (preservation td x) sr

  lu-done : ∀{M Pr P} → done M → M [ P ]= Pr → done/proc Pr
  lu-done {P = P} dd u rewrite sym (reflect-lookup u) = dd P

  still-done : ∀{M M'} → M [ nothing ]⇒ M' → done M → done M'
  still-done {M = M} (s/if/true {Pr = Pr} P x y) d Q with P ≟f Q
  still-done {M = M} (s/if/true {Pr = Pr} P x y) d Q | yes refl
    rewrite lookup∘update P M Pr with lu-done d x
  ... | done-if dP _ = dP
  still-done {M = M} (s/if/true {Pr = Pr} P x y) d Q | no ¬eq
    rewrite lookup∘update′ (≢-sym ¬eq) M Pr = d Q
  still-done {M = M} (s/if/false {Pr' = Pr} P x y) d Q with P ≟f Q
  still-done {M = M} (s/if/false {Pr' = Pr} P x y) d Q | yes refl
    rewrite lookup∘update P M Pr with lu-done d x
  ... | done-if _ dP = dP
  still-done {M = M} (s/if/false {Pr' = Pr} P x y) d Q | no ¬eq
    rewrite lookup∘update′ (≢-sym ¬eq) M Pr = d Q
  still-done (s/rec P x) d Q with lu-done d x
  ... | ()

  ∅≢ifp : ∀{δ γ E} {Pr Pr' Pr'' : Proc δ γ} → Pr ≡ ∅
    → Pr ≡ ifp E then Pr' else Pr'' → ⊥
  ∅≢ifp refl ()

  ∅≢rec : ∀{δ γ} {Pr : Proc δ γ}{Pr'} → Pr ≡ ∅ → Pr ≡ rec Pr' → ⊥
  ∅≢rec refl ()

  still-ended : ∀{M M'} P → M [ nothing ]⇒ M' → M [ P ]s ≡ ∅ → M' [ P ]s ≡ ∅
  still-ended {M = M} P (s/if/true Q x x₁) eq with reflect-lookup x
  still-ended {M = M} P (s/if/true Q x x₁) eq | eq' with P ≟f Q
  still-ended {M = M} P (s/if/true Q x x₁) eq | eq' | yes refl
    = ⊥-elim (∅≢ifp eq eq')
  still-ended {M = M} P (s/if/true {Pr = Pr} Q x x₁) eq | eq' | no ¬eq
    rewrite lookup∘update′ ¬eq M Pr = eq
  still-ended {M = M} P (s/if/false Q x x₁) eq with reflect-lookup x
  still-ended {M = M} P (s/if/false Q x x₁) eq | eq' with P ≟f Q
  still-ended {M = M} P (s/if/false Q x x₁) eq | eq' | yes refl
    = ⊥-elim (∅≢ifp eq eq')
  still-ended {M = M} P (s/if/false {Pr' = Pr} Q x x₁) eq | eq' | no ¬eq
    rewrite lookup∘update′ ¬eq M Pr = eq
  still-ended {M = M} P (s/rec Q x) eq with reflect-lookup x
  still-ended {M = M} P (s/rec Q x) eq | eq' with P ≟f Q
  still-ended {M = M} P (s/rec Q x) eq | eq' | yes refl = ⊥-elim (∅≢rec eq eq')
  still-ended {M = M} P (s/rec {Pr = Pr} Q x) eq | eq' | no ¬eq
    rewrite lookup∘update′ ¬eq M (unfold/proc Pr) = eq

  still-done* : ∀{M M'} → M τ⇒ M' → done M → done M'
  still-done* s/zero d = d
  still-done* (s/more x sr) d = still-done* sr (still-done x d)

  still-ended* : ∀{M M' P} → M τ⇒ M' → M [ P ]s ≡ ∅ → M' [ P ]s ≡ ∅
  still-ended* s/zero d = d
  still-ended* (s/more x sr) d = still-ended* sr (still-ended _ x d)

  final-run-proc : ∀{M G P} Pr → ⊢s M ∶ G → M [ P ]s ≡ Pr
    → done/proc Pr
    → ∃[ M' ] (M τ⇒ M') × (M' [ P ]s ≡ ∅)
  final-run-proc Pr td lu done-∅ = _ , s/zero , lu
  final-run-proc {M = M}{P = P} Pr td lu (done-if dd dd₁)
    with td/lookup {M = M} td (lookup-get lu)
  ... | t/if {Pr = PrT} {Pr' = PrF} etd a a₁ with eval-bool etd
  ... | inj₁ x
    = let next = s/if/true {M = M} _ (lookup-get lu) x
          _ , rr , ff = final-run-proc {M = M [ P ]≔ PrT}{P = P} PrT
                                       (preservation td next)
                                       (lookup∘update P M PrT) dd
      in _ , s/more next rr , ff
  ... | inj₂ y
    = let next = s/if/false {M = M} _ (lookup-get lu) y
          _ , rr , ff = final-run-proc {M = M [ P ]≔ PrF}{P = P} PrF
                                       (preservation td next)
                                       (lookup∘update P M PrF) dd₁
      in _ , s/more next rr , ff

  catτ : ∀{M M' M''} → M τ⇒ M' → M' τ⇒ M'' → M τ⇒ M''
  catτ s/zero sr' = sr'
  catτ (s/more x sr) sr' = s/more x (catτ sr sr')

  final-run' : ∀{I M G} → (Ps : Vec Part I) → ⊢s M ∶ G → done M
    → ∃[ M' ] (M τ⇒ M') × (∀ (i : Fin I) → M' [ lookup Ps i ]s ≡ ∅)
  final-run' {M = M} {G = G} [] td dd = _ , s/zero , λ ()
  final-run' {M = M} {G = G} (P ∷ Ps) td dd with final-run' {M = M} Ps td dd
  ... | M' , rr , ff
    with final-run-proc {M = M'} (M' [ P ]s) (preservation* td rr) refl
                        (still-done* rr dd P)
  ... | M'' , rr' , fP
    = M'' , catτ rr rr' , λ{ zero → fP ; (suc i) → still-ended* rr' (ff i) }

  final-run : ∀{M G} → ⊢s M ∶ G → done M → ∃[ M' ] (M τ⇒ M') × finished M'
  final-run {M = M} s d = let M' , rr , ff = final-run' (tabulate id) s d
                          in M' , rr , lu-tab M' ff
    where
      lu-tab : ∀ M → (∀ (i : Fin N) → M [ lookup (tabulate id) i ]s ≡ ∅)
        → ∀ i → M [ i ]s ≡ ∅
      lu-tab _ f i rewrite sym (lookup∘tabulate id i) = f i

  open _⇒∞
  must-progress : ∀{M G} (td : ⊢s M ∶ G) → M ⇏∞
  must-progress td = no-inf-tau td (<-wellFounded (guard-depth td))
    where
    no-inf-tau : ∀{M G} (td : ⊢s M ∶ G)
      → Acc (_<ℕ_) (guard-depth {M = M} td) → M ⇏∞
    no-inf-tau {M = M} td (acc rs) gr
      = no-inf-tau (preservation td (gr .∞-step))
                   (rs (step-decr-guard td (gr .∞-step)))
                   (gr .∞-next)

  liveness : ∀{M G} → ⊢s M ∶ G
    → ∃[ M' ] ((M τ⇒ M' × finished M') ⊎ Σ[ α ∈ Action ] M [ α ]⇒+ M')
  liveness {M = M}{G = G} td with lv-inv {M = M} (tabulate id) td
  ... | lv-end x
    = let M' , rτ , f = final-run td (λ P → tend/done (lu-tab x P) (td P))
      in M' , inj₁ (rτ , f)
    where
    lu-tab : (f : ∀ i → lookup (tabulate id) i ∉T G) → ∀ P → ¬ (P ∈T G)
    lu-tab f P x = f P (subst (λ A → A ∈T _) (sym (lookup-allFin P)) x)
  ... | lv-red x
    = let α , M' , r = go td x (<-wellFounded (guard-depth td))
      in M' , inj₂ (α , r)
    where
      go : ∀{M G' α} (td : ⊢s M ∶ G) (gr : G -< α >-> G')
        → (gas : Acc (_<ℕ_) (guard-depth {M = M} td))
        → ∃[ α ] ∃[ M' ] M [ α ]⇒+ M'
      go {M = M}{α = P ⟶ Q # S , i} td gr (acc rs) with progress {M = M} td
      ... | inj₁ x = ⊥-elim (step-not-done gr (td P) (x P))
      ... | inj₂ (just x , M' , st) = x , M' , s/one st
      ... | inj₂ (nothing , M' , st)
        with go {M = M'} (preservation td st) gr (rs (step-decr-guard td st))
      ... | α , M'' , sr = α , M'' , s/more st sr
