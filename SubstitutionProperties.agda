{-# OPTIONS --guardedness #-}

open import Data.Empty using (⊥-elim)
open import Data.Unit  using (tt)

open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties using (+-identityʳ)

open import Data.Fin
  using    (Fin; zero; suc; compare; punchIn; punchOut)
  renaming (_≟_ to _≟f_)

open import Data.Fin.Properties
  using (punchIn-punchOut)

open import Data.Vec
  using (Vec; []; _∷_; _++_; _[_]=_; insertAt; cast)
  renaming (lookup to lu; removeAt to _-_)

open import Data.Vec.Properties
  using
    ( insertAt-punchIn
    ; insertAt-lookup
    ; removeAt-insertAt
    ; removeAt-punchOut
    ; cast-is-id
    ; cast-sym
    ; ++-identityʳ-eqFree
    )

open import Data.Vec.Relation.Unary.Any using (Any)

open import Data.Product using (∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function     using (_∘_)

open import Relation.Nullary using (False; ¬_; yes; no)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; _≢_; cong)

open import Utils.Fin using (refl-is-equal; reflect-lookup)
open import Utils.Vec using (lookup-not-insertAt)

open import Definitions

module SubstitutionProperties {N : ℕ}{B : BTheory N}(BP : BT-Prop B) where
  open module M = Definitions.MPST(BP)
  open M
  open M.Subst

  private
    variable
      γ δ ξ ξ′ : ℕ

  lookup/prepend :
    ∀ {G}
      {Ξ : Vec Behav ξ}
    → (Ξ′ : Vec Behav ξ′)
    → ∃[ X ] lu Ξ X ~ G
    → ∃[ X′ ] lu (Ξ′ ++ Ξ) X′ ~ G

  lookup/prepend [] (X , eq) =
    X , eq

  lookup/prepend (_ ∷ Ξ′) (X , eq)
    with lookup/prepend Ξ′ (X , eq)
  ... | X′ , eq′ =
    suc X′ , eq′


  lookup/swap :
    ∀ {G H H′}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → ∃[ X ] lu (Ξ′ ++ (H′ ∷ H ∷ Ξ)) X ~ G
    → ∃[ X′ ] lu (Ξ′ ++ (H ∷ H′ ∷ Ξ)) X′ ~ G

  lookup/swap {Ξ′ = []} (zero , eq) =
    suc zero , eq

  lookup/swap {Ξ′ = []} (suc zero , eq) =
    zero , eq

  lookup/swap {Ξ′ = []} (suc (suc X) , eq) =
    suc (suc X) , eq

  lookup/swap {Ξ′ = _ ∷ Ξ′} (zero , eq) =
    zero , eq

  lookup/swap {Ξ′ = _ ∷ Ξ′} (suc X , eq)
    with lookup/swap {Ξ′ = Ξ′} (X , eq)
  ... | X′ , eq′ =
    suc X′ , eq′


  lookup/insert :
    ∀ {G H}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → ∃[ X ] lu (Ξ′ ++ (H ∷ Ξ)) X ~ G
    → H ~ G ⊎ ∃[ X′ ] lu (Ξ′ ++ Ξ) X′ ~ G

  lookup/insert {Ξ′ = []} (zero , eq) =
    inj₁ eq

  lookup/insert {Ξ′ = []} (suc X , eq) =
    inj₂ (X , eq)

  lookup/insert {Ξ′ = _ ∷ Ξ′} (zero , eq) =
    inj₂ (zero , eq)

  lookup/insert {Ξ′ = _ ∷ Ξ′} (suc X , eq)
    with lookup/insert {Ξ′ = Ξ′} (X , eq)
  ... | inj₁ eq′ =
    inj₁ eq′
  ... | inj₂ (X′ , eq′) =
    inj₂ (suc X′ , eq′)


  lookup/float :
    ∀ {G H}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → ∃[ X ] lu (Ξ′ ++ (H ∷ Ξ)) X ~ G
    → ∃[ X′ ] lu (H ∷ (Ξ′ ++ Ξ)) X′ ~ G

  lookup/float {H = H} {Ξ = Ξ} {Ξ′ = Ξ′} lookup
    with lookup/insert {H = H} {Ξ = Ξ} {Ξ′ = Ξ′} lookup
  ... | inj₁ eq =
    zero , eq
  ... | inj₂ (X′ , eq′) =
    suc X′ , eq′


  skip/bisim :
    ∀ {G G′ H P}
    → G′ ~ H
    → G -[¬ P ]->* G′
    → ∃[ H₀ ] (G ~ H₀) × (H₀ -[¬ P ]->* H)
  skip/bisim G~H skip/refl =
    _ , G~H , skip/refl
  skip/bisim G′~H (skip/step gr P∉α tr) =
    let _ , G₁~H₁ , H₁↝H = skip/bisim G′~H tr
        _ , G~H₀  , H₀↝H₁ = stepback/~ G₁~H₁ gr
    in _ , G~H₀ , skip/step H₀↝H₁ P∉α H₁↝H


  td/bisim :
    ∀ {γ δ ξ G G′ P Pr}
      {Γ : Vec Sort γ}
      {Δ Δ′ : Vec Behav δ}
      {Ξ Ξ′ : Vec Behav ξ}
    → Δ ~ᵛ Δ′
    → Ξ ~ᵛ Ξ′
    → G ~ G′
    → Γ & Δ  & Ξ  ⊢p P ◂ Pr ∶ G
    → Γ & Δ′ & Ξ′ ⊢p P ◂ Pr ∶ G′
  td/bisim Δ~Δ′ Ξ~Ξ′ G~G′ (t/send gr etd td) =
    t/send (~L→ G~G′ gr) etd
      (td/bisim Δ~Δ′ ~ᵛ/[] (~L→~ G~G′ gr) td)
  td/bisim Δ~Δ′ Ξ~Ξ′ G~G′ (t/recv gr conts) =
    t/recv (~L→ G~G′ gr) λ gr′ →
      td/bisim Δ~Δ′ ~ᵛ/[] (~R→~ G~G′ gr′)
        (conts (~R→ G~G′ gr′))
  td/bisim Δ~Δ′ Ξ~Ξ′ G~G′ (t/skip gr na ktd) =
    t/skip (~L→ G~G′ gr) (na ∘ ~R→ G~G′) λ gr′ →
      td/bisim Δ~Δ′ (~ᵛ/∷ G~G′ Ξ~Ξ′) (~R→~ G~G′ gr′)
        (ktd (~R→ G~G′ gr′))
  td/bisim Δ~Δ′ Ξ~Ξ′ G~G′ (t/skip-cycle {X = X} eq P∈G) =
    t/skip-cycle
      (~trans (lookup/~ᵛ Ξ~Ξ′ X eq) G~G′)
      (∈~ G~G′ P∈G)
  td/bisim Δ~Δ′ Ξ~Ξ′ G~G′ (t/unskip tr td)
    with skip/bisim G~G′ tr
  ... | _ , G₀~G₀′ , tr′ =
    t/unskip tr′ (td/bisim Δ~Δ′ ~ᵛ/[] G₀~G₀′ td)
  td/bisim Δ~Δ′ Ξ~Ξ′ G~G′ (t/if etd td td₁) =
    t/if etd
      (td/bisim Δ~Δ′ ~ᵛ/[] G~G′ td)
      (td/bisim Δ~Δ′ ~ᵛ/[] G~G′ td₁)
  td/bisim Δ~Δ′ Ξ~Ξ′ G~G′ (t/rec mg₁ td) =
    t/rec mg₁ (td/bisim (~ᵛ/∷ G~G′ Δ~Δ′) ~ᵛ/[] G~G′ td)
  td/bisim Δ~Δ′ Ξ~Ξ′ G~G′ (t/var eq) =
    t/var (~trans (lookup/~ᵛ Δ~Δ′ _ eq) G~G′)
  td/bisim Δ~Δ′ Ξ~Ξ′ G~G′ (t/end d) =
    t/end (d ∘ ∈~ (~sym G~G′))


  t/bisim :
    ∀ {δ γ ξ G G′ P Pr}
      {Γ : Vec Sort γ}
      {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
    → G ~ G′
    → Γ & Δ & Ξ ⊢p P ◂ Pr ∶ G
    → Γ & Δ & Ξ ⊢p P ◂ Pr ∶ G′
  t/bisim = td/bisim ~ᵛ-refl ~ᵛ-refl


  transport-behav :
    ∀ {P Pr G G′}
      {Γ : Vec Sort γ}
      {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
    → G ≡ G′
    → Γ & Δ & Ξ ⊢p P ◂ Pr ∶ G
    → Γ & Δ & Ξ ⊢p P ◂ Pr ∶ G′
  transport-behav = subst (λ G → _ & _ & _ ⊢p _ ◂ _ ∶ G)


  swap/visited :
    ∀ {P Pr G H H′}
      {Γ : Vec Sort γ}
      {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → Γ & Δ & (Ξ′ ++ (H′ ∷ H ∷ Ξ)) ⊢p P ◂ Pr ∶ G
    → Γ & Δ & (Ξ′ ++ (H ∷ H′ ∷ Ξ)) ⊢p P ◂ Pr ∶ G

  swap/visited (t/send gr etd td) =
    t/send gr etd td
  swap/visited (t/recv gr conts) =
    t/recv gr conts
  swap/visited {Ξ′ = Ξ′} (t/skip gr na ktd) =
    t/skip gr na λ gr′ →
      swap/visited {Ξ′ = _ ∷ Ξ′} (ktd gr′)
  swap/visited {G = G} {H = H} {H′ = H′} {Ξ = Ξ} {Ξ′ = Ξ′}
    (t/skip-cycle {X = X} eq P∈G)
    with lookup/swap {G = G} {H = H} {H′ = H′} {Ξ = Ξ} {Ξ′ = Ξ′}
           (X , eq)
  ... | X′ , eq′ =
    t/skip-cycle {X = X′} eq′ P∈G
  swap/visited (t/unskip tr td) =
    t/unskip tr td
  swap/visited (t/if etd ttd ftd) =
    t/if etd ttd ftd
  swap/visited (t/rec guarded td) =
    t/rec guarded td
  swap/visited (t/var eq) =
    t/var eq
  swap/visited (t/end done) =
    t/end done


  float/visited :
    ∀ {P Pr G H}
      {Γ : Vec Sort γ}
      {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
      {Ξ′ : Vec Behav ξ′}
    → Γ & Δ & (Ξ′ ++ (H ∷ Ξ)) ⊢p P ◂ Pr ∶ G
    → Γ & Δ & (H ∷ (Ξ′ ++ Ξ)) ⊢p P ◂ Pr ∶ G

  float/visited (t/send gr etd td) =
    t/send gr etd td
  float/visited (t/recv gr conts) =
    t/recv gr conts
  float/visited {Ξ′ = Ξ′} (t/skip gr na ktd) =
    t/skip gr na λ gr′ →
      swap/visited {Ξ′ = []}
        (float/visited {Ξ′ = _ ∷ Ξ′} (ktd gr′))
  float/visited {G = G} {H = H} {Ξ = Ξ} {Ξ′ = Ξ′}
    (t/skip-cycle {X = X} eq P∈G)
    with lookup/float {G = G} {H = H} {Ξ = Ξ} {Ξ′ = Ξ′}
           (X , eq)
  ... | X′ , eq′ =
    t/skip-cycle {X = X′} eq′ P∈G
  float/visited (t/unskip tr td) =
    t/unskip tr td
  float/visited (t/if etd ttd ftd) =
    t/if etd ttd ftd
  float/visited (t/rec guarded td) =
    t/rec guarded td
  float/visited (t/var eq) =
    t/var eq
  float/visited (t/end done) =
    t/end done


  strengthen/visited :
    ∀ {P Pr G}
      {Γ : Vec Sort γ}
      {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
    → (Ξ′ : Vec Behav ξ′)
    → Γ & Δ & Ξ ⊢p P ◂ Pr ∶ G
    → Γ & Δ & (Ξ′ ++ Ξ) ⊢p P ◂ Pr ∶ G

  strengthen/visited Ξ′ (t/send gr etd td) =
    t/send gr etd td
  strengthen/visited Ξ′ (t/recv gr conts) =
    t/recv gr conts
  strengthen/visited Ξ′ (t/skip gr na ktd) =
    t/skip gr na λ gr′ →
      float/visited (strengthen/visited Ξ′ (ktd gr′))
  strengthen/visited Ξ′ (t/skip-cycle {X = X} eq P∈G)
    with lookup/prepend Ξ′ (X , eq)
  ... | X′ , eq′ =
    t/skip-cycle {X = X′} eq′ P∈G
  strengthen/visited Ξ′ (t/unskip tr td) =
    t/unskip tr td
  strengthen/visited Ξ′ (t/if etd ttd ftd) =
    t/if etd ttd ftd
  strengthen/visited Ξ′ (t/rec guarded td) =
    t/rec guarded td
  strengthen/visited Ξ′ (t/var eq) =
    t/var eq
  strengthen/visited Ξ′ (t/end done) =
    t/end done


  unfold/tskip :
    ∀ {P Pr G H}
      {Γ : Vec Sort γ}
      {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
    → (Ξ′ : Vec Behav ξ′)
    → Γ & Δ & Ξ ⊢p P ◂ Pr ∶ H
    → Γ & Δ & (Ξ′ ++ (H ∷ Ξ)) ⊢p P ◂ Pr ∶ G
    → Γ & Δ & (Ξ′ ++ Ξ) ⊢p P ◂ Pr ∶ G

  unfold/tskip Ξ′ otd (t/send gr etd td) =
    t/send gr etd td
  unfold/tskip Ξ′ otd (t/recv gr conts) =
    t/recv gr conts
  unfold/tskip Ξ′ otd (t/skip gr na ktd) =
    t/skip gr na λ gr′ →
      unfold/tskip (_ ∷ Ξ′) otd (ktd gr′)
  unfold/tskip Ξ′ otd (t/skip-cycle {X = X} eq P∈G)
    with lookup/insert {Ξ′ = Ξ′} (X , eq)
  ... | inj₁ eq′ =
    t/bisim eq′ (strengthen/visited Ξ′ otd)
  ... | inj₂ (X′ , eq′) =
    t/skip-cycle {X = X′} eq′ P∈G
  unfold/tskip Ξ′ otd (t/unskip tr td) =
    t/unskip tr td
  unfold/tskip Ξ′ otd (t/if etd ttd ftd) =
    t/if etd ttd ftd
  unfold/tskip Ξ′ otd (t/rec guarded td) =
    t/rec guarded td
  unfold/tskip Ξ′ otd (t/var eq) =
    t/var eq
  unfold/tskip Ξ′ otd (t/end done) =
    t/end done


  cast-visited :
    ∀ {P Pr G}
      {Γ : Vec Sort γ}
      {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
    → (eq : ξ ≡ ξ′)
    → Γ & Δ & cast eq Ξ ⊢p P ◂ Pr ∶ G
    → Γ & Δ & Ξ ⊢p P ◂ Pr ∶ G

  cast-visited {Ξ = Ξ} refl td
    rewrite cast-is-id refl Ξ =
    td

  expr-weaken-lemma :
    ∀ {γ E S S' x}
      {Γ : Vec Sort γ}
    → Γ ⊢e E ∶ S
    → insertAt Γ x S' ⊢e weaken/exp E x ∶ S

  expr-weaken-lemma (te/val V) =
    te/val V

  expr-weaken-lemma (te/minus1 td) =
    te/minus1 (expr-weaken-lemma td)

  expr-weaken-lemma (te/is-zero td) =
    te/is-zero (expr-weaken-lemma td)

  expr-weaken-lemma {S' = S'} {x = x} {Γ = Γ} (te/var {y})
    rewrite sym (insertAt-punchIn Γ x S' y) =
    te/var


  expr-subst-lemma :
    ∀ {S S′ γ E V}
      {Γ : Vec Sort γ}
      {x : Fin (suc γ)}
    → insertAt Γ x S′ ⊢e E ∶ S
    → ⊢v V ∶ S′
    → Γ ⊢e [ val V / x ]exp E ∶ S

  expr-subst-lemma (te/val V) vtd =
    te/val V

  expr-subst-lemma (te/minus1 etd) vtd =
    te/minus1 (expr-subst-lemma etd vtd)

  expr-subst-lemma (te/is-zero etd) vtd =
    te/is-zero (expr-subst-lemma etd vtd)

  expr-subst-lemma {S′ = S′} {Γ = Γ} {x = x} (te/var {y}) vtd
    with x ≟f y

  expr-subst-lemma {S′ = S′} {Γ = Γ} {x = x} (te/var {y}) vtd
    | yes refl
    rewrite insertAt-lookup Γ x S′ =
    te/val vtd

  expr-subst-lemma {S′ = S′} {Γ = Γ} {x = x} (te/var {y}) vtd
    | no x≢y
    rewrite lookup-not-insertAt {V = Γ} {a = S′} x y x≢y =
    te/var


  removeAt/suc :
    ∀ {A : Set} {γ}
      {x : A}
      {i : Fin (suc γ)}
      {Γ : Vec A (suc γ)}
    → (x ∷ Γ) - suc i ≡ x ∷ (Γ - i)

  removeAt/suc {_} {_} {_} {_} {_ ∷ Γ} =
    refl


  subst/lu :
    ∀ {γ δ I}
      {E : Exp γ}
      {X}
      (Br : Vec (Proc (suc γ) δ) (suc I))
      (i : Fin (suc I))
    → [ E / suc X ]e lu Br i ≡ lu ([ E / X ]ech Br) i

  subst/lu (_ ∷ _) zero =
    refl

  subst/lu {I = suc _} (_ ∷ Br) (suc i) =
    subst/lu Br i


  message-guarded-weaken-expr :
    ∀ {γ δ X}
      {Pr : Proc γ δ}
    → MessageGuarded Pr
    → MessageGuarded (weaken/proc/exp Pr X)
  message-guarded-weaken-expr mg/send =
    mg/send
  message-guarded-weaken-expr mg/recv =
    mg/recv
  message-guarded-weaken-expr (mg/if mmg mmg₁) =
    mg/if
      (message-guarded-weaken-expr mmg)
      (message-guarded-weaken-expr mmg₁)


  subst-message-guarded :
    ∀ {γ δ}
      {E : Exp γ}
      {X : Fin (suc γ)}
      {Pr : Proc (suc γ) (suc δ)}
    → (mmg : MessageGuarded Pr)
    → MessageGuarded ([ E / X ]e Pr)
  subst-message-guarded mg/send = mg/send
  subst-message-guarded mg/recv = mg/recv
  subst-message-guarded (mg/if mmgl mmgr) =
    mg/if
      (subst-message-guarded mmgl)
      (subst-message-guarded mmgr)

  transport-proc :
    ∀ {δ γ ξ p p′ P G}
      {Δ : Vec Behav δ}
      {Γ : Vec Sort γ}
      {Ξ : Vec Behav ξ}
    → p ≡ p′
    → Γ & Δ & Ξ ⊢p P ◂ p  ∶ G
    → Γ & Δ & Ξ ⊢p P ◂ p′ ∶ G
  transport-proc = subst (λ x → _ & _ & _ ⊢p _ ◂ x ∶ _)


  proc-subst-lemma-expr :
    ∀ {γ δ ξ G P E Pr}
      {Γ : Vec Sort (suc γ)}
      {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
      {X : Fin (suc γ)}
    → (Γ - X)     ⊢e E                 ∶ lu Γ X
    → Γ       & Δ & Ξ ⊢p P ◂ Pr            ∶ G
    → (Γ - X) & Δ & Ξ ⊢p P ◂ [ E / X ]e Pr ∶ G

  proc-subst-lemma-expr etd (t/send gr etd′ ptd) =
    t/send gr
      (exp-subst etd′ etd)
      (proc-subst-lemma-expr etd ptd)

  proc-subst-lemma-expr {Γ = _ ∷ _} etd (t/recv {Br = Br} gr conts) =
    t/recv gr
      (transport-proc (subst/lu Br _)
      ∘ proc-subst-lemma-expr (exp-str etd)
      ∘ conts)

  proc-subst-lemma-expr etd (t/skip gr na ktd) =
    t/skip gr na (proc-subst-lemma-expr etd ∘ ktd)

  proc-subst-lemma-expr etd (t/skip-cycle eq P∈G) =
    t/skip-cycle eq P∈G

  proc-subst-lemma-expr etd (t/unskip tr ptd) =
    t/unskip tr (proc-subst-lemma-expr etd ptd)

  proc-subst-lemma-expr etd (t/if etd₁ ptd ptd₁) =
    t/if
      (exp-subst etd₁ etd)
      (proc-subst-lemma-expr etd ptd)
      (proc-subst-lemma-expr etd ptd₁)

  proc-subst-lemma-expr etd (t/rec mmg ptd) =
    t/rec
      (subst-message-guarded mmg)
      (proc-subst-lemma-expr etd ptd)

  proc-subst-lemma-expr etd (t/var eq) =
    t/var eq

  proc-subst-lemma-expr etd (t/end done₁) =
    t/end done₁


  expr-lookup-after-branch-weakening :
    ∀ {γ δ I i x}
    → (Br : Vec (Proc (suc γ) δ) I)
    → weaken/proc/exp (lu Br i) x
      ≡ lu (weaken/exp/branch Br x) i

  expr-lookup-after-branch-weakening {i = zero} (_ ∷ _) =
    refl

  expr-lookup-after-branch-weakening {i = suc i} (_ ∷ Br) =
    expr-lookup-after-branch-weakening {i = i} Br

  proc-weaken-lemma-expr :
    ∀ {γ δ ξ P Pr G S x}
      {Γ : Vec Sort γ}
      {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
    → Γ & Δ & Ξ ⊢p P ◂ Pr ∶ G
    → insertAt Γ x S & Δ & Ξ ⊢p P ◂ weaken/proc/exp Pr x ∶ G

  proc-weaken-lemma-expr (t/send gr etd ptd) =
    t/send gr
      (expr-weaken-lemma etd)
      (proc-weaken-lemma-expr ptd)

  proc-weaken-lemma-expr (t/recv {Br = Br} gr conts) =
    t/recv gr
      ( transport-proc (expr-lookup-after-branch-weakening Br)
      ∘ proc-weaken-lemma-expr
      ∘ conts
      )

  proc-weaken-lemma-expr (t/skip gr na ktd) =
    t/skip gr na
      (proc-weaken-lemma-expr ∘ ktd)

  proc-weaken-lemma-expr (t/skip-cycle eq P∈G) =
    t/skip-cycle eq P∈G

  proc-weaken-lemma-expr (t/unskip tr ptd) =
    t/unskip tr
      (proc-weaken-lemma-expr ptd)

  proc-weaken-lemma-expr (t/if etd ptd₁ ptd₂) =
    t/if
      (expr-weaken-lemma etd)
      (proc-weaken-lemma-expr ptd₁)
      (proc-weaken-lemma-expr ptd₂)

  proc-weaken-lemma-expr (t/rec mg₁ ptd) =
    t/rec
      (message-guarded-weaken-expr mg₁)
      (proc-weaken-lemma-expr ptd)

  proc-weaken-lemma-expr (t/var eq) =
    t/var eq

  proc-weaken-lemma-expr (t/end done) =
    t/end done

  proc-lookup-after-branch-weakening :
    ∀ {γ δ I}
    → (Br : Vec (Proc (suc γ) δ) I)
    → (i : Fin I)
    → (X : Fin (suc δ))
    → weaken/proc (lu Br i) X
      ≡ lu (weaken/proc/branch Br X) i

  proc-lookup-after-branch-weakening (_ ∷ _) zero _ =
    refl

  proc-lookup-after-branch-weakening (_ ∷ Br) (suc i) X =
    proc-lookup-after-branch-weakening Br i X


  message-guarded-weaken :
    ∀ {γ δ X}
      {Pr : Proc γ δ}
    → MessageGuarded Pr
    → MessageGuarded (weaken/proc Pr X)

  message-guarded-weaken mg/send =
    mg/send

  message-guarded-weaken mg/recv =
    mg/recv

  message-guarded-weaken (mg/if mmg mmg₁) =
    mg/if
      (message-guarded-weaken mmg)
      (message-guarded-weaken mmg₁)


  proc-weaken-lemma :
    ∀ {γ δ ξ G G' P Pr X}
      {Γ : Vec Sort γ}
      {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
    → Γ & Δ & Ξ ⊢p P ◂ Pr ∶ G
    → Γ & insertAt Δ X G' & Ξ ⊢p P ◂ weaken/proc Pr X ∶ G

  proc-weaken-lemma (t/send gr etd ptd) =
    t/send gr etd
      (proc-weaken-lemma ptd)

  proc-weaken-lemma (t/recv {Br = Br} gr conts) =
    t/recv gr
      ( transport-proc (proc-lookup-after-branch-weakening Br _ _)
      ∘ proc-weaken-lemma
      ∘ conts
      )

  proc-weaken-lemma (t/skip gr na ktd) =
    t/skip gr na
      (proc-weaken-lemma ∘ ktd)

  proc-weaken-lemma (t/skip-cycle eq P∈G) =
    t/skip-cycle eq P∈G

  proc-weaken-lemma (t/unskip tr ptd) =
    t/unskip tr
      (proc-weaken-lemma ptd)

  proc-weaken-lemma (t/if etd ptd ptd₁) =
    t/if etd
      (proc-weaken-lemma ptd)
      (proc-weaken-lemma ptd₁)

  proc-weaken-lemma (t/rec mg₁ ptd) =
    t/rec
      (message-guarded-weaken mg₁)
      (proc-weaken-lemma ptd)

  proc-weaken-lemma
    {G' = G'}
    {X = X}
    {Δ = Δ}
    (t/var {X = Y} eq)
    rewrite sym (insertAt-punchIn Δ X G' Y) =
    t/var eq

  proc-weaken-lemma (t/end done₁) =
    t/end done₁

  proc-lookup-after-branch-subst :
    ∀ {γ δ I Pr X i}
    → (Br : Vec (Proc (suc γ) (suc δ)) I)
    → [ weaken/proc/exp Pr zero / X ]pr (lu Br i)
      ≡ lu ([ Pr / X ]prch Br) i

  proc-lookup-after-branch-subst {i = zero} (_ ∷ _) =
    refl

  proc-lookup-after-branch-subst {i = suc i} (_ ∷ Br) =
    proc-lookup-after-branch-subst {i = i} Br


  message-guarded-after-proc-subst :
    ∀ {γ δ X}
      {Pr' : Proc γ δ}
      {Pr  : Proc γ (suc (suc δ))}
    → MessageGuarded Pr
    → MessageGuarded ([ weaken/proc Pr' zero / suc X ]pr Pr)

  message-guarded-after-proc-subst mg/send =
    mg/send

  message-guarded-after-proc-subst mg/recv =
    mg/recv

  message-guarded-after-proc-subst (mg/if mg₁ mg₂) =
    mg/if
      (message-guarded-after-proc-subst mg₁)
      (message-guarded-after-proc-subst mg₂)


  lookup-after-insertAt-punchOut :
    ∀ {A : Set} {γ}
    → (Γ : Vec A γ)
    → {x : Fin (suc γ)}
    → {S : A}
    → {y : Fin (suc γ)}
    → (x≢y : x ≢ y)
    → lu (insertAt Γ x S) y ≡ lu Γ (punchOut x≢y)

  lookup-after-insertAt-punchOut Γ {x = x} {S = S} {y = y} x≢y
    rewrite sym (removeAt-insertAt Γ x S)
    with sym (removeAt-punchOut (insertAt Γ x S) x≢y)
  ... | eq
    rewrite removeAt-insertAt Γ x S =
    eq

  proc-subst-lemma :
    ∀ {γ δ ξ G G' P Pr Pr'}
      {Γ : Vec Sort γ}
      {Δ : Vec Behav δ}
      {Ξ : Vec Behav ξ}
      {X : Fin (suc δ)}
    → Γ & Δ & [] ⊢p P ◂ Pr' ∶ G'
    → Γ & insertAt Δ X G' & Ξ ⊢p P ◂ Pr ∶ G
    → Γ & Δ & Ξ ⊢p P ◂ [ Pr' / X ]pr Pr ∶ G

  proc-subst-lemma ptd′ (t/send gr etd ptd) =
    t/send gr etd
      (proc-subst-lemma ptd′ ptd)

  proc-subst-lemma ptd′ (t/recv {Br = Br} gr conts) =
    t/recv gr
      ( transport-proc (proc-lookup-after-branch-subst Br)
      ∘ proc-subst-lemma (proc-weaken-lemma-expr ptd′)
      ∘ conts
      )

  proc-subst-lemma ptd′ (t/skip gr na ktd) =
    t/skip gr na (proc-subst-lemma ptd′ ∘ ktd)

  proc-subst-lemma ptd′ (t/skip-cycle eq P∈G) =
    t/skip-cycle eq P∈G

  proc-subst-lemma ptd′ (t/unskip tr ptd) =
    t/unskip tr (proc-subst-lemma ptd′ ptd)

  proc-subst-lemma ptd′ (t/if etd ptd ptd₁) =
    t/if etd
      (proc-subst-lemma ptd′ ptd)
      (proc-subst-lemma ptd′ ptd₁)

  proc-subst-lemma ptd′ (t/rec mg₁ ptd) =
    t/rec
      (message-guarded-after-proc-subst mg₁)
      (proc-subst-lemma
        (proc-weaken-lemma ptd′)
        ptd)

  proc-subst-lemma
    {ξ = ξ}
    {G' = G'}
    {Δ = Δ}
    {Ξ = Ξ}
    {X = X}
    ptd′
    (t/var {X = X′} eq)
    with X ≟f X′
  ... | no ¬eq
    rewrite lookup-after-insertAt-punchOut
              Δ
              {x = X}
              {S = G'}
              {y = X′}
              ¬eq =
    t/var eq
  ... | yes refl
    rewrite insertAt-lookup Δ X G' =
    let res = strengthen/visited Ξ (t/bisim eq ptd′)
        idr = sym (cast-sym (+-identityʳ ξ) (++-identityʳ-eqFree Ξ))
        res′ = subst (λ Ξ′ → _ & _ & Ξ′ ⊢p _ ◂ _ ∶ _) idr res
    in cast-visited (sym (+-identityʳ _)) res′

  proc-subst-lemma ptd′ (t/end done₁) =
    t/end done₁
