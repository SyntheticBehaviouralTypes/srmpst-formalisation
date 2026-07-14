{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc)
open import Data.Fin
  using (Fin; zero; suc; punchIn; punchOut)
  renaming (_≟_ to _≟f_)
open import Data.Vec
  using (Vec; []; _∷_; insertAt)
  renaming (lookup to lu; removeAt to _-_)
open import Data.Vec.Properties
  using
    ( insertAt-punchIn
    ; insertAt-lookup
    ; removeAt-insertAt
    ; removeAt-punchOut
    )
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; _≢_)
open import Utils.Vec using (lookup-not-insertAt)
open import Definitions
import Safety.Skip

module Typing.Substitution {N : ℕ}{B : BTheory N}(BP : BT-Prop B) where
  open module M = Definitions.MPST(BP)
  open module SK = Safety.Skip BP using (td/bisim)
  open M
  open M.Subst

  private
    variable
      γ δ ξ ξ′ : ℕ


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
    ∀ {δ γ p p′ P G}
      {Δ : Vec Behav δ}
      {Γ : Vec Sort γ}
    → p ≡ p′
    → Γ & Δ ⊢p P ◂ p  ∶ G
    → Γ & Δ ⊢p P ◂ p′ ∶ G
  transport-proc = subst (λ x → _ & _ ⊢p _ ◂ x ∶ _)


  mutual

    skip-subst-lemma-expr :
      ∀ {m γ δ ξ G P E Pr}
        {Γ : Vec Sort (suc γ)}
        {Δ : Vec Behav δ}
        {Ξ : Vec Behav ξ}
        {X : Fin (suc γ)}
      → (Γ - X)     ⊢e E                 ∶ lu Γ X
      → Γ       & Δ & Ξ ⊢skip[ m ] P ◂ Pr            ∶ G
      → (Γ - X) & Δ & Ξ ⊢skip[ m ] P ◂ [ E / X ]e Pr ∶ G

    skip-subst-lemma-expr etd (skip/main td) =
      skip/main (proc-subst-lemma-expr etd td)

    skip-subst-lemma-expr etd (skip/step gr na ktd prod-gr) =
      skip/step gr na
        (λ gr′ →
          proj₁ (ktd gr′) , skip-subst-lemma-expr etd (proj₂ (ktd gr′)))
        prod-gr

    skip-subst-lemma-expr etd (skip/cycle eq) =
      skip/cycle eq


    proc-subst-lemma-expr :
      ∀ {γ δ G P E Pr}
        {Γ : Vec Sort (suc γ)}
        {Δ : Vec Behav δ}
        {X : Fin (suc γ)}
      → (Γ - X)     ⊢e E                 ∶ lu Γ X
      → Γ       & Δ ⊢p P ◂ Pr            ∶ G
      → (Γ - X) & Δ ⊢p P ◂ [ E / X ]e Pr ∶ G

    proc-subst-lemma-expr etd (t/send gr etd′ ptd) =
      t/send gr
        (exp-subst etd′ etd)
        (proc-subst-lemma-expr etd ptd)

    proc-subst-lemma-expr {Γ = _ ∷ _} etd (t/recv {Br = Br} gr conts) =
      t/recv gr
        (transport-proc (subst/lu Br _)
        ∘ proc-subst-lemma-expr (exp-str etd)
        ∘ conts)

    proc-subst-lemma-expr etd (t/skip std) =
      t/skip (skip-subst-lemma-expr etd std)

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

  mutual

    skip-weaken-lemma-expr :
      ∀ {m γ δ ξ P Pr G S x}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {Ξ : Vec Behav ξ}
      → Γ & Δ & Ξ ⊢skip[ m ] P ◂ Pr ∶ G
      → insertAt Γ x S & Δ & Ξ ⊢skip[ m ] P ◂ weaken/proc/exp Pr x ∶ G

    skip-weaken-lemma-expr (skip/main td) =
      skip/main (proc-weaken-lemma-expr td)

    skip-weaken-lemma-expr (skip/step gr na ktd prod-gr) =
      skip/step gr na
        (λ gr′ →
          proj₁ (ktd gr′) , skip-weaken-lemma-expr (proj₂ (ktd gr′)))
        prod-gr

    skip-weaken-lemma-expr (skip/cycle eq) =
      skip/cycle eq


    proc-weaken-lemma-expr :
      ∀ {γ δ P Pr G S x}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
      → Γ & Δ ⊢p P ◂ Pr ∶ G
      → insertAt Γ x S & Δ ⊢p P ◂ weaken/proc/exp Pr x ∶ G

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

    proc-weaken-lemma-expr (t/skip std) =
      t/skip (skip-weaken-lemma-expr std)

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

  mutual

    skip-weaken-lemma :
      ∀ {m γ δ ξ G G' P Pr X}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {Ξ : Vec Behav ξ}
      → Γ & Δ & Ξ ⊢skip[ m ] P ◂ Pr ∶ G
      → Γ & insertAt Δ X G' & Ξ ⊢skip[ m ] P ◂ weaken/proc Pr X ∶ G

    skip-weaken-lemma (skip/main td) =
      skip/main (proc-weaken-lemma td)

    skip-weaken-lemma (skip/step gr na ktd prod-gr) =
      skip/step gr na
        (λ gr′ →
          proj₁ (ktd gr′) , skip-weaken-lemma (proj₂ (ktd gr′)))
        prod-gr

    skip-weaken-lemma (skip/cycle eq) =
      skip/cycle eq


    proc-weaken-lemma :
      ∀ {γ δ G G' P Pr X}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
      → Γ & Δ ⊢p P ◂ Pr ∶ G
      → Γ & insertAt Δ X G' ⊢p P ◂ weaken/proc Pr X ∶ G

    proc-weaken-lemma (t/send gr etd ptd) =
      t/send gr etd
        (proc-weaken-lemma ptd)

    proc-weaken-lemma (t/recv {Br = Br} gr conts) =
      t/recv gr
        ( transport-proc (proc-lookup-after-branch-weakening Br _ _)
        ∘ proc-weaken-lemma
        ∘ conts
        )

    proc-weaken-lemma (t/skip std) =
      t/skip (skip-weaken-lemma std)

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


  message-guarded/proc-subst :
    ∀ {γ δ X}
      {Pr′ : Proc γ δ}
      {Pr : Proc γ (suc δ)}
    → MessageGuarded Pr
    → MessageGuarded ([ Pr′ / X ]pr Pr)
  message-guarded/proc-subst mg/send =
    mg/send
  message-guarded/proc-subst mg/recv =
    mg/recv
  message-guarded/proc-subst (mg/if mg₁ mg₂) =
    mg/if
      (message-guarded/proc-subst mg₁)
      (message-guarded/proc-subst mg₂)

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

  mutual

    skip-subst-lemma :
      ∀ {m γ δ ξ G G' P Pr Pr'}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {Ξ : Vec Behav ξ}
        {X : Fin (suc δ)}
      → Γ & Δ ⊢p P ◂ Pr' ∶ G'
      → Γ & insertAt Δ X G' & Ξ ⊢skip[ m ] P ◂ Pr ∶ G
      → Γ & Δ & Ξ ⊢skip[ m ] P ◂ [ Pr' / X ]pr Pr ∶ G

    skip-subst-lemma ptd′ (skip/main td) =
      skip/main (proc-subst-lemma ptd′ td)

    skip-subst-lemma ptd′ (skip/step gr na ktd prod-gr) =
      skip/step gr na
        (λ gr′ →
          proj₁ (ktd gr′) , skip-subst-lemma ptd′ (proj₂ (ktd gr′)))
        prod-gr

    skip-subst-lemma ptd′ (skip/cycle eq) =
      skip/cycle eq


    proc-subst-lemma :
      ∀ {γ δ G G' P Pr Pr'}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {X : Fin (suc δ)}
      → Γ & Δ ⊢p P ◂ Pr' ∶ G'
      → Γ & insertAt Δ X G' ⊢p P ◂ Pr ∶ G
      → Γ & Δ ⊢p P ◂ [ Pr' / X ]pr Pr ∶ G

    proc-subst-lemma ptd′ (t/send gr etd ptd) =
      t/send gr etd
        (proc-subst-lemma ptd′ ptd)

    proc-subst-lemma ptd′ (t/recv {Br = Br} gr conts) =
      t/recv gr
        ( transport-proc (proc-lookup-after-branch-subst Br)
        ∘ proc-subst-lemma (proc-weaken-lemma-expr ptd′)
        ∘ conts
        )

    proc-subst-lemma ptd′ (t/skip std) =
      t/skip (skip-subst-lemma ptd′ std)

    proc-subst-lemma ptd′ (t/unskip tr ptd) =
      t/unskip tr (proc-subst-lemma ptd′ ptd)

    proc-subst-lemma ptd′ (t/if etd ptd ptd₁) =
      t/if etd
        (proc-subst-lemma ptd′ ptd)
        (proc-subst-lemma ptd′ ptd₁)

    proc-subst-lemma ptd′ (t/rec mg₁ ptd) =
      t/rec
        (message-guarded/proc-subst mg₁)
        (proc-subst-lemma
          (proc-weaken-lemma ptd′)
          ptd)

    proc-subst-lemma
      {G' = G'}
      {Δ = Δ}
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
      td/bisim ~ᵛ-refl eq ptd′

    proc-subst-lemma ptd′ (t/end done₁) =
      t/end done₁
