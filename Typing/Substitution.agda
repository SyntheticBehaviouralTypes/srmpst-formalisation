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
    )
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; _≢_)
open import Utils.Vec using (lookup-not-insertAt)
open import Definitions

module Typing.Substitution {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  private
    module M = Definitions.MPST wb
  open M
  open M.Subst
  open import Safety.Skip wb using (td/bisim)

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

  guarded/weaken-expr :
    ∀ {γ δ X}
      {Pr : Proc γ δ}
    → MessageGuarded Pr
    → MessageGuarded (weaken/proc/exp Pr X)
  guarded/weaken-expr mg/send =
    mg/send
  guarded/weaken-expr mg/recv =
    mg/recv
  guarded/weaken-expr (mg/if mmg mmg₁) =
    mg/if
      (guarded/weaken-expr mmg)
      (guarded/weaken-expr mmg₁)

  guarded/subst-expr :
    ∀ {γ δ}
      {E : Exp γ}
      {X : Fin (suc γ)}
      {Pr : Proc (suc γ) (suc δ)}
    → (mmg : MessageGuarded Pr)
    → MessageGuarded ([ E / X ]e Pr)
  guarded/subst-expr mg/send = mg/send
  guarded/subst-expr mg/recv = mg/recv
  guarded/subst-expr (mg/if mmgl mmgr) =
    mg/if
      (guarded/subst-expr mmgl)
      (guarded/subst-expr mmgr)

  transport-proc :
    ∀ {δ γ p p′ P G}
      {Δ : Vec Behav δ}
      {Γ : Vec Sort γ}
    → p ≡ p′
    → Γ & Δ ⊢p P ◂ p  ∶ G
    → Γ & Δ ⊢p P ◂ p′ ∶ G
  transport-proc = subst (λ x → _ & _ ⊢p _ ◂ x ∶ _)

  mutual

    skip/subst-expr :
      ∀ {m γ δ ξ G P E Pr}
        {Γ : Vec Sort (suc γ)}
        {Δ : Vec Behav δ}
        {Ξ : Vec Behav ξ}
        {X : Fin (suc γ)}
      → (Γ - X)     ⊢e E                 ∶ lu Γ X
      → Γ       & Δ & Ξ ⊢skip[ m ] P ◂ Pr            ∶ G
      → (Γ - X) & Δ & Ξ ⊢skip[ m ] P ◂ [ E / X ]e Pr ∶ G
    skip/subst-expr etd (skip/main td) =
      skip/main (typing/subst-expr etd td)
    skip/subst-expr etd (skip/step gr na ktd prod-gr) =
      skip/step gr na
        (λ gr′ →
          proj₁ (ktd gr′) , skip/subst-expr etd (proj₂ (ktd gr′)))
        prod-gr
    skip/subst-expr etd (skip/cycle eq) =
      skip/cycle eq

    typing/subst-expr :
      ∀ {γ δ G P E Pr}
        {Γ : Vec Sort (suc γ)}
        {Δ : Vec Behav δ}
        {X : Fin (suc γ)}
      → (Γ - X)     ⊢e E                 ∶ lu Γ X
      → Γ       & Δ ⊢p P ◂ Pr            ∶ G
      → (Γ - X) & Δ ⊢p P ◂ [ E / X ]e Pr ∶ G
    typing/subst-expr etd (t/send gr etd′ ptd) =
      t/send gr
        (exp-subst etd′ etd)
        (typing/subst-expr etd ptd)
    typing/subst-expr {Γ = _ ∷ _} etd (t/recv {Br = Br} gr conts) =
      t/recv gr
        (transport-proc (subst/lu Br _)
        ∘ typing/subst-expr (exp-str etd)
        ∘ conts)
    typing/subst-expr etd (t/skip std) =
      t/skip (skip/subst-expr etd std)
    typing/subst-expr etd (t/unskip tr ptd) =
      t/unskip tr (typing/subst-expr etd ptd)
    typing/subst-expr etd (t/if etd₁ ptd ptd₁) =
      t/if
        (exp-subst etd₁ etd)
        (typing/subst-expr etd ptd)
        (typing/subst-expr etd ptd₁)
    typing/subst-expr etd (t/rec mmg ptd) =
      t/rec
        (guarded/subst-expr mmg)
        (typing/subst-expr etd ptd)
    typing/subst-expr etd (t/var eq) =
      t/var eq
    typing/subst-expr etd (t/end done₁) =
      t/end done₁

  lookup/weaken-expr :
    ∀ {γ δ I i x}
    → (Br : Vec (Proc (suc γ) δ) I)
    → weaken/proc/exp (lu Br i) x
      ≡ lu (weaken/exp/branch Br x) i
  lookup/weaken-expr {i = zero} (_ ∷ _) =
    refl
  lookup/weaken-expr {i = suc i} (_ ∷ Br) =
    lookup/weaken-expr {i = i} Br

  mutual

    skip/weaken-expr :
      ∀ {m γ δ ξ P Pr G S x}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {Ξ : Vec Behav ξ}
      → Γ & Δ & Ξ ⊢skip[ m ] P ◂ Pr ∶ G
      → insertAt Γ x S & Δ & Ξ ⊢skip[ m ] P ◂ weaken/proc/exp Pr x ∶ G
    skip/weaken-expr (skip/main td) =
      skip/main (typing/weaken-expr td)
    skip/weaken-expr (skip/step gr na ktd prod-gr) =
      skip/step gr na
        (λ gr′ →
          proj₁ (ktd gr′) , skip/weaken-expr (proj₂ (ktd gr′)))
        prod-gr
    skip/weaken-expr (skip/cycle eq) =
      skip/cycle eq

    typing/weaken-expr :
      ∀ {γ δ P Pr G S x}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
      → Γ & Δ ⊢p P ◂ Pr ∶ G
      → insertAt Γ x S & Δ ⊢p P ◂ weaken/proc/exp Pr x ∶ G
    typing/weaken-expr (t/send gr etd ptd) =
      t/send gr
        (expr-weaken-lemma etd)
        (typing/weaken-expr ptd)
    typing/weaken-expr (t/recv {Br = Br} gr conts) =
      t/recv gr
        ( transport-proc (lookup/weaken-expr Br)
        ∘ typing/weaken-expr
        ∘ conts
        )
    typing/weaken-expr (t/skip std) =
      t/skip (skip/weaken-expr std)
    typing/weaken-expr (t/unskip tr ptd) =
      t/unskip tr
        (typing/weaken-expr ptd)
    typing/weaken-expr (t/if etd ptd₁ ptd₂) =
      t/if
        (expr-weaken-lemma etd)
        (typing/weaken-expr ptd₁)
        (typing/weaken-expr ptd₂)
    typing/weaken-expr (t/rec mg₁ ptd) =
      t/rec
        (guarded/weaken-expr mg₁)
        (typing/weaken-expr ptd)
    typing/weaken-expr (t/var eq) =
      t/var eq
    typing/weaken-expr (t/end done) =
      t/end done

  lookup/weaken-proc :
    ∀ {γ δ I}
    → (Br : Vec (Proc (suc γ) δ) I)
    → (i : Fin I)
    → (X : Fin (suc δ))
    → weaken/proc (lu Br i) X
      ≡ lu (weaken/proc/branch Br X) i
  lookup/weaken-proc (_ ∷ _) zero _ =
    refl
  lookup/weaken-proc (_ ∷ Br) (suc i) X =
    lookup/weaken-proc Br i X

  guarded/weaken-proc :
    ∀ {γ δ X}
      {Pr : Proc γ δ}
    → MessageGuarded Pr
    → MessageGuarded (weaken/proc Pr X)
  guarded/weaken-proc mg/send =
    mg/send
  guarded/weaken-proc mg/recv =
    mg/recv
  guarded/weaken-proc (mg/if mmg mmg₁) =
    mg/if
      (guarded/weaken-proc mmg)
      (guarded/weaken-proc mmg₁)

  mutual

    skip/weaken-proc :
      ∀ {m γ δ ξ G G' P Pr X}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {Ξ : Vec Behav ξ}
      → Γ & Δ & Ξ ⊢skip[ m ] P ◂ Pr ∶ G
      → Γ & insertAt Δ X G' & Ξ ⊢skip[ m ] P ◂ weaken/proc Pr X ∶ G
    skip/weaken-proc (skip/main td) =
      skip/main (typing/weaken-proc td)
    skip/weaken-proc (skip/step gr na ktd prod-gr) =
      skip/step gr na
        (λ gr′ →
          proj₁ (ktd gr′) , skip/weaken-proc (proj₂ (ktd gr′)))
        prod-gr
    skip/weaken-proc (skip/cycle eq) =
      skip/cycle eq

    typing/weaken-proc :
      ∀ {γ δ G G' P Pr X}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
      → Γ & Δ ⊢p P ◂ Pr ∶ G
      → Γ & insertAt Δ X G' ⊢p P ◂ weaken/proc Pr X ∶ G
    typing/weaken-proc (t/send gr etd ptd) =
      t/send gr etd
        (typing/weaken-proc ptd)
    typing/weaken-proc (t/recv {Br = Br} gr conts) =
      t/recv gr
        ( transport-proc (lookup/weaken-proc Br _ _)
        ∘ typing/weaken-proc
        ∘ conts
        )
    typing/weaken-proc (t/skip std) =
      t/skip (skip/weaken-proc std)
    typing/weaken-proc (t/unskip tr ptd) =
      t/unskip tr
        (typing/weaken-proc ptd)
    typing/weaken-proc (t/if etd ptd ptd₁) =
      t/if etd
        (typing/weaken-proc ptd)
        (typing/weaken-proc ptd₁)
    typing/weaken-proc (t/rec mg₁ ptd) =
      t/rec
        (guarded/weaken-proc mg₁)
        (typing/weaken-proc ptd)
    typing/weaken-proc
      {G' = G'}
      {X = X}
      {Δ = Δ}
      (t/var {X = Y} eq)
      rewrite sym (insertAt-punchIn Δ X G' Y) =
      t/var eq
    typing/weaken-proc (t/end done₁) =
      t/end done₁

  lookup/subst-proc :
    ∀ {γ δ I Pr X i}
    → (Br : Vec (Proc (suc γ) (suc δ)) I)
    → [ weaken/proc/exp Pr zero / X ]pr (lu Br i)
      ≡ lu ([ Pr / X ]prch Br) i
  lookup/subst-proc {i = zero} (_ ∷ _) =
    refl
  lookup/subst-proc {i = suc i} (_ ∷ Br) =
    lookup/subst-proc {i = i} Br

  guarded/subst-proc :
    ∀ {γ δ X}
      {Pr′ : Proc γ δ}
      {Pr : Proc γ (suc δ)}
    → MessageGuarded Pr
    → MessageGuarded ([ Pr′ / X ]pr Pr)
  guarded/subst-proc mg/send =
    mg/send
  guarded/subst-proc mg/recv =
    mg/recv
  guarded/subst-proc (mg/if mg₁ mg₂) =
    mg/if
      (guarded/subst-proc mg₁)
      (guarded/subst-proc mg₂)

  mutual

    skip/subst-proc :
      ∀ {m γ δ ξ G G' P Pr Pr'}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {Ξ : Vec Behav ξ}
        {X : Fin (suc δ)}
      → Γ & Δ ⊢p P ◂ Pr' ∶ G'
      → Γ & insertAt Δ X G' & Ξ ⊢skip[ m ] P ◂ Pr ∶ G
      → Γ & Δ & Ξ ⊢skip[ m ] P ◂ [ Pr' / X ]pr Pr ∶ G
    skip/subst-proc ptd′ (skip/main td) =
      skip/main (typing/subst-proc ptd′ td)
    skip/subst-proc ptd′ (skip/step gr na ktd prod-gr) =
      skip/step gr na
        (λ gr′ →
          proj₁ (ktd gr′) , skip/subst-proc ptd′ (proj₂ (ktd gr′)))
        prod-gr
    skip/subst-proc ptd′ (skip/cycle eq) =
      skip/cycle eq

    typing/subst-proc :
      ∀ {γ δ G G' P Pr Pr'}
        {Γ : Vec Sort γ}
        {Δ : Vec Behav δ}
        {X : Fin (suc δ)}
      → Γ & Δ ⊢p P ◂ Pr' ∶ G'
      → Γ & insertAt Δ X G' ⊢p P ◂ Pr ∶ G
      → Γ & Δ ⊢p P ◂ [ Pr' / X ]pr Pr ∶ G
    typing/subst-proc ptd′ (t/send gr etd ptd) =
      t/send gr etd
        (typing/subst-proc ptd′ ptd)
    typing/subst-proc ptd′ (t/recv {Br = Br} gr conts) =
      t/recv gr
        ( transport-proc (lookup/subst-proc Br)
        ∘ typing/subst-proc (typing/weaken-expr ptd′)
        ∘ conts
        )
    typing/subst-proc ptd′ (t/skip std) =
      t/skip (skip/subst-proc ptd′ std)
    typing/subst-proc ptd′ (t/unskip tr ptd) =
      t/unskip tr (typing/subst-proc ptd′ ptd)
    typing/subst-proc ptd′ (t/if etd ptd ptd₁) =
      t/if etd
        (typing/subst-proc ptd′ ptd)
        (typing/subst-proc ptd′ ptd₁)
    typing/subst-proc ptd′ (t/rec mg₁ ptd) =
      t/rec
        (guarded/subst-proc mg₁)
        (typing/subst-proc
          (typing/weaken-proc ptd′)
          ptd)
    typing/subst-proc
      {G' = G'}
      {Δ = Δ}
      {X = X}
      ptd′
      (t/var {X = X′} eq)
      with X ≟f X′
    ... | no ¬eq
      rewrite lookup-not-insertAt
                {V = Δ}
                {a = G'}
                X
                X′
                ¬eq =
      t/var eq
    ... | yes refl
      rewrite insertAt-lookup Δ X G' =
      td/bisim ~ᵛ-refl eq ptd′
    typing/subst-proc ptd′ (t/end done₁) =
      t/end done₁
