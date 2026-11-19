{-# OPTIONS --guardedness #-}

-- Weakening and substitution for the paper's judgements, the unfolding of
-- `rec`, and the `⊢a` faces `Safety/` uses.

open import Data.Nat using (ℕ; suc)
open import Data.Fin
  using (Fin; zero; suc; punchOut)
  renaming (_≟_ to _≟f_)
open import Data.Vec
  using (Vec; []; _∷_; insertAt)
  renaming (lookup to lu; removeAt to _-_)
open import Data.Vec.Properties
  using
    ( insertAt-punchIn
    ; insertAt-lookup
    )
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Data.Fin.Properties using (punchIn-punchOut)
open import Definitions.Typing.Declarative
open import Utils.Family using (_∋_↦_; here; there)

module Definitions.Typing.Substitution {N : ℕ}{B : BTheory N}(wb : WellBehaved B) where
  private
    module M = MPST wb
  open M
  open M.Subst
  open import Definitions.Typing.Properties wb using (td/≐; ≐ᵛ-refl)
  open import Definitions.Typing.Alg wb using (_⊢at_∶_)
  open import Definitions.Typing.AlgNorm wb using (td⇒at)
  open import Definitions.Typing.AlgDeclarative wb using (at⇒typing)

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

  -- Each branch map sends the branch of `ℓ` to the branch of `ℓ`.
  ∋/subst-expr :
    ∀ {γ δ n ℓ}
      {E : Exp γ}
      {X}
      {Br : Vec _ n}
      {Pr : Proc (suc γ) δ}
    → Br ∋ ℓ ↦ Pr
    → [ E / X ]ech Br ∋ ℓ ↦ [ E / suc X ]e Pr
  ∋/subst-expr here = here
  ∋/subst-expr {Br = nothing ∷ _} (there p) = there (∋/subst-expr p)
  ∋/subst-expr {Br = just _  ∷ _} (there p) = there (∋/subst-expr p)

  guarded/weaken-expr :
    ∀ {γ δ X}
      {Pr : Proc γ δ}
    → MessageGuarded Pr
    → MessageGuarded (weaken/proc/exp Pr X)
  guarded/weaken-expr mg/send =
    mg/send
  guarded/weaken-expr mg/recv =
    mg/recv
  guarded/weaken-expr (mg/let mmg) =
    mg/let (guarded/weaken-expr mmg)
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
  guarded/subst-expr (mg/let mmg) = mg/let (guarded/subst-expr mmg)
  guarded/subst-expr (mg/if mmgl mmgr) =
    mg/if
      (guarded/subst-expr mmgl)
      (guarded/subst-expr mmgr)

  mutual

    skip/subst-expr :
      ∀ {γ δ ξ G R E Pr}
        {Γ : Vec Sort (suc γ)}
        {Δ : Vec Cls δ}
        {Ξ : Vec Cls ξ}
        {X : Fin (suc γ)}
      → (Γ - X)     ⊢e E                 ∶ lu Γ X
      → Γ       & Δ & Ξ ⊢[ R ] Pr            ∶ G
      → (Γ - X) & Δ & Ξ ⊢[ R ] [ E / X ]e Pr ∶ G
    skip/subst-expr etd (skip-main td) =
      skip-main (typing/subst-expr etd td)
    skip/subst-expr etd (skip-step ex na k) =
      skip-step ex na
        (λ st → skip/subst-expr etd (k st))
    skip/subst-expr etd (skip-cycle mem inT) =
      skip-cycle mem inT

    typing/subst-expr :
      ∀ {γ δ G R E Pr}
        {Γ : Vec Sort (suc γ)}
        {Δ : Vec Cls δ}
        {X : Fin (suc γ)}
      → (Γ - X)     ⊢e E                 ∶ lu Γ X
      → Γ       & Δ ⊢[ R ] Pr            ∶ G
      → (Γ - X) & Δ ⊢[ R ] [ E / X ]e Pr ∶ G
    typing/subst-expr etd (send fi gr etd′ ptd) =
      send fi gr
        (exp-subst etd′ etd)
        (typing/subst-expr etd ptd)
    typing/subst-expr {Γ = _ ∷ _} etd (recv fi p∉ ex conts) =
      recv fi p∉ ex λ gr′ →
        let _ , br , td = conts gr′
        in _ , ∋/subst-expr br
             , typing/subst-expr (expr-weaken-lemma {x = zero} etd) td
    typing/subst-expr etd (skip std) =
      skip (skip/subst-expr etd std)
    typing/subst-expr etd (forward ptd run) =
      forward (typing/subst-expr etd ptd) run
    typing/subst-expr {Γ = _ ∷ _} etd (let′ etd₁ ptd) =
      let′
        (exp-subst etd₁ etd)
        (typing/subst-expr (expr-weaken-lemma {x = zero} etd) ptd)
    typing/subst-expr etd (if etd₁ ptd ptd₁) =
      if
        (exp-subst etd₁ etd)
        (typing/subst-expr etd ptd)
        (typing/subst-expr etd ptd₁)
    typing/subst-expr etd (rec ptd mmg) =
      rec
        (typing/subst-expr etd ptd)
        (guarded/subst-expr mmg)
    typing/subst-expr etd (var eq) =
      var eq
    typing/subst-expr etd (end out) =
      end out

  ∋/weaken-expr :
    ∀ {γ δ n ℓ x}
      {Br : Vec _ n}
      {Pr : Proc (suc γ) δ}
    → Br ∋ ℓ ↦ Pr
    → weaken/exp/branch Br x ∋ ℓ ↦ weaken/proc/exp Pr x
  ∋/weaken-expr here = here
  ∋/weaken-expr {Br = nothing ∷ _} (there p) = there (∋/weaken-expr p)
  ∋/weaken-expr {Br = just _  ∷ _} (there p) = there (∋/weaken-expr p)

  mutual

    skip/weaken-expr :
      ∀ {γ δ ξ R Pr G S x}
        {Γ : Vec Sort γ}
        {Δ : Vec Cls δ}
        {Ξ : Vec Cls ξ}
      → Γ & Δ & Ξ ⊢[ R ] Pr ∶ G
      → insertAt Γ x S & Δ & Ξ ⊢[ R ] weaken/proc/exp Pr x ∶ G
    skip/weaken-expr (skip-main td) =
      skip-main (typing/weaken-expr td)
    skip/weaken-expr (skip-step ex na k) =
      skip-step ex na
        (λ st → skip/weaken-expr (k st))
    skip/weaken-expr (skip-cycle mem inT) =
      skip-cycle mem inT

    typing/weaken-expr :
      ∀ {γ δ R Pr G S x}
        {Γ : Vec Sort γ}
        {Δ : Vec Cls δ}
      → Γ & Δ ⊢[ R ] Pr ∶ G
      → insertAt Γ x S & Δ ⊢[ R ] weaken/proc/exp Pr x ∶ G
    typing/weaken-expr (send fi gr etd ptd) =
      send fi gr
        (expr-weaken-lemma etd)
        (typing/weaken-expr ptd)
    typing/weaken-expr (recv fi p∉ ex conts) =
      recv fi p∉ ex λ gr′ →
        let _ , br , td = conts gr′
        in _ , ∋/weaken-expr br , typing/weaken-expr td
    typing/weaken-expr (skip std) =
      skip (skip/weaken-expr std)
    typing/weaken-expr (forward ptd run) =
      forward (typing/weaken-expr ptd) run
    typing/weaken-expr (let′ etd ptd) =
      let′
        (expr-weaken-lemma etd)
        (typing/weaken-expr ptd)
    typing/weaken-expr (if etd ptd₁ ptd₂) =
      if
        (expr-weaken-lemma etd)
        (typing/weaken-expr ptd₁)
        (typing/weaken-expr ptd₂)
    typing/weaken-expr (rec ptd mg₁) =
      rec
        (typing/weaken-expr ptd)
        (guarded/weaken-expr mg₁)
    typing/weaken-expr (var eq) =
      var eq
    typing/weaken-expr (end out) =
      end out

  ∋/weaken-proc :
    ∀ {γ δ n ℓ X}
      {Br : Vec _ n}
      {Pr : Proc (suc γ) δ}
    → Br ∋ ℓ ↦ Pr
    → weaken/proc/branch Br X ∋ ℓ ↦ weaken/proc Pr X
  ∋/weaken-proc here = here
  ∋/weaken-proc {Br = nothing ∷ _} (there p) = there (∋/weaken-proc p)
  ∋/weaken-proc {Br = just _  ∷ _} (there p) = there (∋/weaken-proc p)

  guarded/weaken-proc :
    ∀ {γ δ X}
      {Pr : Proc γ δ}
    → MessageGuarded Pr
    → MessageGuarded (weaken/proc Pr X)
  guarded/weaken-proc mg/send =
    mg/send
  guarded/weaken-proc mg/recv =
    mg/recv
  guarded/weaken-proc (mg/let mmg) =
    mg/let (guarded/weaken-proc mmg)
  guarded/weaken-proc (mg/if mmg mmg₁) =
    mg/if
      (guarded/weaken-proc mmg)
      (guarded/weaken-proc mmg₁)

  mutual

    skip/weaken-proc :
      ∀ {γ δ ξ G G' R Pr X}
        {Γ : Vec Sort γ}
        {Δ : Vec Cls δ}
        {Ξ : Vec Cls ξ}
      → Γ & Δ & Ξ ⊢[ R ] Pr ∶ G
      → Γ & insertAt Δ X G' & Ξ ⊢[ R ] weaken/proc Pr X ∶ G
    skip/weaken-proc (skip-main td) =
      skip-main (typing/weaken-proc td)
    skip/weaken-proc (skip-step ex na k) =
      skip-step ex na
        (λ st → skip/weaken-proc (k st))
    skip/weaken-proc (skip-cycle mem inT) =
      skip-cycle mem inT

    typing/weaken-proc :
      ∀ {γ δ G G' R Pr X}
        {Γ : Vec Sort γ}
        {Δ : Vec Cls δ}
      → Γ & Δ ⊢[ R ] Pr ∶ G
      → Γ & insertAt Δ X G' ⊢[ R ] weaken/proc Pr X ∶ G
    typing/weaken-proc (send fi gr etd ptd) =
      send fi gr etd
        (typing/weaken-proc ptd)
    typing/weaken-proc (recv fi p∉ ex conts) =
      recv fi p∉ ex λ gr′ →
        let _ , br , td = conts gr′
        in _ , ∋/weaken-proc br , typing/weaken-proc td
    typing/weaken-proc (skip std) =
      skip (skip/weaken-proc std)
    typing/weaken-proc (forward ptd run) =
      forward (typing/weaken-proc ptd) run
    typing/weaken-proc (let′ etd ptd) =
      let′ etd (typing/weaken-proc ptd)
    typing/weaken-proc (if etd ptd ptd₁) =
      if etd
        (typing/weaken-proc ptd)
        (typing/weaken-proc ptd₁)
    typing/weaken-proc (rec ptd mg₁) =
      rec
        (typing/weaken-proc ptd)
        (guarded/weaken-proc mg₁)
    typing/weaken-proc
      {G' = G'}
      {X = X}
      {Δ = Δ}
      (var {X = Y} eq)
      rewrite sym (insertAt-punchIn Δ X G' Y) =
      var eq
    typing/weaken-proc (end out) =
      end out

  ∋/subst-proc :
    ∀ {γ δ n ℓ X}
      {Pr : Proc γ δ}
      {Br : Vec _ n}
      {Pr′ : Proc (suc γ) (suc δ)}
    → Br ∋ ℓ ↦ Pr′
    → [ Pr / X ]prch Br ∋ ℓ ↦ [ weaken/proc/exp Pr zero / X ]pr Pr′
  ∋/subst-proc here = here
  ∋/subst-proc {Br = nothing ∷ _} (there p) = there (∋/subst-proc p)
  ∋/subst-proc {Br = just _  ∷ _} (there p) = there (∋/subst-proc p)

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
  guarded/subst-proc (mg/let mg) =
    mg/let (guarded/subst-proc mg)
  guarded/subst-proc (mg/if mg₁ mg₂) =
    mg/if
      (guarded/subst-proc mg₁)
      (guarded/subst-proc mg₂)

  mutual

    skip/subst-proc :
      ∀ {γ δ ξ G G' R Pr Pr'}
        {Γ : Vec Sort γ}
        {Δ : Vec Cls δ}
        {Ξ : Vec Cls ξ}
        {X : Fin (suc δ)}
      → Γ & Δ ⊢[ R ] Pr' ∶ G'
      → Γ & insertAt Δ X G' & Ξ ⊢[ R ] Pr ∶ G
      → Γ & Δ & Ξ ⊢[ R ] [ Pr' / X ]pr Pr ∶ G
    skip/subst-proc ptd′ (skip-main td) =
      skip-main (typing/subst-proc ptd′ td)
    skip/subst-proc ptd′ (skip-step ex na k) =
      skip-step ex na
        (λ st → skip/subst-proc ptd′ (k st))
    skip/subst-proc ptd′ (skip-cycle mem inT) =
      skip-cycle mem inT

    typing/subst-proc :
      ∀ {γ δ G G' R Pr Pr'}
        {Γ : Vec Sort γ}
        {Δ : Vec Cls δ}
        {X : Fin (suc δ)}
      → Γ & Δ ⊢[ R ] Pr' ∶ G'
      → Γ & insertAt Δ X G' ⊢[ R ] Pr ∶ G
      → Γ & Δ ⊢[ R ] [ Pr' / X ]pr Pr ∶ G
    typing/subst-proc ptd′ (send fi gr etd ptd) =
      send fi gr etd
        (typing/subst-proc ptd′ ptd)
    typing/subst-proc ptd′ (recv fi p∉ ex conts) =
      recv fi p∉ ex λ gr′ →
        let _ , br , td = conts gr′
        in _ , ∋/subst-proc br , typing/subst-proc (typing/weaken-expr ptd′) td
    typing/subst-proc ptd′ (skip std) =
      skip (skip/subst-proc ptd′ std)
    typing/subst-proc ptd′ (forward ptd run) =
      forward (typing/subst-proc ptd′ ptd) run
    typing/subst-proc ptd′ (let′ etd ptd) =
      let′ etd (typing/subst-proc (typing/weaken-expr ptd′) ptd)
    typing/subst-proc ptd′ (if etd ptd ptd₁) =
      if etd
        (typing/subst-proc ptd′ ptd)
        (typing/subst-proc ptd′ ptd₁)
    typing/subst-proc ptd′ (rec ptd mg₁) =
      rec
        (typing/subst-proc
          (typing/weaken-proc ptd′)
          ptd)
        (guarded/subst-proc mg₁)
    typing/subst-proc
      {G' = G'}
      {Δ = Δ}
      {X = X}
      ptd′
      (var {X = X′} eq)
      with X ≟f X′
    ... | no ¬eq =
      var
        (subst (_≐ _)
          (trans (cong (lu (insertAt Δ X G')) (sym (punchIn-punchOut ¬eq)))
                 (insertAt-punchIn Δ X G' (punchOut ¬eq)))
          eq)
    ... | yes refl
      rewrite insertAt-lookup Δ X G' =
      td/≐ ≐ᵛ-refl eq ptd′
    typing/subst-proc ptd′ (end out) =
      end out

  -- ══════════════════════════════════════════════════════════════════
  --  `rec` unfolding, and the `⊢a` faces
  -- ══════════════════════════════════════════════════════════════════

  mutual

    rec/unfold :
      ∀ {G R Pr}
      → [] & [] ⊢[ R ] rec Pr ∶ G
      → [] & [] ⊢[ R ] unfold/proc Pr ∶ G

    rec/unfold (rec ptd mmg) =
      typing/subst-proc (rec ptd mmg) ptd

    rec/unfold (skip std) =
      skip (skip/rec/unfold std)

    rec/unfold (forward td run) =
      forward (rec/unfold td) run

    skip/rec/unfold :
      ∀ {ξ}
        {Ξ : Vec Cls ξ}
        {G R Pr}
      → [] & [] & Ξ ⊢[ R ] rec Pr ∶ G
      → [] & [] & Ξ ⊢[ R ] unfold/proc Pr ∶ G
    skip/rec/unfold (skip-main td) =
      skip-main (rec/unfold td)
    skip/rec/unfold (skip-step ex na k) =
      skip-step ex na
        (λ st → skip/rec/unfold (k st))
    skip/rec/unfold (skip-cycle mem inT) =
      skip-cycle mem inT

  -- The `⊢a` operations `Safety/` uses, each a round trip through `⊢`.
  module _ (bal : Balanced B) where

    at/rec/unfold :
      ∀ {G P Pr}
      → [] ⊢at P ◂ rec Pr ∶ ([] , G)
      → [] ⊢at P ◂ unfold/proc Pr ∶ ([] , G)
    at/rec/unfold td = td⇒at bal (rec/unfold (at⇒typing td))

    at/subst-expr :
      ∀ {γ δ G P E Pr}
        {Γ : Vec Sort (suc γ)}
        {ws : Vec Behav δ}
        {X : Fin (suc γ)}
      → (Γ - X) ⊢e E ∶ lu Γ X
      → Γ ⊢at P ◂ Pr ∶ (ws , G)
      → (Γ - X) ⊢at P ◂ [ E / X ]e Pr ∶ (ws , G)
    at/subst-expr etd td = td⇒at bal (typing/subst-expr etd (at⇒typing td))

    -- Along a `¬P` run, then `~`.
    at/unskip :
      ∀ {γ δ G G″ G′ P Pr}
        {Γ : Vec Sort γ}
        {ws : Vec Behav δ}
      → G -[¬ P ]->* G″
      → G″ ~ G′
      → Γ ⊢at P ◂ Pr ∶ (ws , G)
      → Γ ⊢at P ◂ Pr ∶ (ws , G′)
    at/unskip tr eq td =
      td⇒at bal (td/≐ ≐ᵛ-refl eq (forward (at⇒typing td) (run⇒ᶜ tr)))
