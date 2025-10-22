{-# OPTIONS --guardedness #-}
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin ; zero ; suc ; compare ; punchIn ; punchOut) renaming (_≟_ to _≟f_)
open import Data.Vec using (Vec ; _∷_ ; _[_]=_ ; insertAt ) renaming (lookup to lu; removeAt to _-_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Nullary using (False; ¬_; yes; no)
open import Relation.Nullary.Decidable using (toWitness ; fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; subst ; _≢_)
open import Utils.Fin using (refl-is-equal ; reflect-lookup)
open import Utils.Vec using (lookup-not-insertAt)
open import Data.Fin.Properties
  using (punchIn-punchOut)
open import Data.Vec.Properties
  using (insertAt-punchIn ; insertAt-lookup ; removeAt-insertAt ; removeAt-punchOut)

open import Definitions

module SubstitutionProperties {N : ℕ}{B : BTheory N}(BP : BT-Prop B) where
  open module M = Definitions.MPST(BP)
  open M
  open M.Subst

  exp-wkn-lemma : ∀{γ}{Γ : Vec Sort γ}{E S S' x} ->
    Γ ⊢e E ∶ S -> insertAt Γ x S' ⊢e weaken/exp E x ∶ S
  exp-wkn-lemma (te/val V) = te/val V
  exp-wkn-lemma (te/minus1 td) = te/minus1 (exp-wkn-lemma td)
  exp-wkn-lemma (te/is-zero td) = te/is-zero(exp-wkn-lemma td)
  exp-wkn-lemma {Γ = Γ}{S' = S'}{x = x} (te/var {y})
    rewrite sym (insertAt-punchIn Γ x S' y) = te/var

  exp-subst-lemma :
    ∀{S S' γ}{Γ : Vec Sort γ}{E x V} ->
    -- here before substitution we have an extra variable. Using this
    -- lemma will need rewriting the context into such an insert
    -- statement.
    insertAt Γ x S' ⊢e E ∶ S ->
    ⊢v V ∶ S' ->
    Γ ⊢e [ val V / x ]exp E ∶ S
  exp-subst-lemma (te/val V) vtd = te/val V
  exp-subst-lemma (te/minus1 etd) vtd = te/minus1 (exp-subst-lemma etd vtd)
  exp-subst-lemma (te/is-zero etd) vtd = te/is-zero (exp-subst-lemma etd vtd)
  exp-subst-lemma {x = x} (te/var {y}) vtd with x ≟f y
  exp-subst-lemma {S' = S'}{Γ = Γ}{x = x}{V = V}
    (te/var {y}) vtd | yes refl rewrite insertAt-lookup Γ x S' =
      te/val vtd
  exp-subst-lemma {S' = S'}{Γ = Γ}{x = x}{V = V}
    (te/var {y}) vtd | no eq
    rewrite lookup-not-insertAt {V = Γ}{a = S'} x y eq = te/var

  removeAt/suc : ∀{A : Set}{γ}{x : A}{i : Fin (suc γ)}{Γ : Vec A (suc γ)}
    → (x ∷ Γ) - suc i ≡ x ∷ (Γ - i)
  removeAt/suc {A} {γ} {x} {i} {_ ∷ Γ} = refl

  subst/lu : ∀{γ δ I}{E : Exp γ}{X}(Br : Vec (Proc (suc γ) δ) (suc I)) i
    → ([ E / suc X ]e lu Br i) ≡ lu ([ E / X ]ech Br) i
  subst/lu (x ∷ Br) zero = refl
  subst/lu {I = suc I} (x ∷ Br) (suc i) = subst/lu Br i

  is-comm/subst/exp : ∀ {γ δ Q X}{E : Exp γ}{Pr : Proc (suc γ) δ}
                      → is-comm Q Pr
                      → is-comm Q ([ E / X ]e Pr)
  is-comm/subst/exp is-send = is-send
  is-comm/subst/exp is-recv = is-recv

  is-comm/subst : ∀ {γ δ Q X E}{Pr : Proc γ (suc δ)}
                      → is-comm Q Pr
                      → is-comm Q ([ E / X ]pr Pr)
  is-comm/subst is-send = is-send
  is-comm/subst is-recv = is-recv

  is-comm/wk/pr/exp : ∀ {γ δ P x}{Pr : Proc γ δ}
                      → is-comm P Pr
                      → is-comm P (weaken/proc/exp Pr x)
  is-comm/wk/pr/exp is-send = is-send
  is-comm/wk/pr/exp is-recv = is-recv

  is-comm/wk/pr : ∀ {γ δ P x}{Pr : Proc γ δ}
                      → is-comm P Pr
                      → is-comm P (weaken/proc Pr x)
  is-comm/wk/pr is-send = is-send
  is-comm/wk/pr is-recv = is-recv

  expr-subst-lemma : ∀{γ δ g G P E Pr}
    → ∀ {Γ : Vec Sort (suc γ)}{Δ : Vec Behav δ}{X : Fin (suc γ)}
    → (Γ - X) ⊢e E ∶ lu Γ X
    → Γ     & Δ / G ↑ P ⊢p< g > Pr
    → (Γ - X) & Δ / G ↑ P ⊢p< g > ([ E / X ]e Pr)
  expr-subst-lemma etd (t/send gr etd₁ ptd)
    = t/send gr (exp-subst etd₁ etd) (expr-subst-lemma etd ptd)
  expr-subst-lemma {E = E}{Γ = S ∷ Γ}{X = X} etd (t/recv {Br = Br} x conts)
    = t/recv x (λ {i = i} y →
        let etd' = exp-str etd
            ky = expr-subst-lemma {E = weaken/exp E zero}{X = suc X}
                                  etd' (conts y)
        in subst (λ Pr -> _ & _ / _ ↑ _ ⊢p< ng > Pr) (subst/lu Br i) ky)
  expr-subst-lemma {E = E}{Γ = S ∷ Γ}{X = X} etd (t/skip x x₃ conts)
    = t/skip (is-comm/subst/exp x) x₃
             (λ gr → expr-subst-lemma etd (conts gr))
  expr-subst-lemma etd (t/if etd₁ ptd ptd₁)
    = t/if (exp-subst etd₁ etd)
           (expr-subst-lemma etd ptd)
           (expr-subst-lemma etd ptd₁)
  expr-subst-lemma etd (t/rec gr ptd) = t/rec gr (expr-subst-lemma etd ptd)
  expr-subst-lemma etd (t/var x gr) = t/var x gr
  expr-subst-lemma etd (t/end p∉g) = t/end p∉g

  -- small lemma to show that weakening branches commutes with lookup
  branch-wkn-lookup-perm : ∀{γ δ I}{Br : Vec (Proc (suc γ) δ) I}{i x} ->
    weaken/proc/exp (lu Br i) x ≡ lu (weaken/exp/branch Br x) i
  branch-wkn-lookup-perm {Br = Pr ∷ Br} {i = zero} = refl
  branch-wkn-lookup-perm {Br = Pr ∷ Br} {i = suc i} = branch-wkn-lookup-perm {Br = Br}{i = i}

  proc-exp-wkn-lemma :
    ∀{S γ δ g}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{G P Pr}{x : Fin (suc γ)} ->
    Γ & Δ / G ↑ P ⊢p< g > Pr ->
    insertAt Γ x S & Δ / G ↑ P ⊢p< g > weaken/proc/exp Pr x
  proc-exp-wkn-lemma (t/send gr etd td)
    = t/send gr (exp-wkn-lemma etd) (proc-exp-wkn-lemma td)
  proc-exp-wkn-lemma (t/recv {Br = Br} r k)
    = t/recv r λ gr → subst (λ Pr → _ & _ / _ ↑ _ ⊢p< _ > Pr)
                            (branch-wkn-lookup-perm {Br = Br})
                            (proc-exp-wkn-lemma (k gr))
  proc-exp-wkn-lemma (t/skip r p k)
    = t/skip (is-comm/wk/pr/exp r) p
             λ gr → proc-exp-wkn-lemma (k gr)
  proc-exp-wkn-lemma (t/if etd td td₁)
    = t/if (exp-wkn-lemma etd) (proc-exp-wkn-lemma td) (proc-exp-wkn-lemma td₁)
  proc-exp-wkn-lemma (t/rec x td) = t/rec x (proc-exp-wkn-lemma td)
  proc-exp-wkn-lemma (t/var x gr) = t/var x gr
  proc-exp-wkn-lemma (t/end p∉g) = t/end p∉g

  branch-subst-lookup-perm :  ∀{γ δ I}{Br : Vec (Proc (suc γ) δ) I}{N x i} ->
       [ N / suc x ]e (lu Br i)  ≡ lu ([ N / x ]ech Br) i
  branch-subst-lookup-perm {Br = Pr ∷ Br} {i = zero} = refl
  branch-subst-lookup-perm {Br = _ ∷ Br} {i = suc i} = branch-subst-lookup-perm {Br = Br} {i = i}

  branch-wknpr-lookup-perm : ∀{γ δ I}(Br : Vec (Proc (suc γ) δ) I) i X ->
    weaken/proc (lu Br i) X ≡ lu (weaken/proc/branch Br X) i
  branch-wknpr-lookup-perm (Pr ∷ Br) zero X = refl
  branch-wknpr-lookup-perm (_ ∷ Br) (suc i) X = branch-wknpr-lookup-perm Br i X

  -- weakening lemma for procs with proc vars
  proc-wkn-lemma : ∀{γ δ g}{Γ : Vec Sort γ}{Δ : Vec Behav δ}
    → ∀ {G G' P Pr X}
    → Γ & Δ / G ↑ P ⊢p< g > Pr
    → Γ & insertAt Δ X G' / G ↑ P ⊢p< g > weaken/proc Pr X
  proc-wkn-lemma (t/send gr etd td) = t/send gr etd (proc-wkn-lemma td)
  proc-wkn-lemma {X = X}(t/recv {Br = Br} x k)
    = t/recv x λ {i = i} gr →
             subst (λ Pr → _ & _ / _ ↑ _ ⊢p< _ > Pr )
                   (branch-wknpr-lookup-perm Br i X) (proc-wkn-lemma (k gr))
  proc-wkn-lemma (t/skip r p k)
    = t/skip (is-comm/wk/pr r) p λ gr → proc-wkn-lemma (k gr)
  proc-wkn-lemma (t/if etd td td₁)
    = t/if etd (proc-wkn-lemma td) (proc-wkn-lemma td₁)
  proc-wkn-lemma (t/rec x td) = t/rec x (proc-wkn-lemma td)
  proc-wkn-lemma {Δ = Δ}{G' = G'}{X = X}(t/var {X = Y} x gr)
    rewrite sym (insertAt-punchIn Δ X G' Y) = t/var x gr
  proc-wkn-lemma (t/end p∉g) = t/end p∉g

  branch-prsub-lookup-perm : ∀{γ δ I}{Br : Vec (Proc (suc γ) (suc δ)) I} {Pr X i} ->
    ([ weaken/proc/exp Pr zero / X ]pr (lu Br i)) ≡ lu ([ Pr / X ]prch Br) i
  branch-prsub-lookup-perm {Br = Pr ∷ Br} {i = zero} = refl
  branch-prsub-lookup-perm {Br = _ ∷ Br} {i = suc i} = branch-prsub-lookup-perm {Br = Br}{i = i}

--   -- lookup lemma (This should be "easy" to tidy up)
--   -- TODO "tidy it up" and move it to Vec.Utils
  lookup-insert-punchOut : ∀{A : Set}{γ}(Γ : Vec A γ){x S y} ->
    (x≢y : x ≢ y) -> lu (insertAt Γ x S) y ≡ lu Γ (punchOut x≢y)
  lookup-insert-punchOut Γ {x = x}{S}{y} x≢y rewrite sym(removeAt-insertAt Γ x S) with
    sym (removeAt-punchOut (insertAt Γ x S) x≢y)
  ...| res rewrite removeAt-insertAt Γ x S = res

  open HeadAct
  proc-subst-lemma :
    ∀{γ δ g}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{X : Fin (suc δ)}
    → ∀ {G G' P Pr Pr'}
    → Γ & insertAt Δ X G' / G ↑ P ⊢p< g > Pr
    → Γ & Δ / G' ↑ P ⊢p< ng > Pr'
    → Γ & Δ / G ↑ P ⊢p< g > ([ Pr' / X ]pr Pr)
  proc-subst-lemma (t/send gr etd x) y = t/send gr etd (proc-subst-lemma x y)
  proc-subst-lemma {Γ = Γ}{Δ = Δ}{X = X}{G' = G'}{Pr' = Pr'}
                   (t/recv {p = p}{Br = Br} x k) y
    = t/recv x λ {i = i} gr →
             subst (λ Pr -> _ & _ / _ ↑ _ ⊢p< ng > Pr)
                   (branch-prsub-lookup-perm {Br = Br})
                   (proc-subst-lemma (k gr) (proc-exp-wkn-lemma y))
  proc-subst-lemma {Pr = Pr} (t/skip r p k) y
    = t/skip (is-comm/subst r) p λ α → proc-subst-lemma (k α) y
  proc-subst-lemma (t/if etd x x₁) y
    = t/if etd (proc-subst-lemma x y) (proc-subst-lemma x₁ y)
  proc-subst-lemma (t/rec x x₁) y
    = t/rec x (proc-subst-lemma x₁ (proc-wkn-lemma y))
  proc-subst-lemma {Δ = Δ}{X = X}{G' = G'}(t/var {X = X₁} x gr) y with X ≟f X₁
  proc-subst-lemma {Δ = Δ}{X = X}{G' = G'}(t/var {X = X₁} x gr) y | yes refl
    rewrite insertAt-lookup Δ X G'
      = unrelated/trace (t/bisim (~sym x) y) gr
  proc-subst-lemma {Δ = Δ}{X = X}{G = G}{G' = G'}(t/var {X = X₁} x gr) y | no ne
     with insertAt-punchIn Δ X G' (punchOut ne)
  ... | lu rewrite punchIn-punchOut ne | lu = t/var x gr
  proc-subst-lemma (t/end p∉g) y = t/end p∉g
