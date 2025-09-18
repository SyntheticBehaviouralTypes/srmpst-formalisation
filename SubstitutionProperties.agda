{-# OPTIONS --guardedness #-}
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Fin using (Fin ; zero ; suc ; compare ; punchIn ; punchOut) renaming (_≟_ to _≟f_)
open import Data.Vec using (Vec ; _∷_ ; _++_ ; [] ; _[_]=_ ; insertAt ) renaming (lookup to lu; removeAt to _-_)
open import Data.Vec.Relation.Unary.Any using (Any)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Function using (_∘_)
open import Relation.Nullary using (False; ¬_; yes; no)
open import Relation.Nullary.Decidable using (toWitness ; fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; subst ; _≢_ ; cong)
open import Utils.Fin using (refl-is-equal ; reflect-lookup)
open import Utils.Vec using (lookup-not-insertAt)
open import Data.Fin.Properties
  using (punchIn-punchOut)
open import Data.Vec.Properties
  using ( insertAt-punchIn ; insertAt-lookup ; removeAt-insertAt
        ; removeAt-punchOut ; cast-is-id ; cast-sym ; ++-identityʳ-eqFree)

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

  expr-subst-lemma : ∀{γ δ ξ g G P E Pr}
    → ∀ {Γ : Vec Sort (suc γ)}{Δ : Vec Behav δ}{Ξ : Vec Behav ξ}{X : Fin (suc γ)}
    → (Γ - X) ⊢e E ∶ lu Γ X
    → Γ       & Δ & Ξ / G ↑ P ⊢p< g > Pr
    → (Γ - X) & Δ & Ξ / G ↑ P ⊢p< g > ([ E / X ]e Pr)
  expr-subst-lemma etd (t/send gr etd₁ ptd)
    = t/send gr (exp-subst etd₁ etd) (expr-subst-lemma etd ptd)
  expr-subst-lemma {E = E}{Γ = S ∷ Γ}{X = X} etd (t/recv {Br = Br} x conts)
    = t/recv x (λ {i = i} y →
        let etd' = exp-str etd
            ky = expr-subst-lemma {E = weaken/exp E zero}{X = suc X}
                                  etd' (conts y)
        in subst (_ & _ & _ / _ ↑ _ ⊢p< ng >_) (subst/lu Br i) ky)
  expr-subst-lemma etd (t/if etd₁ ptd ptd₁)
    = t/if (exp-subst etd₁ etd)
           (expr-subst-lemma etd ptd)
           (expr-subst-lemma etd ptd₁)
  expr-subst-lemma etd (t/rec gr ptd) = t/rec gr (expr-subst-lemma etd ptd)
  expr-subst-lemma etd (t/var x gr) = t/var x gr
  expr-subst-lemma etd (t/end p∉g) = t/end p∉g
  expr-subst-lemma {E = E} {Γ = S ∷ Γ} {X = X} etd (t/skip-next [ x & y & z & t ] k)
    = t/skip-next [ is-comm/subst/exp x & y & z & t ] (expr-subst-lemma etd ∘ k)
  expr-subst-lemma {E = E} {Γ = S ∷ Γ} {X = X} etd (t/skip-close [ x & y & z & t ] k)
    = t/skip-close [ is-comm/subst/exp x & y & z & t ] k

  -- small lemma to show that weakening branches commutes with lookup
  branch-wkn-lookup-perm : ∀{γ δ I}{Br : Vec (Proc (suc γ) δ) I}{i x} ->
    weaken/proc/exp (lu Br i) x ≡ lu (weaken/exp/branch Br x) i
  branch-wkn-lookup-perm {Br = Pr ∷ Br} {i = zero} = refl
  branch-wkn-lookup-perm {Br = Pr ∷ Br} {i = suc i} = branch-wkn-lookup-perm {Br = Br}{i = i}

  proc-exp-wkn-lemma : ∀{S γ δ ξ g G P Pr}
    → {Γ : Vec Sort γ}{Δ : Vec Behav δ}{Ξ : Vec Behav ξ}{x : Fin (suc γ)}
    → Γ & Δ & Ξ / G ↑ P ⊢p< g > Pr
    → insertAt Γ x S & Δ & Ξ / G ↑ P ⊢p< g > weaken/proc/exp Pr x
  proc-exp-wkn-lemma (t/send gr etd td)
    = t/send gr (exp-wkn-lemma etd) (proc-exp-wkn-lemma td)
  proc-exp-wkn-lemma (t/recv {Br = Br} r k)
    = t/recv r λ gr → subst (_ & _ & _ / _ ↑ _ ⊢p< _ >_)
                            (branch-wkn-lookup-perm {Br = Br})
                            (proc-exp-wkn-lemma (k gr))
  proc-exp-wkn-lemma (t/if etd td td₁)
    = t/if (exp-wkn-lemma etd) (proc-exp-wkn-lemma td) (proc-exp-wkn-lemma td₁)
  proc-exp-wkn-lemma (t/rec x td) = t/rec x (proc-exp-wkn-lemma td)
  proc-exp-wkn-lemma (t/var x gr) = t/var x gr
  proc-exp-wkn-lemma (t/end p∉g) = t/end p∉g
  proc-exp-wkn-lemma (t/skip-next [ x & y & z & t ] ktd)
    = t/skip-next [ is-comm/wk/pr/exp x & y & z & t ] (proc-exp-wkn-lemma ∘ ktd)
  proc-exp-wkn-lemma (t/skip-close [ x & y & z & t ] ktd)
    = t/skip-close [ is-comm/wk/pr/exp x & y & z & t ] ktd

  branch-subst-lookup-perm :  ∀{γ δ I}{Br : Vec (Proc (suc γ) δ) I}{N x i} ->
       [ N / suc x ]e (lu Br i)  ≡ lu ([ N / x ]ech Br) i
  branch-subst-lookup-perm {Br = Pr ∷ Br} {i = zero} = refl
  branch-subst-lookup-perm {Br = _ ∷ Br} {i = suc i} = branch-subst-lookup-perm {Br = Br} {i = i}

  branch-wknpr-lookup-perm : ∀{γ δ I}(Br : Vec (Proc (suc γ) δ) I) i X ->
    weaken/proc (lu Br i) X ≡ lu (weaken/proc/branch Br X) i
  branch-wknpr-lookup-perm (Pr ∷ Br) zero X = refl
  branch-wknpr-lookup-perm (_ ∷ Br) (suc i) X = branch-wknpr-lookup-perm Br i X

  -- weakening lemma for procs with proc vars
  proc-wkn-lemma : ∀{γ δ ξ g}{Γ : Vec Sort γ}{Δ : Vec Behav δ}{Ξ : Vec Behav ξ}
    → ∀ {G G' P Pr X}
    → Γ & Δ & Ξ / G ↑ P ⊢p< g > Pr
    → Γ & insertAt Δ X G' & Ξ / G ↑ P ⊢p< g > weaken/proc Pr X
  proc-wkn-lemma (t/send gr etd td) = t/send gr etd (proc-wkn-lemma td)
  proc-wkn-lemma {X = X}(t/recv {Br = Br} x k)
    = t/recv x λ {i = i} gr →
             subst (_ & _ & _ / _ ↑ _ ⊢p< _ >_)
                   (branch-wknpr-lookup-perm Br i X) (proc-wkn-lemma (k gr))
  proc-wkn-lemma (t/if etd td td₁)
    = t/if etd (proc-wkn-lemma td) (proc-wkn-lemma td₁)
  proc-wkn-lemma (t/rec x td) = t/rec x (proc-wkn-lemma td)
  proc-wkn-lemma {Δ = Δ}{G' = G'}{X = X}(t/var {X = Y} x gr)
    rewrite sym (insertAt-punchIn Δ X G' Y) = t/var x gr
  proc-wkn-lemma (t/end p∉g) = t/end p∉g
  proc-wkn-lemma (t/skip-next [ ic & nv & na & t ] ktd)
    = t/skip-next [ is-comm/wk/pr ic & nv & na & t ] (proc-wkn-lemma ∘ ktd)
  proc-wkn-lemma (t/skip-close [ ic & nv & na & t ] ktd)
    = t/skip-close [ is-comm/wk/pr ic & nv & na & t ] ktd

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

  -- TODO "tidy up" & refactor
  any-cast : ∀ {ξ} {ξ'} {G}
             {Ξ : Vec Behav ξ} (eq : ξ ≡ ξ')
           → Any (_~_ G) (Data.Vec.cast eq Ξ)
           → Any (_~_ G) Ξ
  any-cast refl px = subst (λ x → Any _ x) (cast-is-id refl _) px

  cast-visited : ∀{γ δ ξ ξ' g G P Pr}
    → {Γ : Vec Sort γ}{Δ : Vec Behav δ}{Ξ : Vec Behav ξ}
    → (eq : ξ ≡ ξ')
    → Γ & Δ & Data.Vec.cast eq Ξ / G ↑ P ⊢p< g > Pr
    → Γ & Δ & Ξ / G ↑ P ⊢p< g > Pr
  cast-visited eq (t/send gr etd x) = t/send gr etd x
  cast-visited eq (t/recv gr conts) = t/recv gr conts
  cast-visited eq (t/if etd x x₁) = t/if etd x x₁
  cast-visited eq (t/rec x x₁) = t/rec x x₁
  cast-visited eq (t/var x x₁) = t/var x x₁
  cast-visited eq (t/end x) = t/end x
  cast-visited eq (t/skip-next x ktd)
    = t/skip-next x (cast-visited (cong suc eq) ∘ ktd)
  cast-visited eq (t/skip-close x x₁) = t/skip-close x (any-cast eq x₁)

  open HeadAct
  proc-subst-lemma : ∀{γ δ ξ g G G' P Pr Pr'}
    → {Γ : Vec Sort γ}{Δ : Vec Behav δ}{Ξ : Vec Behav ξ}{X : Fin (suc δ)}
    → Γ & insertAt Δ X G' & Ξ / G ↑ P ⊢p< g > Pr
    → Γ & Δ & Data.Vec.[] / G' ↑ P ⊢p< ng > Pr'
    → Γ & Δ & Ξ / G ↑ P ⊢p< g > ([ Pr' / X ]pr Pr)
  proc-subst-lemma (t/send gr etd x) y = t/send gr etd (proc-subst-lemma x y)
  proc-subst-lemma {G' = G'}{Pr' = Pr'}{Γ = Γ}{Δ = Δ}{X = X}
                   (t/recv {Br = Br} x k) y
    = t/recv x λ {i = i} gr →
             subst (_ & _ & _ / _ ↑ _ ⊢p< ng >_)
                   (branch-prsub-lookup-perm {Br = Br})
                   (proc-subst-lemma (k gr) (proc-exp-wkn-lemma y))
  proc-subst-lemma (t/if etd x x₁) y
    = t/if etd (proc-subst-lemma x y) (proc-subst-lemma x₁ y)
  proc-subst-lemma (t/rec x x₁) y
    = t/rec x (proc-subst-lemma x₁ (proc-wkn-lemma y))
  proc-subst-lemma {X = X}(t/var {X = X₁} x gr) y with X ≟f X₁
  proc-subst-lemma {ξ = ξ}{G' = G'}{Δ = Δ}{Ξ = Ξ}{X = X}(t/var {X = X₁} x gr) y
    | yes refl
    rewrite insertAt-lookup Δ X G'
      = let res = strengthen/visited Ξ (unrelated/trace (t/bisim (~sym x) y) gr)
            idr = sym (cast-sym (+-identityʳ ξ) (++-identityʳ-eqFree Ξ))
            res' = subst (_ & _ &_/ _ ↑ _ ⊢p< ng > _) idr res
        in cast-visited (sym (+-identityʳ _)) res'
  proc-subst-lemma {G = G}{G' = G'}{Δ = Δ}{X = X}(t/var {X = X₁} x gr) y
    | no ne
     with insertAt-punchIn Δ X G' (punchOut ne)
  ... | lu rewrite punchIn-punchOut ne | lu = t/var x gr
  proc-subst-lemma (t/end p∉g) y = t/end p∉g
  proc-subst-lemma {Pr = Pr} (t/skip-next [ x & y & z & t ] ktd) r
    = t/skip-next [ is-comm/subst x & y & z & t ] (λ g → proc-subst-lemma (ktd g) r)
  proc-subst-lemma {Pr = Pr} (t/skip-close [ x & y & z & t ] ktd) a
    = t/skip-close [ is-comm/subst x & y & z & t ] ktd
