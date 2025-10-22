module Definitions.Expr where

open import Data.Empty using (⊥-elim)
open import Data.Product
open import Data.Sum
open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ ; zero ; suc ; less ; equal ; greater)
open import Data.Fin using (Fin ; zero ; suc ; punchOut ; punchIn) renaming (_≟_ to _≟f_)
open import Data.Vec using (Vec ; [] ; _[_]=_ ; lookup; _∷_) renaming (removeAt to _-_)
open import Data.Vec.Properties using (removeAt-punchOut)
open import Relation.Nullary using (Dec; yes; no ; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; _≢_ ; ≢-sym)

-- Expressions

data Sort : Set where
  s/bool s/nat s/unit : Sort

data Value : Set where
  v/bool : Bool -> Value
  v/nat : ℕ -> Value
  v/unit : Value

data Exp (γ : ℕ) : Set where
  val : Value -> Exp γ
  minus1 : Exp γ -> Exp γ
  is-zero : Exp γ -> Exp γ
  var : Fin γ -> Exp γ

weaken/exp : ∀{γ} -> Exp γ -> Fin (suc γ) -> Exp (suc γ)
weaken/exp (val V) x = val V
weaken/exp (minus1 E) x = minus1 (weaken/exp E x)
weaken/exp (is-zero E) x = is-zero (weaken/exp E x)
weaken/exp (var y) x = var (punchIn x y)

-- of expressions
data _⇓_ : Exp 0 -> Value -> Set where
  e/minus1/z : ∀{E} -> E ⇓ (v/nat 0) -> minus1 E ⇓ (v/nat 0)
  e/minus1/s : ∀{E N} -> E ⇓ (v/nat (suc N)) -> minus1 E ⇓ v/nat N

  e/is-zero/s : ∀{E N} -> E ⇓ v/nat (suc N) -> is-zero E ⇓ v/bool false
  e/is-zero/z : ∀{E} -> E ⇓ v/nat 0 -> is-zero E ⇓ v/bool true

  e/val : ∀{V} -> val V ⇓ V

[_/_]exp : ∀{γ} -> Exp γ -> Fin (suc γ) -> Exp (suc γ) -> Exp γ
[ E / y ]exp (val V) = val V
[ E / y ]exp (minus1 E') = minus1 ([ E / y ]exp E')
[ E / y ]exp (is-zero E') = is-zero ([ E / y ]exp E')
[ E / y ]exp (var x) with  y ≟f x
[ E / y ]exp (var x) | yes refl = E
[ E / y ]exp (var x) | no eq = var (punchOut eq)

[E/x]exp-x : ∀{γ x}(E : Exp γ) -> [ E / x ]exp (var x) ≡ E
[E/x]exp-x {_}{x} E with x ≟f x
[E/x]exp-x {_}{x} E | yes refl = refl
[E/x]exp-x {_}{x} E | no eq = ⊥-elim (eq refl)

[E/y]exp-x : ∀{γ x y}{E : Exp γ} -> (y≢x : y ≢ x) -> [ E / y ]exp (var x) ≡ var (punchOut y≢x)
[E/y]exp-x {_}{x}{y} prf with y ≟f x
[E/y]exp-x prf | yes refl = ⊥-elim (prf refl)
[E/y]exp-x prf | no eq = refl

data ⊢v_∶_ : Value -> Sort -> Set where
  tv/bool : {b : Bool} -> ⊢v (v/bool b) ∶ s/bool
  tv/nat : {n : ℕ} -> ⊢v (v/nat n) ∶ s/nat
  tv/unit : ⊢v (v/unit) ∶ s/unit

data _⊢e_∶_ {γ : ℕ} (Γ : Vec Sort γ) : Exp γ -> Sort -> Set where
  te/val : ∀{V S} -> ⊢v V ∶ S -> Γ ⊢e val V ∶ S
  te/minus1 : ∀{E} ->  Γ ⊢e E ∶ s/nat -> Γ ⊢e minus1 E ∶ s/nat
  te/is-zero : ∀{E} ->  Γ ⊢e E ∶ s/nat -> Γ ⊢e is-zero E ∶ s/bool
  te/var : ∀{x} ->  Γ ⊢e var x ∶ (lookup Γ x) -- TODO make {x} explicit

exp-subst : ∀{γ}{Γ : Vec Sort (suc γ)}{E E' S x} -> Γ ⊢e E ∶ S -> (Γ - x) ⊢e E' ∶ lookup Γ x -> (Γ - x) ⊢e [ E' / x ]exp E ∶ S
exp-subst (te/val x) td' = te/val x
exp-subst (te/minus1 td) td' = te/minus1 (exp-subst td td')
exp-subst (te/is-zero td) td' = te/is-zero (exp-subst td td')
exp-subst {x = x} (te/var {y}) td' with x ≟f y
exp-subst {x = x} (te/var {y}) td' | yes refl = td'
exp-subst {Γ = Γ}{x = x} (te/var {y}) td' | no neq rewrite sym(removeAt-punchOut Γ neq) = te/var

exp-str : ∀{γ}{Γ : Vec Sort γ}{S S' E}
  → Γ ⊢e E ∶ S → (S' ∷ Γ) ⊢e weaken/exp E zero ∶ S
exp-str (te/val x) = te/val x
exp-str (te/minus1 x) = te/minus1 (exp-str x)
exp-str (te/is-zero x) = te/is-zero (exp-str x)
exp-str te/var = te/var

exp-pres : ∀{E S V} -> [] ⊢e E ∶ S -> E ⇓ V -> ⊢v V ∶ S
exp-pres (te/val td) e/val = td
exp-pres (te/minus1 td) (e/minus1/z rd) = tv/nat
exp-pres (te/minus1 td) (e/minus1/s rd) = tv/nat
exp-pres (te/is-zero td) (e/is-zero/s rd) = tv/bool
exp-pres (te/is-zero td) (e/is-zero/z rd) = tv/bool

eval-exp : ∀ {E S} → [] ⊢e E ∶ S → ∃[ V ] E ⇓ V
eval-exp (te/val x) = _ , e/val
eval-exp (te/minus1 td) with eval-exp td
eval-exp (te/minus1 td) | v , ev with exp-pres td ev
eval-exp (te/minus1 td) | v/nat zero , ev | tv/nat = _ , e/minus1/z ev
eval-exp (te/minus1 td) | v/nat (suc n) , ev | tv/nat = _ , e/minus1/s ev
eval-exp (te/is-zero td) with eval-exp td
eval-exp (te/is-zero td) | v , ev with exp-pres td ev
eval-exp (te/is-zero td) | v/nat zero , ev | tv = _ , e/is-zero/z ev
eval-exp (te/is-zero td) | v/nat (suc v) , ev | tv = _ , e/is-zero/s ev

eval-bool : ∀ {E} → [] ⊢e E ∶ s/bool → (E ⇓ v/bool true) ⊎  (E ⇓ v/bool false)
eval-bool td with eval-exp td
eval-bool td | v , ev with exp-pres td ev
eval-bool td | v/bool false , ev | tv/bool = inj₂ ev
eval-bool td | v/bool true , ev | tv/bool = inj₁ ev
