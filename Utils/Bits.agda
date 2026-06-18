{-# OPTIONS --guardedness #-}

-- Bool-vector fixpoints: iteration, and the weight `wt` as a termination
-- measure.

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as Nat
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (Bool; true; false; T)
import Data.Fin as F
open import Data.Vec using (Vec; lookup)
import Data.Vec as V
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; _≢_; sym; trans)
open import Relation.Nullary using (Dec; yes; no)

module Utils.Bits where

iter : ∀ {A : Set} → ℕ → (A → A) → A → A
iter zero    f x = x
iter (suc k) f x = iter k f (f x)

iter-shift :
  ∀ {A} k (f : A → A) x → iter k f (f x) ≡ f (iter k f x)
iter-shift zero    f x = refl
iter-shift (suc k) f x = iter-shift k f (f x)

iter-suc :
  ∀ {A} k (f : A → A) x → iter (suc k) f x ≡ f (iter k f x)
iter-suc k f x = iter-shift k f x

iter-add :
  ∀ {A} a b (f : A → A) x
  → iter (a + b) f x ≡ iter b f (iter a f x)
iter-add zero    b f x = refl
iter-add (suc a) b f x = iter-add a b f (f x)

-- `iter`, stopping at a stable round.  The equality test forces each round,
-- which a lazy `iter` chain does not.  `iterateFix/iterate` relates them.
iterateFix :
  ∀ {A : Set}
  → ((x y : A) → Dec (x ≡ y))
  → ℕ → (A → A) → A → A
iterateFix eq? zero f x = x
iterateFix eq? (suc fuel) f x with f x
... | fx with eq? fx x
...   | yes _ = x
...   | no  _ = iterateFix eq? fuel f fx

iter/stable :
  ∀ {A : Set} fuel (f : A → A) x
  → f x ≡ x
  → iter fuel f x ≡ x
iter/stable zero f x eq = refl
iter/stable (suc fuel) f x eq =
  trans (cong (iter fuel f) eq) (iter/stable fuel f x eq)

iterateFix/iterate :
  ∀ {A : Set}
    (eq? : (x y : A) → Dec (x ≡ y))
    fuel (f : A → A) x
  → iterateFix eq? fuel f x ≡ iter fuel f x
iterateFix/iterate eq? zero f x = refl
iterateFix/iterate eq? (suc fuel) f x with f x in fxeq
... | fx with eq? fx x
...   | yes eq =
  sym (trans (cong (iter fuel f) eq)
             (iter/stable fuel f x (trans fxeq eq)))
...   | no _ = iterateFix/iterate eq? fuel f fx

≡true→T : ∀ {b} → b ≡ true → T b
≡true→T refl = tt

T→≡true : ∀ {b} → T b → b ≡ true
T→≡true {true}  _  = refl
T→≡true {false} ()

bitv : Bool → ℕ
bitv false = zero
bitv true  = suc zero

wt : ∀ {n} → Vec Bool n → ℕ
wt V.[]        = zero
wt (b V.∷ row) = bitv b + wt row

Incl : ∀ {n} → Vec Bool n → Vec Bool n → Set
Incl left right =
  ∀ i → T (lookup left i) → T (lookup right i)

Incl-refl : ∀ {n} {v : Vec Bool n} → Incl v v
Incl-refl i x = x

Incl-trans :
  ∀ {n} {a b c : Vec Bool n}
  → Incl a b → Incl b c → Incl a c
Incl-trans ab bc i x = bc i (ab i x)

bitv/mono : ∀ l r → (T l → T r) → bitv l ≤ bitv r
bitv/mono false r    _    = z≤n
bitv/mono true  false incl = ⊥-elim (incl tt)
bitv/mono true  true  _    = s≤s z≤n

wt/mono :
  ∀ {n} {left right : Vec Bool n}
  → Incl left right
  → wt left ≤ wt right
wt/mono {left = V.[]} {V.[]} _ = z≤n
wt/mono {left = l V.∷ ls} {r V.∷ rs} incl =
  Nat.+-mono-≤
    (bitv/mono l r (incl F.zero))
    (wt/mono {left = ls} {right = rs} (λ i → incl (F.suc i)))

wt/strict :
  ∀ {n} {left right : Vec Bool n}
  → Incl left right
  → left ≢ right
  → wt left < wt right
wt/strict {left = V.[]} {V.[]} _ ne = ⊥-elim (ne refl)
wt/strict {left = false V.∷ ls} {false V.∷ rs} incl ne =
  wt/strict {left = ls} {right = rs}
    (λ i → incl (F.suc i))
    (λ e → ne (cong (false V.∷_) e))
wt/strict {left = false V.∷ ls} {true V.∷ rs} incl ne =
  s≤s (wt/mono {left = ls} {right = rs} (λ i → incl (F.suc i)))
wt/strict {left = true V.∷ ls} {false V.∷ rs} incl ne =
  ⊥-elim (incl F.zero tt)
wt/strict {left = true V.∷ ls} {true V.∷ rs} incl ne =
  s≤s (wt/strict {left = ls} {right = rs}
    (λ i → incl (F.suc i))
    (λ e → ne (cong (true V.∷_) e)))

wt-bound : ∀ {n} (v : Vec Bool n) → wt v ≤ n
wt-bound V.[]           = z≤n
wt-bound (false V.∷ v)  =
  Nat.≤-trans (wt-bound v) (Nat.n≤1+n _)
wt-bound (true V.∷ v)   = s≤s (wt-bound v)

wt-pos :
  ∀ {n} {v : Vec Bool n} {i} → lookup v i ≡ true → 1 ≤ wt v
wt-pos {v = b V.∷ v} {F.zero}  p rewrite p = s≤s z≤n
wt-pos {v = b V.∷ v} {F.suc i} p =
  Nat.≤-trans (wt-pos {v = v} {i = i} p) (Nat.m≤n+m (wt v) (bitv b))

-- The all-true vector has full weight.
wt/true : ∀ n → wt (V.replicate n true) ≡ n
wt/true zero    = refl
wt/true (suc n) = cong suc (wt/true n)
