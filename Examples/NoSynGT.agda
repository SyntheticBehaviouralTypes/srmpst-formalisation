{-# OPTIONS --guardedness #-}

-- `A` messages `B` then `C`, or `C` then `B`: no synchronous global type
-- describes it, but it is well-typed.  Of the partitions of the roles,
-- four are accepted; {A} {B,C} is rejected (`Focus`), in either order.

module Examples.NoSynGT where

open import Definitions.Expr.Syntax
import Data.Bool as Bool
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Sum using (_⊎_)
open import Data.Product using (proj₁; ∃-syntax; _×_)
open import Data.List using (length)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (does; from-yes)

open import Definitions.Expr using (s/unit; val; v/unit; v/nat; is-zero)
open import Check

open import Definitions.Graph.Algebra 3
open import Data.Fin.Subset using (⁅_⁆)
open import Definitions.Actions 3
open import Definitions.Proc 3 hiding (rec; _⇐_？·_)
open import Definitions.Proc.Syntax 3
open import Utils.Branch using (⟪_⟫; _↦_; _∣_)

A B C : Fin 3
A = 0F
B = 1F
C = 2F

notify : Fin 1
notify = 0F

-- From s0, `A` messages `B` first or `C` first; both end in `ended`.
nosyn : OpenGraph 0
nosyn =
  ⟪ A ⟶ ⁅ B ⁆ # notify < s/unit > ∙ A ⟶ ⁅ C ⁆ # notify < s/unit > ∙ end
  ∣ A ⟶ ⁅ C ⁆ # notify < s/unit > ∙ A ⟶ ⁅ B ⁆ # notify < s/unit > ∙ end
  ⟫

wbg : WBGraph {N = 3}
wbg = buildG nosyn {p = tt}

s₀ = initial (proj₁ wbg)

open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_; safety; module Global)

p/A : Proc 0 0
p/A =
  ifp is-zero (0)
    then A ⇒ ⁅ B ⁆ ! notify < unit >∙
         A ⇒ ⁅ C ⁆ ! notify < unit >∙ ∅
    else A ⇒ ⁅ C ⁆ ! notify < unit >∙
         A ⇒ ⁅ B ⁆ ! notify < unit >∙ ∅

p/B : Proc 0 0
p/B = B ⇐ A ？· ⟪ notify ↦ ∅ ⟫

p/C : Proc 0 0
p/C = C ⇐ A ？· ⟪ notify ↦ ∅ ⟫

own/AB∣C own/AC∣B own/A∣BC : Fin 3 → Fin 2
own/AB∣C 0F = 0F
own/AB∣C 1F = 0F
own/AB∣C 2F = 1F
own/AC∣B 0F = 0F
own/AC∣B 1F = 1F
own/AC∣B 2F = 0F
own/A∣BC 0F = 0F
own/A∣BC 1F = 1F
own/A∣BC 2F = 1F

-- {A} {B} {C}: one process per role.
module A∣B∣C where
  Ρ = singletons
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = p/A v∷ p/B v∷ p/C v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = from-yes (typecheckSession wbg Ρ M)

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- {A,B} {C}: `A→B` is internal; `A` sends to `C`, before or after it.
module AB∣C where
  Ρ = byOwner own/AB∣C
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = A ⇒ ⁅ C ⁆ ! notify < unit >∙ ∅ v∷ p/C v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = from-yes (typecheckSession wbg Ρ M)

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- {A,C} {B}: symmetrically.
module AC∣B where
  Ρ = byOwner own/AC∣B
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = A ⇒ ⁅ B ⁆ ! notify < unit >∙ ∅ v∷ p/B v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = from-yes (typecheckSession wbg Ρ M)

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- {A} {B,C}: rejected, in either order.
module A∣BC where
  Ρ = byOwner own/A∣BC
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M₁ M₂ : Session
  M₁ = p/A v∷ B ⇐ A ？· ⟪ notify ↦ C ⇐ A ？· ⟪ notify ↦ ∅ ⟫ ⟫ v∷ v[]
  M₂ = p/A v∷ C ⇐ A ？· ⟪ notify ↦ B ⇐ A ？· ⟪ notify ↦ ∅ ⟫ ⟫ v∷ v[]

  _ : does (typecheckSession wbg Ρ M₁) ≡ Bool.false
  _ = refl

  _ : does (typecheckSession wbg Ρ M₂) ≡ Bool.false
  _ = refl

-- {A,B,C}: everything is internal.
module ABC where
  Ρ : Assignment 1
  Ρ = byOwner λ _ → 0F
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = ∅ v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = from-yes (typecheckSession wbg Ρ M)

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed
