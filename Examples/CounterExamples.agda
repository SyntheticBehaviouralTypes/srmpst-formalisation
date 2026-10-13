{-# OPTIONS --guardedness #-}

-- Ill-typed processes for `C`, rejected by the checker, and one well-typed
-- control.  Then the whole session under every partition of the roles: all
-- five are accepted.

module Examples.CounterExamples where

open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_; proj₁; ∃-syntax; _×_)
open import Data.List using (length)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Unit using (tt)
open import Data.Bool using (true)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Nullary.Decidable using (from-yes; from-no)

open import Definitions.Expr using (s/bool; val; v/bool)
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

-- `A`'s choice to `B`, forwarded by `B` to `C`
accept reject : Fin 2
accept = 0F
reject = 1F

-- a message from `A` straight to `C`, which the protocol never sends
direct : Fin 1
direct = 0F

-- s0 --A→B[0]--> s1 --B→C[0]--> ended
-- s0 --A→B[1]--> s2 --B→C[1]--> ended    (`ended` is the DSL's unique end)
round : OpenGraph 0
round =
  ⟪ A ⟶ ⁅ B ⁆ # accept < s/bool > ∙ B ⟶ ⁅ C ⁆ # accept < s/bool > ∙ end
  ∣ A ⟶ ⁅ B ⁆ # reject < s/bool > ∙ B ⟶ ⁅ C ⁆ # reject < s/bool > ∙ end
  ⟫

wbg : WBGraph {N = 3}
wbg = buildG round {p = tt}

s₀ = initial (proj₁ wbg)

open import Safety (wb-of wbg) (sync-of wbg) using (⊢ᵛ[_]_∶_; ⊢s[_]_∶_; safety; module Global)

-- the well-typed reference: `C` receives `B`'s (2-ary) forward, then ends
p/C-good : Proc 0 0
p/C-good = C ⇐ B ？· ⟪ accept ↦ ∅ ∣ reject ↦ ∅ ⟫

wtd/good : Dec (⊢ᵛ[ ⁅ C ⁆ ] p/C-good ∶ s₀)
wtd/good = typecheck wbg ⁅ C ⁆ p/C-good

C-good-well-typed : ⊢ᵛ[ ⁅ C ⁆ ] p/C-good ∶ s₀
C-good-well-typed = from-yes wtd/good

-- `C` waits for two sequential messages from `B` — but `B` only ever
-- forwards *one* message to `C`, so this is ill-typed.
p/C2 : Proc 0 0
p/C2 = C ⇐ B ？·
         ⟪ accept ↦ C ⇐ B ？· ⟪ accept ↦ ∅ ∣ reject ↦ ∅ ⟫
         ∣ reject ↦ C ⇐ B ？· ⟪ accept ↦ ∅ ∣ reject ↦ ∅ ⟫
         ⟫

wtd/C2 : Dec (⊢ᵛ[ ⁅ C ⁆ ] p/C2 ∶ s₀)
wtd/C2 = typecheck wbg ⁅ C ⁆ p/C2

C2-illtyped : ¬ ⊢ᵛ[ ⁅ C ⁆ ] p/C2 ∶ s₀
C2-illtyped = from-no wtd/C2

-- `C` waits to receive from `A` first — but `A` never messages `C`
-- directly, so this is ill-typed.
p/C3 : Proc 0 0
p/C3 = C ⇐ A ？· ⟪ direct ↦ C ⇐ B ？· ⟪ accept ↦ ∅ ∣ reject ↦ ∅ ⟫ ⟫

wtd/C3 : Dec (⊢ᵛ[ ⁅ C ⁆ ] p/C3 ∶ s₀)
wtd/C3 = typecheck wbg ⁅ C ⁆ p/C3

C3-illtyped : ¬ ⊢ᵛ[ ⁅ C ⁆ ] p/C3 ∶ s₀
C3-illtyped = from-no wtd/C3

-- Not `MessageGuarded`.
p/C4 : Proc 0 0
p/C4 = rec λ X → X

wtd/C4 : Dec (⊢ᵛ[ ⁅ C ⁆ ] p/C4 ∶ s₀)
wtd/C4 = typecheck wbg ⁅ C ⁆ p/C4

C4-illtyped : ¬ ⊢ᵛ[ ⁅ C ⁆ ] p/C4 ∶ s₀
C4-illtyped = from-no wtd/C4

-- ══════════════════════════════════════════════════════════════════════
--  Whole sessions, under every partition of the roles
-- ══════════════════════════════════════════════════════════════════════

-- `A` picks `accept`; `B` forwards whichever it gets.
p/A p/B : Proc 0 0
p/A = A ⇒ ⁅ B ⁆ ! accept < val (v/bool true) >∙ ∅
p/B = B ⇐ A ？· ⟪ accept ↦ B ⇒ ⁅ C ⁆ ! accept < val (v/bool true) >∙ ∅
                ∣ reject ↦ B ⇒ ⁅ C ⁆ ! reject < val (v/bool true) >∙ ∅
                ⟫

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

-- {A} {B} {C}
module A∣B∣C where
  Ρ = singletons
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = p/A v∷ p/B v∷ p/C-good v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = from-yes (typecheckSession wbg Ρ M)

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- {A,B} {C}: the choice is internal; the forward makes it.
module AB∣C where
  Ρ = byOwner own/AB∣C
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = (B ⇒ ⁅ C ⁆ ! reject < val (v/bool true) >∙ ∅) v∷ p/C-good v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = from-yes (typecheckSession wbg Ρ M)

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- {A,C} {B}: the block chooses, then hears the forward.
module AC∣B where
  Ρ = byOwner own/AC∣B
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = (A ⇒ ⁅ B ⁆ ! accept < val (v/bool true) >∙
         (C ⇐ B ？· ⟪ accept ↦ ∅ ∣ reject ↦ ∅ ⟫))
    v∷ p/B
    v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = from-yes (typecheckSession wbg Ρ M)

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- {A} {B,C}: the forward is internal.
module A∣BC where
  Ρ = byOwner own/A∣BC
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = p/A v∷ (B ⇐ A ？· ⟪ accept ↦ ∅ ∣ reject ↦ ∅ ⟫) v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = from-yes (typecheckSession wbg Ρ M)

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

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
