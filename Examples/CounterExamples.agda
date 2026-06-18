{-# OPTIONS --guardedness #-}

-- Ill-typed processes for `C`, rejected by the checker, and one well-typed
-- control.  Then the whole session under every partition of the roles: all
-- five are accepted.

module Examples.CounterExamples where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Sum using (_⊎_)
open import Data.Product using (_,_; proj₁; ∃-syntax; _×_)
open import Data.List using (length)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Unit using (tt)
open import Data.Bool using (true)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)

open import Definitions.Expr using (s/bool; val; v/bool)
open import Check

open import Definitions.Graph.Algebra 3
open import Data.Fin.Subset using (⁅_⁆)
open import Definitions.Actions 3 renaming (_<_> to mkChoice)
open import Definitions.Proc 3

A B C : Fin 3
A = zero
B = suc zero
C = suc (suc zero)

-- the two labels of the A→B choice (and of the B→C forwarding)
lbl0 lbl1 : Fin 2
lbl0 = zero
lbl1 = suc zero

-- s0 --A→B[0]--> s1 --B→C[0]--> ended
-- s0 --A→B[1]--> s2 --B→C[1]--> ended    (`ended` is the DSL's unique end)
round : OpenGraph 0
round = openGraph 3 (node zero)
  ( ( ((A ⟶ ⁅ B ⁆ # mkChoice lbl0 s/bool) , node (suc zero))
    ∷ ((A ⟶ ⁅ B ⁆ # mkChoice lbl1 s/bool) , node (suc (suc zero)))
    ∷ [] )                                                            -- s0
  v∷ ( ((B ⟶ ⁅ C ⁆ # mkChoice lbl0 s/bool) , ended) ∷ [] )             -- s1
  v∷ ( ((B ⟶ ⁅ C ⁆ # mkChoice lbl1 s/bool) , ended) ∷ [] )             -- s2
  v∷ v[]
  )

wbg : WBGraph {N = 3}
wbg = buildG round {p = tt}

s₀ = initial (proj₁ wbg)

open import Safety (wb-of wbg) (sync-of wbg) using (⊢ᵛ[_]_∶_; ⊢s[_]_∶_; safety; module Global)

-- the well-typed reference: `C` receives `B`'s (2-ary) forward, then ends
p/C-good : Proc 0 0
p/C-good = C ⇐ B ？· (∅ v∷ ∅ v∷ v[])

wtd/good : Dec (⊢ᵛ[ ⁅ C ⁆ ] p/C-good ∶ s₀)
wtd/good = typecheck wbg ⁅ C ⁆ p/C-good

C-good-well-typed : ⊢ᵛ[ ⁅ C ⁆ ] p/C-good ∶ s₀
C-good-well-typed = toWitness {a? = wtd/good} _

-- `C` waits for two sequential messages from `B` — but `B` only ever
-- forwards *one* message to `C`, so this is ill-typed.
p/C2 : Proc 0 0
p/C2 = C ⇐ B ？·
         (  C ⇐ B ？· (∅ v∷ ∅ v∷ v[])
         v∷ C ⇐ B ？· (∅ v∷ ∅ v∷ v[])
         v∷ v[])

wtd/C2 : Dec (⊢ᵛ[ ⁅ C ⁆ ] p/C2 ∶ s₀)
wtd/C2 = typecheck wbg ⁅ C ⁆ p/C2

C2-illtyped : ¬ ⊢ᵛ[ ⁅ C ⁆ ] p/C2 ∶ s₀
C2-illtyped = toWitnessFalse {a? = wtd/C2} _

-- `C` waits to receive from `A` first — but `A` never messages `C`
-- directly, so this is ill-typed.
p/C3 : Proc 0 0
p/C3 = C ⇐ A ？·
         (C ⇐ B ？· (∅ v∷ ∅ v∷ v[]) v∷ v[])

wtd/C3 : Dec (⊢ᵛ[ ⁅ C ⁆ ] p/C3 ∶ s₀)
wtd/C3 = typecheck wbg ⁅ C ⁆ p/C3

C3-illtyped : ¬ ⊢ᵛ[ ⁅ C ⁆ ] p/C3 ∶ s₀
C3-illtyped = toWitnessFalse {a? = wtd/C3} _

-- Not `MessageGuarded`.
p/C4 : Proc 0 0
p/C4 = rec (v zero)

wtd/C4 : Dec (⊢ᵛ[ ⁅ C ⁆ ] p/C4 ∶ s₀)
wtd/C4 = typecheck wbg ⁅ C ⁆ p/C4

C4-illtyped : ¬ ⊢ᵛ[ ⁅ C ⁆ ] p/C4 ∶ s₀
C4-illtyped = toWitnessFalse {a? = wtd/C4} _

-- ══════════════════════════════════════════════════════════════════════
--  Whole sessions, under every partition of the roles
-- ══════════════════════════════════════════════════════════════════════

-- `A` picks label 0; `B` forwards whichever it gets.
p/A p/B : Proc 0 0
p/A = A ⇒ ⁅ B ⁆ ! lbl0 < val (v/bool true) >∙ ∅
p/B = B ⇐ A ？· (  (B ⇒ ⁅ C ⁆ ! lbl0 < val (v/bool true) >∙ ∅)
                v∷ (B ⇒ ⁅ C ⁆ ! lbl1 < val (v/bool true) >∙ ∅)
                v∷ v[])

own/AB∣C own/AC∣B own/A∣BC : Fin 3 → Fin 2
own/AB∣C zero             = zero
own/AB∣C (suc zero)       = zero
own/AB∣C (suc (suc zero)) = suc zero
own/AC∣B zero             = zero
own/AC∣B (suc zero)       = suc zero
own/AC∣B (suc (suc zero)) = zero
own/A∣BC zero             = zero
own/A∣BC (suc zero)       = suc zero
own/A∣BC (suc (suc zero)) = suc zero

-- {A} {B} {C}
module A∣B∣C where
  Ρ = singletons
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = p/A v∷ p/B v∷ p/C-good v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

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
  M = (B ⇒ ⁅ C ⁆ ! lbl1 < val (v/bool true) >∙ ∅) v∷ p/C-good v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

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
  M = (A ⇒ ⁅ B ⁆ ! lbl0 < val (v/bool true) >∙ (C ⇐ B ？· (∅ v∷ ∅ v∷ v[]))) v∷ p/B v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

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
  M = p/A v∷ (B ⇐ A ？· (∅ v∷ ∅ v∷ v[])) v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed

-- {A,B,C}: everything is internal.
module ABC where
  Ρ : Assignment 1
  Ρ = byOwner λ _ → zero
  open Over Ρ
  open Global Ρ using (_-[_]->ᵍ_)

  M : Session
  M = ∅ v∷ v[]

  M-typed : ⊢s[ Ρ ] M ∶ s₀
  M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

  M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
         → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                   × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
  M-safe = safety Ρ M-typed
