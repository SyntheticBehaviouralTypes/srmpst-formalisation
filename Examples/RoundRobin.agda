{-# OPTIONS --guardedness #-}

-- A token ring A → B → C → A, once and in a loop.  All five partitions
-- are accepted.

module Examples.RoundRobin where

open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Vec using ([]; _∷_)
open import Data.Bool using (true)
open import Data.Product using (proj₁; ∃-syntax; _×_)
open import Data.List using (length)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Sum using (_⊎_)
open import Relation.Nullary.Decidable using (from-yes)

open import Definitions.Expr using (s/bool; val; v/bool)
open import Check

open import Definitions.Graph.Algebra 3
open import Data.Fin.Subset using (⁅_⁆)
open import Definitions.Actions 3 renaming (_<_> to mkChoice)
open import Definitions.Proc 3

A B C : Fin 3
A = 0F
B = 1F
C = 2F

here : Fin 1
here = 0F

-- The partitions with two blocks, as owner maps.
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

module NonRecursive where
  -- A --bool--> B --bool--> C --bool--> A, end
  round : OpenGraph 0
  round =
    (A ⟶ ⁅ B ⁆ # mkChoice here s/bool) ∙
    ((B ⟶ ⁅ C ⁆ # mkChoice here s/bool) ∙
     ((C ⟶ ⁅ A ⁆ # mkChoice here s/bool) ∙ end))

  wbg : WBGraph {N = 3}
  wbg = buildG round

  s₀ = initial (proj₁ wbg)

  open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_; safety; module Global)

  p/A p/B p/C : Proc 0 0
  p/A = A ⇒ ⁅ B ⁆ ! here < val (v/bool true) >∙ (A ⇐ C ？· (∅ ∷ []))
  p/B = B ⇐ A ？· ((B ⇒ ⁅ C ⁆ ! here < val (v/bool true) >∙ ∅) ∷ [])
  p/C = C ⇐ B ？· ((C ⇒ ⁅ A ⁆ ! here < val (v/bool true) >∙ ∅) ∷ [])

  -- {A} {B} {C}: one process per role.
  module A∣B∣C where
    Ρ = singletons
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = p/A ∷ p/B ∷ p/C ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = from-yes (typecheckSession wbg Ρ M)

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed

  -- {A,B} {C}: `A→B` is internal.
  module AB∣C where
    Ρ = byOwner own/AB∣C
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = (B ⇒ ⁅ C ⁆ ! here < val (v/bool true) >∙ (A ⇐ C ？· (∅ ∷ []))) ∷ p/C ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = from-yes (typecheckSession wbg Ρ M)

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed

  -- {A,C} {B}: `C→A` is internal.
  module AC∣B where
    Ρ = byOwner own/AC∣B
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = (A ⇒ ⁅ B ⁆ ! here < val (v/bool true) >∙ (C ⇐ B ？· (∅ ∷ []))) ∷ p/B ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = from-yes (typecheckSession wbg Ρ M)

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed

  -- {A} {B,C}: `B→C` is internal.
  module A∣BC where
    Ρ = byOwner own/A∣BC
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = p/A ∷ (B ⇐ A ？· ((C ⇒ ⁅ A ⁆ ! here < val (v/bool true) >∙ ∅) ∷ [])) ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = from-yes (typecheckSession wbg Ρ M)

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed

  -- {A,B,C}: everything is internal; the one process has nothing to do.
  module ABC where
    Ρ : Assignment 1
    Ρ = byOwner λ _ → 0F
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = ∅ ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = from-yes (typecheckSession wbg Ρ M)

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed

module Recursive where
  -- μ (A --bool--> B --bool--> C --bool--> loop)
  round : OpenGraph 0
  round =
    μ ((A ⟶ ⁅ B ⁆ # mkChoice here s/bool) ∙
       ((B ⟶ ⁅ C ⁆ # mkChoice here s/bool) ∙
        ((C ⟶ ⁅ A ⁆ # mkChoice here s/bool) ∙ var 0F)))

  wbg : WBGraph {N = 3}
  wbg = buildG round

  s₀ = initial (proj₁ wbg)

  open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_; safety; module Global)

  p/A p/B p/C : Proc 0 0
  p/A = rec (A ⇒ ⁅ B ⁆ ! here < val (v/bool true) >∙
              (A ⇐ C ？· (v 0F ∷ [])))
  p/B = rec (B ⇐ A ？·
              ((B ⇒ ⁅ C ⁆ ! here < val (v/bool true) >∙ v 0F) ∷ []))
  p/C = rec (C ⇐ B ？·
              ((C ⇒ ⁅ A ⁆ ! here < val (v/bool true) >∙ v 0F) ∷ []))

  -- {A} {B} {C}
  module A∣B∣C where
    Ρ = singletons
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = p/A ∷ p/B ∷ p/C ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = from-yes (typecheckSession wbg Ρ M)

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed

  -- {A,B} {C}
  module AB∣C where
    Ρ = byOwner own/AB∣C
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = rec (B ⇒ ⁅ C ⁆ ! here < val (v/bool true) >∙ (A ⇐ C ？· (v 0F ∷ []))) ∷ p/C ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = from-yes (typecheckSession wbg Ρ M)

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed

  -- {A,C} {B}
  module AC∣B where
    Ρ = byOwner own/AC∣B
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = rec (A ⇒ ⁅ B ⁆ ! here < val (v/bool true) >∙ (C ⇐ B ？· (v 0F ∷ []))) ∷ p/B ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = from-yes (typecheckSession wbg Ρ M)

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed

  -- {A} {B,C}
  module A∣BC where
    Ρ = byOwner own/A∣BC
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = p/A ∷ rec (B ⇐ A ？· ((C ⇒ ⁅ A ⁆ ! here < val (v/bool true) >∙ v 0F) ∷ [])) ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = from-yes (typecheckSession wbg Ρ M)

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed

  -- {A,B,C}: an internal loop, invisible from the one process.
  module ABC where
    Ρ : Assignment 1
    Ρ = byOwner λ _ → 0F
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = ∅ ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = from-yes (typecheckSession wbg Ρ M)

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed
