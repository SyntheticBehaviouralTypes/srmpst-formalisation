{-# OPTIONS --guardedness #-}

-- A token ring A → B → C → A, once and in a loop.  All five partitions
-- are accepted.

module Examples.RoundRobin where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using ([]; _∷_)
open import Data.Bool using (true)
open import Data.Product using (proj₁; ∃-syntax; _×_)
open import Data.List using (length)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Sum using (_⊎_)
open import Relation.Nullary.Decidable using (toWitness)

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

here : Fin 1
here = zero

-- The partitions with two blocks, as owner maps.
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
    M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

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
    M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

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
    M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

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
    M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed

  -- {A,B,C}: everything is internal; the one process has nothing to do.
  module ABC where
    Ρ : Assignment 1
    Ρ = byOwner λ _ → zero
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = ∅ ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

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
        ((C ⟶ ⁅ A ⁆ # mkChoice here s/bool) ∙ var zero)))

  wbg : WBGraph {N = 3}
  wbg = buildG round

  s₀ = initial (proj₁ wbg)

  open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_; safety; module Global)

  p/A p/B p/C : Proc 0 0
  p/A = rec (A ⇒ ⁅ B ⁆ ! here < val (v/bool true) >∙
              (A ⇐ C ？· (v zero ∷ [])))
  p/B = rec (B ⇐ A ？·
              ((B ⇒ ⁅ C ⁆ ! here < val (v/bool true) >∙ v zero) ∷ []))
  p/C = rec (C ⇐ B ？·
              ((C ⇒ ⁅ A ⁆ ! here < val (v/bool true) >∙ v zero) ∷ []))

  -- {A} {B} {C}
  module A∣B∣C where
    Ρ = singletons
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = p/A ∷ p/B ∷ p/C ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

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
    M = rec (B ⇒ ⁅ C ⁆ ! here < val (v/bool true) >∙ (A ⇐ C ？· (v zero ∷ []))) ∷ p/C ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

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
    M = rec (A ⇒ ⁅ B ⁆ ! here < val (v/bool true) >∙ (C ⇐ B ？· (v zero ∷ []))) ∷ p/B ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

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
    M = p/A ∷ rec (B ⇐ A ？· ((C ⇒ ⁅ A ⁆ ! here < val (v/bool true) >∙ v zero) ∷ [])) ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed

  -- {A,B,C}: an internal loop, invisible from the one process.
  module ABC where
    Ρ : Assignment 1
    Ρ = byOwner λ _ → zero
    open Over Ρ
    open Global Ρ using (_-[_]->ᵍ_)

    M : Session
    M = ∅ ∷ []

    M-typed : ⊢s[ Ρ ] M ∶ s₀
    M-typed = toWitness {a? = typecheckSession wbg Ρ M} _

    M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
           → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                     × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
    M-safe = safety Ρ M-typed
