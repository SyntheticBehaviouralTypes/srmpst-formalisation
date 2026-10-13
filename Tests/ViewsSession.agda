{-# OPTIONS --guardedness #-}

-- A multi-role session typed by `typecheckSession`, then `Safety`'s
-- theorems applied.  RoundRobin `A → B → C → A`, blocks `{A,B}` and `{C}`.

module Tests.ViewsSession where

open import Definitions.Expr.Syntax
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Fin.Subset using (⁅_⁆; _∈_; inside; outside)
open import Data.Vec using (Vec; []; _∷_; here; there; lookup)
open import Data.Sum using (_⊎_)
open import Data.Product using (∃-syntax; _×_)
open import Data.List using (length)
open import Relation.Nullary.Decidable using (from-yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Definitions.Common 3 using (PartSet)
open import Definitions.Expr using (s/unit; val; v/unit)
open import Definitions.Behav using (WellBehaved; Synchronous)
open import Definitions.Graph.Core 3 using (graphTheory)
open import Definitions.Graph.Algebra 3
open import Definitions.Actions 3
open import Definitions.Proc 3 hiding (rec; _⇐_？·_)
open import Definitions.Proc.Syntax 3
open import Utils.Branch using (⟪_⟫; _↦_; _∣_)
open import Check

A B C : Fin 3
A = 0F
B = 1F
C = 2F

token : Fin 1
token = 0F

round : OpenGraph 0
round =
  A ⟶ ⁅ B ⁆ # token < s/unit > ∙
  B ⟶ ⁅ C ⁆ # token < s/unit > ∙
  C ⟶ ⁅ A ⁆ # token < s/unit > ∙ end

wbg : WBGraph {N = 3}
wbg = buildG round

G = underlying (compile round)
s₀ = initial (compile round)

-- ── The assignment: {A,B} ↦ 0, {C} ↦ 1 ────────────────────────────────

Ρ : Assignment 2
Ρ = record
  { roles   = roles
  ; owner   = owner
  ; owner/∈ = owner/∈
  ; ∈/owner = ∈/owner
  }
  where
    roles : Vec PartSet 2
    roles = (inside ∷ inside ∷ outside ∷ [])
          ∷ (outside ∷ outside ∷ inside ∷ [])
          ∷ []

    owner : Fin 3 → Fin 2
    owner 0F = 0F
    owner 1F = 0F
    owner 2F = 1F

    owner/∈ : ∀ R → R ∈ lookup roles (owner R)
    owner/∈ 0F = here
    owner/∈ 1F = there here
    owner/∈ 2F = there (there here)

    ∈/owner : ∀ {j R} → R ∈ lookup roles j → owner R ≡ j
    ∈/owner {0F} {0F} _ = refl
    ∈/owner {0F} {1F} _ = refl
    ∈/owner {0F} {2F} (there (there ()))
    ∈/owner {1F} {0F} ()
    ∈/owner {1F} {1F} (there ())
    ∈/owner {1F} {2F} _ = refl

-- ── The global witnesses, `opaque` (see `Tests/SkipBeforeVar.agda`) ────

opaque
  wb : WellBehaved (graphTheory G)
  wb = wb-of wbg

  sync : Synchronous (graphTheory G)
  sync = sync-of wbg

open import Safety wb sync using (⊢s[_]_∶_; safety; module Global)
open Over Ρ
open Global Ρ using (_-[_]->ᵍ_)

-- ── The session ───────────────────────────────────────────────────────

p/AB p/C : Proc 0 0
p/AB = B ⇒ ⁅ C ⁆ ! token < unit >∙ A ⇐ C ？· ⟪ token ↦ ∅ ⟫
p/C  = C ⇐ B ？· ⟪ token ↦ C ⇒ ⁅ A ⁆ ! token < unit >∙ ∅ ⟫

M : Session
M = p/AB ∷ p/C ∷ []

M-typed : ⊢s[ Ρ ] M ∶ s₀
M-typed = from-yes (typecheckSession wbg Ρ M)

M-safe : ∀ {αs M′} → M =[ αs ]⇒* M′
       → ∃[ G′ ] s₀ -[ αs ]->ᵍ G′ × ⊢s[ Ρ ] M′ ∶ G′
                 × (∀ n → ∃[ βs ] ∃[ M″ ] M′ =[ βs ]⇒* M″ × (finished M″ ⊎ length βs ≡ n))
M-safe = safety Ρ M-typed
