{-# OPTIONS --guardedness #-}

-- A `Wait` tree that must revisit a state on its path.
--
--   u --A→B[0]--> t,   u --A→B[1]--> ℓ,   t --B→A--> u,   ℓ --A→C--> end
--
-- `C`'s receive at `u`: the tree steps u → t → u, then on to `ℓ`.

module Tests.Perf09_RevisitSpine where

open import Definitions.Expr.Syntax
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (from-yes)

open import Definitions.Expr using (s/bool)
open import Check
import Definitions.Typing as Typing

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

ack result : Fin 1
ack    = 0F
result = 0F

-- `A` to `B`: go round again, or be done
again done : Fin 2
again = 0F
done  = 1F

-- states: 0 = u, 1 = t, 2 = ℓ, plus the DSL's distinguished end
-- (u → t → u, and u → ℓ)
g : OpenGraph 0
g =
  μ X ·
    ⟪ A ⟶ ⁅ B ⁆ # again < s/bool > ∙ B ⟶ ⁅ A ⁆ # ack < s/bool > ∙ X
    ∣ A ⟶ ⁅ B ⁆ # done < s/bool >  ∙ A ⟶ ⁅ C ⁆ # result < s/bool > ∙ end
    ⟫

wbg : WBGraph {N = 3}
wbg = buildG g {p = tt}

open import Safety (wb-of wbg) (sync-of wbg) using (⊢ᵛ[_]_∶_)

-- C waits for A's message — deliverable only through the revisiting spine
p : Proc 0 0
p = C ⇐ A ？· ⟪ result ↦ ∅ ⟫

wtd : Dec (⊢ᵛ[ ⁅ C ⁆ ] p ∶ initial (proj₁ wbg))
wtd = typecheck wbg ⁅ C ⁆ p

C-well-typed : ⊢ᵛ[ ⁅ C ⁆ ] p ∶ initial (proj₁ wbg)
C-well-typed = from-yes wtd
