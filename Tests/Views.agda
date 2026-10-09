{-# OPTIONS --guardedness #-}

-- Multi-role processes checked against their local views; every verdict
-- forced.

module Tests.Views where

open import Data.Bool using (true; false)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Fin.Subset using (⁅_⁆; _∪_)
open import Data.Vec using ([]; _∷_)
open import Data.Product using (proj₁)
open import Relation.Nullary.Decidable using (does; ⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Definitions.Expr using (s/unit; val; v/unit)
open import Definitions.Graph.Decision 3 using (wellBehaved?)
open import Definitions.Graph.View 3 using (viewGraph)
open import Definitions.Graph.Algebra 3
open import Definitions.Actions 3 renaming (_<_> to mkChoice)
open import Definitions.Proc 3
open import Check

A B C : Fin 3
A = 0F
B = 1F
C = 2F

here : Fin 1
here = 0F

-- A → B → C → A.  Block {A,B}: `A→B` is internal.
module RoundRobin where
  round : OpenGraph 0
  round =
    (A ⟶ ⁅ B ⁆ # mkChoice here s/unit) ∙
    ((B ⟶ ⁅ C ⁆ # mkChoice here s/unit) ∙
     ((C ⟶ ⁅ A ⁆ # mkChoice here s/unit) ∙ end))

  wbg : WBGraph {N = 3}
  wbg = buildG round

  AB = ⁅ A ⁆ ∪ ⁅ B ⁆

  _ : ⌊ wellBehaved? (viewGraph (underlying (proj₁ wbg)) AB) ⌋ ≡ true
  _ = refl

  -- `A→B` is hidden: the process of {A,B} sends at `B`, then receives at `A`.
  _ : does (typecheck wbg AB
              (B ⇒ ⁅ C ⁆ ! here < val v/unit >∙ (A ⇐ C ？· (∅ ∷ []))))
      ≡ true
  _ = refl

  -- Its internal step is no action of the code.
  _ : does (typecheck wbg AB (A ⇒ ⁅ B ⁆ ! here < val v/unit >∙ ∅)) ≡ false
  _ = refl
