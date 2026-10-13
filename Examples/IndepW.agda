{-# OPTIONS --guardedness #-}

-- Two independent worker pipelines `S → A1 → B1 → C1` and
-- `S → A2 → B2 → C2` behind a shared source `S`, built as a `Net` and
-- certified compositionally (`WBNet`).

module Examples.IndepW where

open import Definitions.Expr.Syntax
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using (_∷_)
open import Relation.Nullary.Decidable using (from-yes)

open import Definitions.Expr using (s/unit; val; v/unit)
open import Check
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 7
  using (OpenGraph; end; _∙_; prefix/graph; μ; initial)
open import Definitions.Graph.Network 7 using (Net; base; _∥_; _⨾_; present)
open import Data.Fin.Subset using (⁅_⁆)
open import Definitions.Actions 7
open import Definitions.Proc 7 hiding (rec; _⇐_？·_)
open import Definitions.Proc.Syntax 7
open import Utils.Branch using (⟪_⟫; _↦_; _∣_)

S A1 B1 C1 A2 B2 C2 : Fin 7
S  = 0F
A1 = 1F
B1 = 2F
C1 = 3F
A2 = 4F
B2 = 5F
C2 = 6F

item : Fin 1
item = 0F

private
  itm : Fin 7 → Fin 7 → _
  itm P Q = P ⟶ ⁅ Q ⁆ # item < s/unit >

-- one worker pipeline loop: `Ai` feeds `Bi`, which feeds `Ci`, forever
pipeTail : Fin 7 → Fin 7 → Fin 7 → OpenGraph 0
pipeTail Ai Bi Ci = μ X · itm Ai Bi ∙ itm Bi Ci ∙ X

-- `S` seeds `A1`, then the first pipeline runs in parallel with `S`
-- seeding `A2` and the second pipeline.
indepw : Net
indepw =
  base (itm S A1 ∙ end)
    ⨾ (base (pipeTail A1 B1 C1)
        ∥ (base (itm S A2 ∙ end) ⨾ base (pipeTail A2 B2 C2)))

wnet : WBNet indepw
wnet = base ⨾ (base ∥ (base ⨾ base))

p/S : Proc 0 0
p/S = S ⇒ ⁅ A1 ⁆ ! item < unit >∙ S ⇒ ⁅ A2 ⁆ ! item < unit >∙ ∅

-- Pipeline stages; each takes its own role first.
p/A : Fin 7 → Fin 7 → Proc 0 0
p/A A B = A ⇐ S ？·
            ⟪ item ↦ A ⇒ ⁅ B ⁆ ! item < unit >∙
                     rec X · A ⇒ ⁅ B ⁆ ! item < unit >∙ X
            ⟫

p/B : Fin 7 → Fin 7 → Fin 7 → Proc 0 0
p/B B A C =
  rec X · B ⇐ A ？· ⟪ item ↦ B ⇒ ⁅ C ⁆ ! item < unit >∙ X ⟫

p/C : Fin 7 → Fin 7 → Proc 0 0
p/C C B = rec X · C ⇐ B ？· ⟪ item ↦ X ⟫

open import Safety (wb-net wnet) (sync-net wnet) using (⊢s[_]_∶_)

-- One process per role (the only partition checked).
open Over singletons using (Session)

M : Session
M = p/S v∷ p/A A1 B1 v∷ p/B B1 A1 C1 v∷ p/C C1 B1
        v∷ p/A A2 B2 v∷ p/B B2 A2 C2 v∷ p/C C2 B2 v∷ v[]

M-typed : ⊢s[ singletons ] M ∶ initial (present indepw)
M-typed = from-yes (typecheckSessionNet wnet singletons M)
