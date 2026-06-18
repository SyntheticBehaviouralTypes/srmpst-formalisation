{-# OPTIONS --guardedness #-}

-- Two independent worker pipelines `S → A1 → B1 → C1` and
-- `S → A2 → B2 → C2` behind a shared source `S`, built as a `Net` and
-- certified compositionally (`WBNet`).

module Examples.IndepW where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using (_∷_)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr using (s/unit; val; v/unit)
open import Check
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 7 using (OpenGraph; end; _∙_; μ; var; initial)
open import Definitions.Graph.Network 7 using (Net; base; _∥_; _⨾_; present)
open import Data.Fin.Subset using (⁅_⁆)
open import Definitions.Actions 7 renaming (_<_> to mkChoice)
open import Definitions.Proc 7

S A1 B1 C1 A2 B2 C2 : Fin 7
S  = zero
A1 = suc zero
B1 = suc (suc zero)
C1 = suc (suc (suc zero))
A2 = suc (suc (suc (suc zero)))
B2 = suc (suc (suc (suc (suc zero))))
C2 = suc (suc (suc (suc (suc (suc zero)))))

here : Fin 1
here = zero

private
  itm : Fin 7 → Fin 7 → _
  itm P Q = P ⟶ ⁅ Q ⁆ # mkChoice here s/unit

-- one worker pipeline loop: `Ai` feeds `Bi`, which feeds `Ci`, forever
pipeTail : Fin 7 → Fin 7 → Fin 7 → OpenGraph 0
pipeTail Ai Bi Ci = μ (itm Ai Bi ∙ itm Bi Ci ∙ var zero)

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
p/S = S ⇒ ⁅ A1 ⁆ ! here < val v/unit >∙ (S ⇒ ⁅ A2 ⁆ ! here < val v/unit >∙ ∅)

-- Pipeline stages; each takes its own role first.
p/A : Fin 7 → Fin 7 → Proc 0 0
p/A A B = A ⇐ S ？·
            (  (A ⇒ ⁅ B ⁆ ! here < val v/unit >∙
                (rec (A ⇒ ⁅ B ⁆ ! here < val v/unit >∙ v zero)))
            v∷ v[])

p/B : Fin 7 → Fin 7 → Fin 7 → Proc 0 0
p/B B A C = rec (B ⇐ A ？·
                  ((B ⇒ ⁅ C ⁆ ! here < val v/unit >∙ v zero) v∷ v[]))

p/C : Fin 7 → Fin 7 → Proc 0 0
p/C C B = rec (C ⇐ B ？· (v zero v∷ v[]))

open import Safety (wb-net wnet) (sync-net wnet) using (⊢s[_]_∶_)

-- One process per role (the only partition checked).
open Over singletons using (Session)

M : Session
M = p/S v∷ p/A A1 B1 v∷ p/B B1 A1 C1 v∷ p/C C1 B1
        v∷ p/A A2 B2 v∷ p/B B2 A2 C2 v∷ p/C C2 B2 v∷ v[]

M-typed : ⊢s[ singletons ] M ∶ initial (present indepw)
M-typed = toWitness {a? = typecheckSessionNet wnet singletons M} _
