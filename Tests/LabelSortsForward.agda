{-# OPTIONS --guardedness #-}

-- As `Tests/LabelSorts.agda`, but the branch body uses the received value:
-- it types when the protocol forwards it at the same sort.
--
--    A⟶C # 0<unit>       A⟶B # 0<nat>        B⟶C # 0<nat>
-- s₀ ───────────────► s₁ ───────────────► t₁ ───────────────► ended
--  │
--  │ A⟶C # 1<unit>       A⟶B # 0<bool>       B⟶C # 0<bool>
--  └───────────────► s₂ ───────────────► t₂ ───────────────► ended
--
-- `p/B` forwards what it received: `C ! here < var zero >∙ ∅`.

module Tests.LabelSortsForward where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
open import Data.Bool using (true)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr
  using (s/bool; s/nat; s/unit; val; v/nat; v/bool; v/unit; var)
open import Check hiding (base; _∥_; _⨾_)
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 3 renaming (var to gvar)
open import Data.Fin.Subset using (⁅_⁆)
open import Definitions.Actions 3 renaming (_<_> to mkChoice)
open import Definitions.Proc 3

A B C : Fin 3
A = zero
B = suc zero
C = suc (suc zero)

here : Fin 1
here = zero

lbl0 lbl1 : Fin 2
lbl0 = zero
lbl1 = suc zero

g : OpenGraph 0
g =
  choice
    ((A ⟶ ⁅ C ⁆ # mkChoice lbl0 s/unit) ⇒
      ((A ⟶ ⁅ B ⁆ # mkChoice here s/nat) ∙
       (B ⟶ ⁅ C ⁆ # mkChoice here s/nat) ∙ end))
    ( ((A ⟶ ⁅ C ⁆ # mkChoice lbl1 s/unit) ⇒
        ((A ⟶ ⁅ B ⁆ # mkChoice here s/bool) ∙ (B ⟶ ⁅ C ⁆ # mkChoice here s/bool) ∙ end))
    ∷ [])

wbg : WBGraph {N = 3}
wbg = buildG g {p = tt}

open import Safety (wb-of wbg) (sync-of wbg) using (⊢s[_]_∶_)

p/A : Proc 0 0
p/A =
  ifp val (v/bool true)
  then (A ⇒ ⁅ C ⁆ ! lbl0 < val v/unit >∙
         (A ⇒ ⁅ B ⁆ ! here < val (v/nat 0) >∙ ∅))
  else (A ⇒ ⁅ C ⁆ ! lbl1 < val v/unit >∙
         (A ⇒ ⁅ B ⁆ ! here < val (v/bool true) >∙ ∅))

-- USES the bound variable, at two different sorts, in one derivation
p/B : Proc 0 0
p/B = B ⇐ A ？· ((B ⇒ ⁅ C ⁆ ! here < var zero >∙ ∅) v∷ v[])

p/C : Proc 0 0
p/C =
  C ⇐ A ？·
    (  (C ⇐ B ？· (∅ v∷ v[]))
    v∷ (C ⇐ B ？· (∅ v∷ v[]))
    v∷ v[])

M : Over.Session singletons
M = p/A v∷ p/B v∷ p/C v∷ v[]

wtd : Dec (⊢s[ singletons ] M ∶ initial (proj₁ wbg))
wtd = typecheckSession wbg singletons M

well-typed : ⊢s[ singletons ] M ∶ initial (proj₁ wbg)
well-typed = toWitness {a? = wtd} _
