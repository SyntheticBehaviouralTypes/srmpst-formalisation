{-# OPTIONS --guardedness #-}

-- Port of `main`'s Examples/NoSynGT.agda: `A` picks, at runtime, whether to
-- message `B` then `C` or `C` then `B` — there is no single synchronous
-- global type describing this session, but it is still well-typed (both
-- orders are independent sends). `main` needed a bespoke `BTheory` with
-- explicit `diamond`/`cond-comm` cases just to state this; here the same
-- graph shape is built directly and `typecheckSession` does the independence
-- reasoning on its own.

module Examples.NoSynGT where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr using (s/unit; s/nat; val; v/unit; v/nat; is-zero)
open import Check
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 3
open import Definitions.Actions 3 renaming (_<_> to mkChoice) hiding (_,_)
open import Definitions.Proc 3

A B C : Fin 3
A = zero
B = suc zero
C = suc (suc zero)

here : Fin 1
here = zero

-- from s0: A picks to message B first or C first; both orders must converge
-- on the *literally same* successor state for `wellBehaved?`'s diamond check
-- to close (see Examples/TODO.md).  Since the DSL's `end`s all collapse to
-- the one distinguished ended state, the two branches below genuinely
-- converge and the plain `choice` combinator suffices (an earlier version of
-- the DSL allocated a fresh node per `end`, which made this graph
-- inexpressible without the raw record constructor).
nosyn : OpenGraph 0
nosyn =
  choice
    ((A ⟶ B # mkChoice here s/unit) ⇒
      ((A ⟶ C # mkChoice here s/unit) ∙ end))
    ( ((A ⟶ C # mkChoice here s/unit) ⇒
        ((A ⟶ B # mkChoice here s/unit) ∙ end))
    ∷ [])

wbg : WBGraph {N = 3}
wbg = buildG nosyn {p = tt}

open Typing.MPST (wb-of wbg) using (⊢s_∶_)

p/A : Proc 0 0
p/A =
  ifp is-zero (val (v/nat 0))
    then (B ! here < val v/unit >∙ (C ! here < val v/unit >∙ ∅))
    else (C ! here < val v/unit >∙ (B ! here < val v/unit >∙ ∅))

p/B : Proc 0 0
p/B = Σ A ？[ s/unit v∷ v[] ]· (∅ v∷ v[])

p/C : Proc 0 0
p/C = Σ A ？[ s/unit v∷ v[] ]· (∅ v∷ v[])

M : Session
M = p/A v∷ p/B v∷ p/C v∷ v[]

wtd : Dec (⊢s M ∶ initial (proj₁ wbg))
wtd = typecheckSession wbg M

M-well-typed : ⊢s M ∶ initial (proj₁ wbg)
M-well-typed = toWitness {a? = wtd} _
