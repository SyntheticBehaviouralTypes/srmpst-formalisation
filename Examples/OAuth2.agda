{-# OPTIONS --guardedness #-}

-- Port of `main`'s Examples/OAuth2.agda: a server `S` offers `login`/`cancel`
-- to a client `C`; on `login`, `C` forwards a password to the auth service
-- `A`, which reports to `S`; on `cancel`, `C` tells `A` to quit.  Both
-- branches converge on the same terminal state, which forces the raw
-- `openGraph` construction (the DSL would allocate two bisimilar-but-distinct
-- `end`s and break `Stepback` — see Examples/TODO.md).
--
-- On `main` this took a hand-written `BTheory` instance (~150 lines of
-- `can-step?`/`o-indep?`/`~≡` case analyses) plus per-participant
-- `dt/skip`/`Causal?`/`Active?` proofs for `A` (which must skip the initial
-- `S→C` exchange, in *both* branches, before its own receive).  All of that
-- is one `typecheckSession` call here.

module Examples.OAuth2 where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Data.Bool using (true)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr using (s/bool; s/nat; val; v/bool; v/nat)
open import Check
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 3
open import Definitions.Actions 3 renaming (_<_> to mkChoice) hiding (_,_)
open import Definitions.Proc 3

S C A : Fin 3
S = zero
C = suc zero
A = suc (suc zero)

here : Fin 1
here = zero

-- the S→C choice: login/cancel (both carry a nat)
login cancel : Fin 2
login  = zero
cancel = suc zero

-- the C→A choice: passwd (nat) / quit (bool)
passwd quit : Fin 2
passwd = zero
quit   = suc zero

-- s0 --S→C[login]--> s1 --C→A[passwd]--> s2 --A→S[auth]--> ended
-- s0 --S→C[cancel]--> s3 --C→A[quit]----------------------> ended
oauth : OpenGraph 0
oauth = openGraph 4 (node zero)
  ( ( ((S ⟶ C # mkChoice login s/nat) , node (suc zero))
    ∷ ((S ⟶ C # mkChoice cancel s/nat) , node (suc (suc (suc zero))))
    ∷ [] )                                                            -- s0
  v∷ ( ((C ⟶ A # mkChoice passwd s/nat) , node (suc (suc zero)))
     ∷ [] )                                                           -- s1
  v∷ ( ((A ⟶ S # mkChoice here s/bool) , ended) ∷ [] )                 -- s2
  v∷ ( ((C ⟶ A # mkChoice quit s/bool) , ended) ∷ [] )                 -- s3
  v∷ v[]
  )

wbg : WBGraph {N = 3}
wbg = buildG oauth {p = tt}

open Typing.MPST (wb-of wbg) using (⊢s_∶_)

-- the server picks `cancel` (as on `main`)
p/S : Proc 0 0
p/S = C ! cancel < val (v/nat 0) >∙ ∅

-- the client covers both offers: forward the password, or tell `A` to quit
p/C : Proc 0 0
p/C = Σ S ？·
        (  (A ! passwd < val (v/nat 0) >∙ ∅)
        v∷ (A ! quit < val (v/bool true) >∙ ∅)
        v∷ v[])

-- the auth service: authorize towards `S`, or stop
p/A : Proc 0 0
p/A = Σ C ？·
        (  (S ! here < val (v/bool true) >∙ ∅)
        v∷ ∅
        v∷ v[])

M : Session
M = p/S v∷ p/C v∷ p/A v∷ v[]

wtd : Dec (⊢s M ∶ initial (proj₁ wbg))
wtd = typecheckSession wbg M

M-well-typed : ⊢s M ∶ initial (proj₁ wbg)
M-well-typed = toWitness {a? = wtd} _
