{-# OPTIONS --guardedness #-}

-- RETRACTED counterexample, kept as a worked example of *why* it fails.
--
-- Original claim: `rec Pr` types at `s` ONLY via `t/skip` (universal
-- forward exploration to a leaf anchored at `H`), NOT via a direct `t/rec`
-- at `s` itself, because the leaf's `v 0` needs `H ~ H` while a direct
-- check at `s` would need `s ~ H` (false in this graph). Wrong: `v X`'s
-- rule is not just `t/var` (exact anchor match) but `t/unskip` composed
-- with `t/var` (anchor matches *some* `¬P`-reachable predecessor of the
-- lookup site). Since the anchor `s` trivially reaches itself
-- (reflexivity) and `s -[¬A]->* H` is exactly the same edge the outer
-- skip used, the direct-at-`s` route succeeds too, via that route instead
-- of plain `t/var`. Both derivations below compile, confirming this.

module Tests.RecSkipCounterexample where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr using (s/unit; val; v/unit; tv/unit; te/val)
import Definitions.Typing as Typing

open import Definitions.Graph.Algebra 3
open import Definitions.Graph.Core 3 using (State; graphTheory; step⇒listed)
open import Definitions.Graph.Decision 3 using (wellBehaved?)
open import Definitions.Actions 3 using (_⟶_; _#_) renaming (_<_> to mkChoice)

A B C : Fin 3
A = zero
B = suc zero
C = suc (suc zero)

lbl : Fin 1
lbl = zero

-- states: 0 = s, 1 = H (2 = the DSL's own unused distinguished `ended`)
g : OpenGraph 0
g = openGraph 2 (node zero)
  ( ( ((B ⟶ C # mkChoice lbl s/unit) , node (suc zero)) ∷ [] )   -- s --β--> H, β = B→C, A uninvolved
  v∷ ( ((A ⟶ B # mkChoice lbl s/unit) , node (suc zero)) ∷ [] )  -- H --A→B--> H  (self-loop)
  v∷ v[]
  )

RG = compile g
G  = underlying RG

-- `opaque`, and it matters enormously: `toWitness (wellBehaved? G)` is a
-- module-level *definition*, and Agda unfolds definitions at every use
-- site (it shares argument thunks, not definition applications).  Left
-- transparent, every type mentioning `Typing.MPST wb` that has to be
-- normalised re-runs the whole decision procedure, and the cost compounds
-- per definition — this file used to cost ~28 GB resident and ~3.5 min.
-- Still a real proof: only the body is hidden from the evaluator, unlike
-- a postulate.
opaque
  wb : Typing.WellBehaved (graphTheory G)
  wb = toWitness {a? = wellBehaved? G} tt

open Typing.MPST wb hiding (_<_>; _#_; _⟶_)

s H : State G
s = zero
H = suc zero

-- Named so the `skip/step`/`skip/one` implicits below can be pinned: with
-- `wb` opaque they are no longer recoverable by computing the type of the
-- `tt`-valued step proofs.
βBC : Action
βBC = B ⟶ C # mkChoice lbl s/unit

Pr : Proc 0 1
Pr = B ! lbl < val v/unit >∙ (v zero)

mg : MessageGuarded Pr
mg = mg/send

grH : H -< A ⟶ B # mkChoice lbl s/unit >-> H
grH = tt

gr : s -< B ⟶ C # mkChoice lbl s/unit >-> H
gr = tt

A∉β : A ∉α (B ⟶ C # mkChoice lbl s/unit)
A∉β = ¬∈c→∉c (λ { (∈S ()) ; (∈R ()) })

na : A not-active-in s
na {α} {G′} gr′ with step⇒listed {G = G} {s = s} {α = α} {t = G′} gr′
... | here refl = A∉β
... | there ()

-- Route 1: outer `t/skip` wraps `rec Pr`, anchor = H, closes `v 0` via
-- *direct* `t/var` (H ~ H, reflexivity).

bodyH : v[] & (H v∷ v[]) ⊢p A ◂ Pr ∶ H
bodyH = t/send grH (te/val tv/unit) (t/var ~refl)

leafH : v[] & v[] ⊢p A ◂ (rec Pr) ∶ H
leafH = t/rec mg bodyH

-- `step⇒listed`'s implicits pinned: with `wb` opaque they are no longer
-- recoverable by computing `gr′`'s type, and an unsolved `{s = _}` leaves
-- the `with`-scrutinee's list stuck, so `here` cannot be case-split.
ktd :
  ∀ {G″ β} → (gr′ : s -< β >-> G″)
  → (v[] & v[] ⊢p_∶_) & (s v∷ v[]) ⊢skip A ◂ (rec Pr) ∶ G″
ktd {G″} {β} gr′ with step⇒listed {G = G} {s = s} {α = β} {t = G″} gr′
... | here refl = skip/main leafH
... | there ()

x : (v[] & v[] ⊢p_∶_) & v[] ⊢skip A ◂ (rec Pr) ∶ s
x = skip/step {α = βBC} {G' = H} gr na ktd

typed-via-skip : v[] & v[] ⊢p A ◂ (rec Pr) ∶ s
typed-via-skip = t/skip x

-- Route 2: `t/rec` applied directly at `s` (no outer skip at all). `Pr`'s
-- own internal `t/skip` walks the *same* edge to find the send at `H`;
-- `v 0`'s continuation closes via `t/unskip` (the same edge again) +
-- `t/var ~refl` at `s`, NOT plain `t/var` (which would need `s ~ H`,
-- false: `s`'s only move is `β`, `H`'s only move is the `A⟶B` self-loop).

contS : v[] & (s v∷ v[]) ⊢p A ◂ (v zero) ∶ H
contS = t/unskip (skip/one {G′ = H} {α = βBC} gr A∉β) (t/var ~refl)

bodyS-leaf : v[] & (s v∷ v[]) ⊢p A ◂ Pr ∶ H
bodyS-leaf = t/send grH (te/val tv/unit) contS

ktdS :
  ∀ {G″ β} → (gr′ : s -< β >-> G″)
  → (v[] & (s v∷ v[]) ⊢p_∶_) & (s v∷ v[]) ⊢skip A ◂ Pr ∶ G″
ktdS {G″} {β} gr′ with step⇒listed {G = G} {s = s} {α = β} {t = G″} gr′
... | here refl = skip/main bodyS-leaf
... | there ()

bodyS : v[] & (s v∷ v[]) ⊢p A ◂ Pr ∶ s
bodyS = t/skip (skip/step {α = βBC} {G' = H} gr na ktdS)

typed-directly : v[] & v[] ⊢p A ◂ (rec Pr) ∶ s
typed-directly = t/rec mg bodyS
