{-# OPTIONS --guardedness #-}

-- Port of `main`'s Examples/IndepW.agda: two independent worker pipelines
-- `S → A1 → B1 → C1` and `S → A2 → B2 → C2` behind a shared source `S`,
-- with all cross-pipeline steps interleavable — the stress test for the
-- diamond/independence machinery.
--
-- Unlike the flattening-algebra version, this is built as a syntactic
-- `Net` (`LTS/Network.agda`): three small base graphs combined with `∥`/`⨾`
-- — no product graph is ever materialized. Well-behavedness is a
-- compositional `WBNet` certificate (`Definitions/TypeChecker/Network.agda`):
-- each `base` leaf is `wellBehaved?` on its own tiny presentation, `∥`
-- needs only decided participant-disjointness (`ParWB`'s diamond is free),
-- and `⨾` needs the decided seam-causality checks plus one decided
-- `stepback/~` sweep over the *composite's* presentation (the one axiom
-- that provably cannot be checked seam-locally — `LTS/NetworkSeq.agda`).
--
-- `main` needed ~1040 lines (custom `BTheory` + ~7 mutually recursive
-- `Active?`/`Causal?` families per pipeline) and never assembled a full
-- session judgment — only per-participant typings.  Here the whole 7-way
-- session is one `typecheckSessionNet` call.

module Examples.IndepW where

open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming ([] to v[]; _∷_ to _v∷_)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (toWitness)

open import Definitions.Expr using (s/unit; val; v/unit)
open import Definitions.TypeChecker
import Definitions.Typing as Typing

open import LTS.Algebra 7 using (OpenGraph; end; _∙_; μ; var; underlying; initial)
open import LTS.Network 7 using (Net; base; _∥_; _⨾_; present)
open import Definitions.Actions 7 renaming (_<_> to mkChoice) hiding (_,_)
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
  itm P Q = P ⟶ Q # mkChoice here s/unit

-- one worker pipeline loop: `Ai` feeds `Bi`, which feeds `Ci`, forever
pipeTail : Fin 7 → Fin 7 → Fin 7 → OpenGraph 0
pipeTail Ai Bi Ci = μ (itm Ai Bi ∙ itm Bi Ci ∙ var zero)

-- `main`'s specification: `S` seeds `A1` *first*; only then does the first
-- pipeline run in parallel with (`S` seeding `A2`, then the second
-- pipeline).  Written as a net of three base graphs: the outer `⨾` is the
-- `S→A1 ≺ S→A2` precedence, the inner `∥` lets `A1→B1` overtake `S→A2`, and
-- the inner `⨾` is `S→A2 ≺ A2→B2` — exactly `main`'s hand-interleaved
-- graph, now never flattened into one product.
indepw : Net
indepw =
  base (itm S A1 ∙ end)
    ⨾ (base (pipeTail A1 B1 C1)
        ∥ (base (itm S A2 ∙ end) ⨾ base (pipeTail A2 B2 C2)))

wnet : WBNet indepw
wnet = base ⨾ (base ∥ (base ⨾ base))

open Typing.MPST (wb-net wnet) using (⊢s_∶_)

p/S : Proc 0 0
p/S = A1 ! here < val v/unit >∙ (A2 ! here < val v/unit >∙ ∅)

-- generic pipeline stages, as on `main`
p/A : Fin 7 → Proc 0 0
p/A B = Σ S ？[ s/unit v∷ v[] ]·
          (  (B ! here < val v/unit >∙
              (rec (B ! here < val v/unit >∙ v zero)))
          v∷ v[])

p/B : Fin 7 → Fin 7 → Proc 0 0
p/B A C = rec (Σ A ？[ s/unit v∷ v[] ]·
                ((C ! here < val v/unit >∙ v zero) v∷ v[]))

p/C : Fin 7 → Proc 0 0
p/C B = rec (Σ B ？[ s/unit v∷ v[] ]· (v zero v∷ v[]))

M : Session
M = p/S v∷ p/A B1 v∷ p/B A1 C1 v∷ p/C B1
        v∷ p/A B2 v∷ p/B A2 C2 v∷ p/C B2 v∷ v[]

wtd : Dec (⊢s M ∶ initial (present indepw))
wtd = typecheckSessionNet wnet M

M-well-typed : ⊢s M ∶ initial (present indepw)
M-well-typed = toWitness {a? = wtd} _
