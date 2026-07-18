# Examples — rebuild plan

`main` has nine example files under `Examples/`, all built against the *old* concrete
`Global`-type framework (`Definitions/Types.agda`, `Definitions/GlobalTypesWPar.agda`),
each with a hand-written `BTheory`/`BT-Prop` instance (`step-det`, `~stepback`,
`diamond`, `cond-comm`, `can-step?`, …) and a **fully manual** typing derivation per
participant (often using ad-hoc `must-skip`/`Causal?`/`Active?` lemmas specific to that
example). None of that infrastructure exists on `simplified-theory` — and none of it
should be rebuilt. The whole point of the graph-based decision procedure
(`Definitions.TypeChecker.typecheck`) is that the finite-graph `BTheory` instance and
its well-behavedness proof come for free from `buildG`, and the typing derivation comes
for free from `typecheck`/`typecheckSession`. Porting an example now means:

1. Describe the protocol as an `OpenGraph 0` (`LTS.Algebra`'s `end`/`var`/`μ`/`_∙_`/
   `choice`/`Alternative` DSL) instead of a `Global`/custom `BTheory`.
2. Write the per-participant `Proc 0 0` values (current `Definitions.Proc` syntax is
   close enough to the old one that this is close to copy-paste — see "Syntax deltas"
   below for the handful of real differences).
3. State well-typedness as `Dec (...)` via `typecheck`/`typecheckSession` applied to
   `buildG openGraph`, instead of postulating a `Global` and writing `⊢s M ∶ G`.
4. Discharge it by *running* the decision procedure (`yes _` — nothing to prove by
   hand), or, for the negative examples, confirm `no _`.
5. Optionally: instantiate `Safety.progress`/`preservation`/`no-infinite-τ-reductions`
   at the concrete `wb-of (buildG ...)` witness, to get a session-specific safety
   corollary "for free" from the general theorem.

## Import recipe (confirmed working, use verbatim per example)

```agda
open import LTS.Algebra N
open import Definitions.Actions N renaming (_<_> to mkChoice)
open import Definitions.Proc N
open import Definitions.TypeChecker
import Definitions.Typing as Typing
```

Gotchas found while validating this on `SendRecv`/`PingPong`/`NoSynGT` (all
parse/scope-level, not semantic — worth stating precisely so they don't need
re-discovering per example):

- `Definitions.Actions`'s `Choice` constructor `_<_>` collides with `Proc`'s
  `_!_<_>∙_` send syntax if both are opened unqualified — rename it on import
  (`renaming (_<_> to mkChoice)`); build actions as `A ⟶ B # mkChoice label sort`.
  `LTS.Algebra`'s own `_∙_` does *not* need renaming — it does not clash with `∙`
  inside `_!_<_>∙_` (that syntax is a single fused token `>∙`, not `>` then `∙`).
- `_!_<_>∙_`'s `>∙` must be written **adjacent, no space** (`e >∙ Pr`, not
  `e > ∙ Pr`) — with a space Agda tokenizes `>` and `∙` separately and neither is a
  registered operator on its own, so the parse just fails with no useful operator
  list in the error.
- A bare `zero` used as a non-branching send/receive index (`Q ! zero < e > ∙ Pr`,
  `A ⟶ B # mkChoice zero s/bool`) leaves the implicit `I`/`nchoices` **unsolved** —
  nothing else pins it. Fix: define `here : Fin 1; here = zero` once per example file
  and use `here` in place of a bare `zero` at every singleton choice/index site.
- **State the actual `⊢s M ∶ G` type, don't hide it behind `Dec _`.** Import
  `Definitions.Typing as Typing`, then, once `wbg : WBGraph` and `wb-of wbg` are in
  hand, `open Typing.MPST (wb-of wbg) using (⊢s_∶_)` (restrict to just this name —
  opening the whole `MPST` unqualified re-imports `Proc`/`Session`/etc. under a
  *different* instantiation path than the file's own top-level `Definitions.Proc N`
  import, which Agda then reports as ambiguous). State
  `wtd : Dec (⊢s M ∶ initial (proj₁ wbg))`, run it via `typecheckSession wbg M`, and
  extract a genuine derivation with `M-well-typed = toWitness {a? = wtd} _` (stdlib
  2.2's `toWitness`'s implicit is named `a?`, not `Q`) rather than just sanity-checking
  `Dec` reduces to `yes` via `T ⌊ wtd ⌋`.
- When building a *raw* `OpenGraph`/`Graph` (see next section) rather than going
  through `choice`/`_∙_`/`end`, the node table is `Vec (List (Action × Ref δ n)) n` —
  both `Vec` and `List` have `[]`/`_∷_`, and having both unqualified is ambiguous the
  same way `Choice`'s `_<_>` was. Import `Data.Vec` renamed
  (`renaming ([] to v[]; _∷_ to _v∷_)`) and leave `Data.List`'s `[]`/`_∷_` unqualified
  (used far more often in this shape); use `v[]`/`_v∷_` only for the outer per-node
  `Vec`. Also: `Definitions.Actions` exports its own `_∉c_` record constructor `_,_`
  (unrelated to pairing) — `hiding (_,_)` on that import before pulling in
  `Data.Product`'s `_,_`; and write edge pairs with explicit parens around the action,
  `((A ⟶ B # …) , target)` — `_,_` and `_#_` share precedence level 4 with different
  fixity (`infixr` vs `infix`), so relying on precedence alone to disambiguate fails
  to parse.

Validated end-to-end on `Examples/SendRecv.agda`, `Examples/PingPong.agda`,
`Examples/NoSynGT.agda` (`--no-allow-unsolved-metas` green, real `⊢s M ∶ G` witnesses
extracted via `toWitness`, not just `Dec` sanity checks).

## Major finding: `step-diamond` needs a *literally shared* target state

`WellBehaved.step-diamond` (`Definitions/Behav.agda`) states, for two `⋄`-independent
actions out of the same state: `∃[ G′ ] (G₁ -< α′ >-> G′) × (G₂ -< α >-> G′)` — **one**
witness state `G′` both continuations must reach. For the concrete graph `BTheory`,
`Behav = Fin (size G)`, so this is exact index equality, not bisimilarity.

`OpenGraph`'s ergonomic combinators (`choice`/`_∙_`/`end`/`μ`/`var`) always allocate
**fresh** nodes for each sub-term — two syntactically-identical `end`s used in two
different branches become two different (merely bisimilar) states after `compile`.
Building `NoSynGT`'s "A picks B-then-C or C-then-B, converging on done" shape the
naive way (`choice (… ⇒ (… ∙ end)) (… ⇒ (… ∙ end) ∷ [])`, one `end` per branch) makes
`wellBehaved?` genuinely return `no` — **not** a bug in the algebra (the `⋄`
independence check is correct: `A→B`/`A→C` have disjoint receivers, diamond is
required and should hold), but a representation bug in that construction: two
distinct states were built to represent what should be one.

Fix: build the graph so the converging point is a *literally shared* node index. The
`OpenGraph`/`Graph` DSL has no combinator for this (its only sharing primitive is
`μ`/`var`, which reference an *enclosing recursion's own root*, not an arbitrary
later node — using it here would turn a terminating protocol into a looping one).
Use the raw `openGraph : (nodes : ℕ) → Ref δ nodes → Vec (List (Action × Ref δ nodes))
nodes → OpenGraph δ` record constructor instead, with explicit `Fin` indices, giving
both converging edges the *same* target index (`Ref 0 n = ⊥ ⊎ Fin n`, use `inj₂`
throughout for a non-recursive graph). `buildG` still accepts the result — no change
needed there, this is purely about how the `OpenGraph` value is constructed. Confirmed
on `NoSynGT`: `wellBehaved?` fails on the naive construction, succeeds (and
`--no-allow-unsolved-metas` goes green) on the shared-index one.

**This affects any example where two `⋄`-independent actions are enabled from the
same graph state and their continuations reconverge** — re-examining `main`'s state
machines with this in mind:
- **RecMW**: state `s1` has *both* `m→w2/dat1` (M→W2) and `w1→r/res1` (W1→R) enabled
  (`main`'s own states show this — it's not purely the sequential chain it looks like
  at a glance), independent, reconverging at `s2`. Needs the raw-constructor treatment.
- **IndepW**: state `s1` has both `s→a2/1` (S→A2) and `a1→b1/1` (A1→B1) enabled,
  independent, reconverging at `s4` (and further diamonds deeper in). Needs it too,
  likely more than once given the file's size.
- **OAuth2**'s `login`/`cancel` split does *not* need this: both alternatives are
  `S→C` (same sender **and** receiver, different label) — mutually exclusive branches
  of one `Σ`-choice, not independent commuting actions, so `⋄` doesn't even hold
  between them and no diamond obligation arises. Two separate `end` copies (one per
  branch) are fine there; `t/end` only needs *local* absence of further activity, not
  a shared target.
- **RoundRobin**, **Rec2Buy**: appear to be single-path chains per state (each state
  has exactly one outgoing participant-pair at a time) from re-reading `main`'s `LTS`
  constructors — no obviously-independent pair sharing a source state, so likely fine
  with `choice`/`_∙_` as originally planned, but worth double-checking each state's
  full out-edge set before assuming so, given RecMW's shape was easy to miss on a
  first pass.

**Revision (confirmed on `CounterExamples`):** the rule is broader than diamond
specifically. `CounterExamples`'s `A ⟶ B` two-label choice (*same* sender and
receiver — not `⋄`-independent, no diamond obligation at all) *still* failed
`wellBehaved?`, because the label-0 branch's `end` and the label-1 branch's
eventual `end` were two separate-but-bisimilar states, which violates the
`Stepback` axiom (`LTS/Decision.agda`'s `FiniteStepback`/`StepbackAt`) — a
different axiom than diamond, same root cause. Fixed the same way: raw
`openGraph` with the two branches sharing one `end` index (confirmed both by a
minimal 2-state isolated test and on the full example). **Practical rule of
thumb going forward: build every `OpenGraph` with the raw constructor and
explicit shared indices whenever `end` (or any other sub-graph) is used more
than once, not only when the branches are independent/commuting.** `_∙_`/`end`
used *exactly once* (as in `SendRecv`/`PingPong`) is fine; anything with two or
more branches converging is not, regardless of whether it's a `Σ`-choice or a
genuine diamond.

## STATUS: all nine examples ported and green (July 2026)

Every example from `main` now type-checks against the decision procedure, each with a
full `⊢s M ∶ G` witness extracted via `toWitness` (including the 7-way `IndepW`
session `main` never assembled, and the recursive `RoundRobin` variant `main`
abandoned).  Warm-cache wall times (≈5s of each is interface loading):
SendRecv/PingPong/NoSynGT/RoundRobin ≈ 6s; CounterExamples 6.1s; OAuth2 8.6s;
Rec2Buy 12.3s; RecMW 32.3s; IndepW 32.9s.

Getting Rec2Buy/RecMW/IndepW into that range required one performance fix in
`SkipDecide.semSkip?` (`Definitions/TypeChecker/Core.agda`): the leaf decider is now
evaluated once per state into a Bool table passed as a *bound argument* to the
sweep, so `reachVia?`'s O(size³) filter evaluations are vector lookups instead of
recursive checker runs (before: Rec2Buy 166s, RecMW killed after >1h).  The
remaining known inefficiency is cross-call: `R?` results are still re-derived per
sweep/anchor demand (no process-level memo tables), and bisimilarity is recomputed
per queried pair — revisit only if bigger examples appear.

## RESOLVED: the fuel-based checker was exponential; replaced by the shape-restricted judgment (July 2026)

The old `Alg`/`checkWithFuelD`/`Saturate.agda` decision procedure re-derived every sub-decision
at every fuel level (`size G ^ (suc (size G) * processFuel Pr)` — measured under `Tests/`:
skip-depth 0 ≈ 5s, depth 1 ≈ 58s, depth 2 > 90s on 2–3-state graphs). It was deleted wholesale
and replaced by the shape-restricted judgment `R = D ⊎ SemSkipP (D …)`
(`Definitions/TypeChecker/Restricted.agda`) with a fuel-free structural decider, plus soundness
(via the existing `theoremB`) and completeness (`Definitions/TypeChecker/Completeness.agda`,
mirroring `Safety/Head.agda`'s `td/head`) — so the public `typecheck`/`typecheckSession` still
return genuine `Dec`s of the declarative judgment, with identical types. All of
`Tests/Perf01–09` now check in ~5–6s each (≈5s of that is interface loading), including the
formerly-hanging Perf06/07 and `Examples/CounterExamples.agda`. See CLAUDE.md §"Decidability
layer" for the architecture and the two structural findings made along the way
(spine-revisiting skip trees — `Tests/Perf09_RevisitSpine.agda` — and the exponential fuel
recursion).

Also fixed here: `CounterExamples.agda`'s original graph made participant `C` *unprojectable*
(one branch ended without ever messaging `C`, so no `C`-process is typeable — `C ∈T s0` kills
`∅` and the receive dies in the silent branch); its "good process" sanity check was wrong and
the old checker never terminated on it, so this went unnoticed. The graph now forwards to `C`
in both branches (with distinct labels — bisimilar-duplicate states would break `Stepback`).

## Syntax deltas from `main` (apply uniformly to every example)

- **Single-sort messages.** `main`'s `Choice` carried a `Vec Sort (suc I)` (so one
  message could carry several values at once, e.g. OAuth2's `s/nat ∷ s/nat ∷ []`).
  Here `Definitions.Actions.Choice` carries exactly one `Sort` per edge, matching
  `Proc`'s `_!_<_>∙_ : Part → {I} → Fin (suc I) → Exp γ → Proc γ δ → Proc γ δ` (one
  `Exp`). Any old example whose messages carried more than one value needs those
  values either dropped to the one that's semantically relevant, or split into two
  sequential single-value sends. Concretely this affects OAuth2 (2-nat/nat-bool
  payloads → single nat/bool), RecMW/Rec2Buy's `s/a-b = s/nat ∷ s/unit ∷ []`-style
  vectors, similarly.
- **Branch count is per-edge, not `Vec Sort`-driven.** A graph branch point is
  `choice (α₀ ⇒ K₀) (α₁ ⇒ K₁ ∷ … ∷ [])`, one `Alternative` per label, each carrying
  its own single `Sort`. A non-branching step is just `_∙_` (`α ∙ K`, sugar for
  `choice (α ⇒ K) []`). Silent (`ifp`) branches need **no** graph `choice` (there is
  no label/`Choice` to distinguish — `t/if` just needs both `Proc` branches to type at
  the *same* target behavior); the case needing a real `choice` is when a
  participant's own runtime decision determines *which distinct message* it sends
  (e.g. RecMW's `r→m/continue` vs `r→m/stop`, Rec2Buy's `split` vs `cancel`). **But**
  "both branches reach the same target" is *not* automatically trivial to arrange via
  the `OpenGraph` combinators themselves, once the two branches' paths reconverge from
  genuinely different edges — see "Major finding" below; it only stays trivial when
  one branch is a straight-line prefix of a shared continuation (as in `NoSynGT`'s
  `p/A`, where both `ifp` arms bottom out at the *same* `choice`-alternative
  structure, not two separately-authored copies).
- **`I` is implicit in `_!_<_>∙_`.** `B ! 0 , zero < e > ∙ Pr` (old, explicit index)
  becomes `B ! zero < e > ∙ Pr` (new; `I` inferred). `Σ P ？[ sorts ]· branches` is
  unchanged in shape.
- **No manual `BTheory`, `BT-Prop`, `BT-Extra`, `must-skip`, `Causal?`, `Active?`.**
  All deleted outright; `buildG`/`wellBehaved?`/`typecheck` replace every use.
- **No `Global`/`>>`/`μ` (global-type syntax).** Replaced by `OpenGraph`/`end`/`var`/`μ`
  (same recursion-binder shape: `LTS.Algebra`'s `μ : OpenGraph (suc δ) → OpenGraph δ`,
  `var : Fin δ → OpenGraph δ` mirror the old `Global`'s `μ`/`var` almost exactly).
- **`SimpleGT.agda` has no counterpart.** It was pure infrastructure (`tt/end`,
  `tt/rec`, `tt/var`, `t/recvhd` shortcut lemmas for hand-written derivations) — dead
  weight once `typecheck` exists.

## Per-example plan (ordered simplest → most complex; this is the iteration order for
## sub-task 2)

Each entry: participants, states/shape, protocol sketch (informal — see syntax deltas
above for exact combinator names), processes, and porting notes. "Old proof burden"
notes roughly how much manual derivation this example needed on `main`, to make
concrete how much the decision procedure is expected to delete.

### 1. `SendRecv.agda` — 2 participants (A, B)
Old proof burden: ~10 lines/derivation, 3 variants.
- **NR**: `A --bool--> B, end`. `p/A = B ! e ∙ ∅`, `p/B = Σ A ？[bool]· (∅ ∷ [])`.
- **Rec**: `μ (A --bool--> var 0)`. `p/A = rec (B ! e ∙ v 0)`,
  `p/B = rec (Σ A ？[bool]· (v 0 ∷ []))`.
- **Rec′**: same graph, but A's process unfolds the loop once before recursing
  (`p/A = B ! e ∙ rec (B ! e ∙ v 0)`) — exercises `t/unskip`/bisimilarity-up-to-`~`
  implicitly (old proof needed `t/bisim (~sym ~unfold)`; decision procedure needs
  nothing extra since `typecheck` doesn't care how the derivation looks).
- Session: `M = p/A ∷ p/B ∷ []`.

### 2. `PingPong.agda` — 2 participants (A, B)
Old proof burden: similar to SendRecv, 2 variants (NR, Rec).
- **NR**: `A --bool--> B --nat--> A, end`. `p/A` sends then receives; `p/B` receives
  then sends.
- **Rec**: `μ (A --bool--> (B --nat--> var 0))`. Same shape with `rec`/`v`.

### 3. `NoSynGT.agda` — 3 participants (A, B, C), 4 states, non-recursive
Old proof burden: small hand-rolled `BTheory` (diamond/cond-comm cases), but process
derivations are short.
- Graph: from `s0`, two edges out, **no shared choice label** — `A→B` and `A→C` are
  simply two independent `_∙_`-reachable continuations from the same state (both
  present as edges at `s0`; not a `choice` since B and C don't need to distinguish a
  label — it's the same idea as RoundRobin's fan-out, just non-recursive and smaller).
  Concretely: `s0` has edges `A→B` (to `s1`) and `A→C` (to `s2`); `s1` has `A→C` (to
  `s3`); `s2` has `A→B` (to `s3`); `s3 = end`.
- `p/A = ifp cond then (B!e ∙ C!e ∙ ∅) else (C!e ∙ B!e ∙ ∅)` — the whole point of this
  example is that **both branches must type against the same graph region** despite
  sending in different orders; this is exactly what the independence/diamond
  reasoning in `WellBehaved`/`checkWithFuelD` is for. Good smoke test that the
  decision procedure's skip/diamond handling still does its job without a bespoke
  `BT-Prop`.
- `p/B = Σ A ？[unit]· (∅ ∷ [])`, `p/C` symmetric.

### 4. `CounterExamples.agda` — 3 participants (A, B, C), branching, non-recursive
Old proof burden: full manual refutations (~10 lines each) that 3 specific processes
are **ill-typed**.
- Graph: `A --choice(bool: end | B--choice-bool-->C--bool-->end)-->B`, i.e. `A` sends
  a labelled choice to `B`; label 0 ends immediately, label 1 continues with a
  `B→C` step. (`choice` with 2 alternatives from `A`'s perspective; the state after
  label 1 has a further `B→C` edge.)
- Three deliberately-wrong `C` processes to check `typecheck` returns **`no`** for:
  `p/C2` (double-receives from `B` without justification), `p/C3` (receives from `A`
  instead of `B`), `p/C4` (`rec (v 0)` — an unproductive loop, `MessageGuarded`
  violation). Port these as `Dec`-returning `typecheck` calls and pattern-match the
  `no` branch (no need to reconstruct the old manual refutation proofs — that's
  exactly what `typecheck`'s completeness buys us). Keep as a regression check that
  the checker rejects what it should.

### 5. `RoundRobin.agda` — 3 participants (A, B, C), needs skip/diamond reasoning
Old proof burden: **by far the worst** on `main` — two full `must-skip` instances
(`MS1`, `MS2`), each a multi-page case-bashed proof object, purely to justify that `A`
(after sending to `B`) can skip over the intervening `B→C` step before receiving from
`C`. This is the single best demonstration case for this whole rebuild: the decision
procedure should discharge in one `typecheck` call what took ~150 lines by hand.
- **NR** (the only variant `main` finished): `A --bool--> B --bool--> C --bool--> A,
  end` (cyclic fan-out, not recursive — ends after one round).
- `p/A = B!e ∙ Σ C ？[bool]· (∅ ∷ [])`, `p/B = Σ A ？[bool]· (C!e ∙ ∅ ∷ [])`,
  `p/C = Σ B ？[bool]· (A!e ∙ ∅ ∷ [])`.
- **Bonus**: `main` has a **commented-out, incomplete** `Recursive` variant (`μ (A→B→
  C→ var 0)`, only `p/A` sketched, no proof attempted — presumably because the manual
  `must-skip` burden was too high to bother). This is a good opportunity to finish
  what `main` gave up on, now that it costs nothing extra.

### 6. `OAuth2.agda` — 3 participants (S, C, A), 5 states, branching, non-recursive
Old proof burden: full custom `BTheory` + properties (~150 lines) + per-participant
`dt/skip`/`Causal?`/`Active?` proofs for `A`.
- Graph (after collapsing 2-value payloads to 1, see syntax deltas): `S` picks
  `login`/`cancel` to `C` (2-way `choice`); `login` branch continues `C→A→S`
  (`passwd` then `auth`, both single edges) to `end`; `cancel` branch continues `C→A`
  (`quit`) to the **same `end`** as the login branch (both paths converge — `main`'s
  `s3` is a shared terminal state for both branches, which is easy to arrange in
  `OpenGraph` by pointing both continuations at the same sub-term).
- `p/S`, `p/C`, `p/A` per the original — `p/A` is the interesting one (`main` needed
  `dt/skip` to justify `A` skipping the `S→C` step before its own `C→A` receive);
  should now just fall out of `typecheck`.

### 7. `Rec2Buy.agda` — 3 participants (A, B, S), 7 states, recursive + branching
Old proof burden: full custom `BTheory` (~150 lines) + several `Causal?`/`Active?`
lemmas for `S` and `B`'s skip reasoning.
- Graph: `A→S` (item) → `S→A` (price) → loop point: `A` picks `cancel` (→`B`→`S`, end)
  or `split` (→`B`, then `B` picks `no` (loop back to the price-branch point) or `yes`
  (→`A`→`S` buy, end)). The recursion is on the `split`/`no` cycle (`A` and `B` both
  loop). Use `μ` at the shared A/B loop point (two-sided recursion, mirroring `main`'s
  loop over `s2`/`s4`).
- Processes: `p/A` (`rec` over the split/cancel choice), `p/B` (`rec` over yes/no),
  `p/S` (straight-line: recv item, send price, recv final outcome).

### 8. `RecMW.agda` — 4 participants (M, R, W1, W2), 9 states, recursive
Old proof burden: full custom `BTheory` (~200 lines) + **7** separate `Causal?`/
`Active?` skip-justification pairs (`C1a0R/A1a0`, `C2/A2`, `C3/A3`, `C4/A4`, `C5/U5`,
`C6/A6`, `C7/A7`) — the densest example on `main`.
- Graph: `M` sends `datum` to `W1` then `W2` (independent, interleavable — this is
  where the diamond property matters); `W1`, `W2` each send `result` to `R`
  (independent again); `R` picks `continue` (loop back to `M`'s start, `μ`) or `stop`
  (→ `M` sends `stop` to `W1` then `W2`, end).
- Processes: `p/M` (`rec`, two sends then a branching recv), `p/R` (`rec`, two recvs
  then an `ifp`-driven send-choice), `p/W` (shared shape for `W1`/`W2`: recv datum,
  `rec` over send-result/recv-next-or-stop).

### 9. `IndepW.agda` — 7 participants (S, A1, B1, C1, A2, B2, C2), 7 states
Old proof burden: **largest** file on `main` (~1040 lines) — two independent
`M→W1→W2→R`-shaped pipelines (`{A1,B1,C1}` and `{A2,B2,C2}` behind a shared `S`) whose
steps interleave arbitrarily; `main` proves per-participant typing only (no assembled
`⊢s`) via ~7 mutually-recursive `Active?`/`Causal?` families per pipeline. This is the
stress test for the independence/diamond machinery at real scale — worth doing last,
once 1–8 have validated the approach, and worth actually assembling the full 7-way
`typecheckSession` this time (which `main` never did).
- Graph: `S` sends `item` to `A1` then `A2` (independent); each `Ai` sends `item` to
  `Bi`, loops; each `Bi` sends `item` to `Ci`, loops; `Ci` just keeps receiving
  (`rec (Σ Bi ？[unit]· (v 0 ∷ []))`, mirrors `main`'s generic `p/C`). Reuse `main`'s
  generic `p/C`/`p/B`/`p/A` process *shapes* (parameterised over which `B`/`A`/`C`
  they talk to) via ordinary Agda functions `Part → Part → Proc 0 0` — ports directly.

## Safety specialization (sub-task 2.5, optional per example)

Once `typecheck`/`typecheckSession` yields a `yes wtd` for an example, `wb-of` gives
the concrete `WellBehaved (graphTheory G)` witness, so `Safety.progress wb-of-G wtd`,
`Safety.preservation …`, `Safety.no-infinite-τ-reductions …` (from
`Definitions.TypeChecker.Complete`'s internals / root `Safety.agda`) all specialize
directly — no new proof needed, just instantiation. Do this opportunistically per
example once the typing derivation is extracted (not for the negative
`CounterExamples` entries, which have no derivation to specialize).

## Suggested execution order

Do 1–2 first (validate the whole `OpenGraph`→`buildG`→`typecheck` pipeline end-to-end
on the simplest possible cases, including a recursive one), then 3–4 (small, exercise
independence and the negative/`no` path), then 5 (the highest-value payoff — biggest
proof-size reduction relative to effort), then 6–8, then 9 last.
