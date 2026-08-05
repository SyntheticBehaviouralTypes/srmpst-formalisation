# DONE — 2026-08-04 — algorithmic judgment + `⊢p → ⊢a` normalisation

> **STATUS: DONE. ARCHIVED. DO NOT WORK FROM THIS FILE.**
>
> Closed 2026-08-04. The live plan is `TODO.md` at the repo root.
>
> **What this plan achieved:**
>
> - `Definitions/Typing/Algorithmic.agda` — the algorithmic judgment `⊢a`,
>   with its leaf family `⊢blocked` (`blocked/send`, `blocked/recv`,
>   `blocked/var`, `blocked/rec`) and soundness `alg/typing : ⊢a → ⊢p`.
>   Hole-free.
> - `Definitions/Typing/Norm.agda` — the normalisation
>   `norm : ⊢p → trace → ⊢a`, including `push` ("push the skip tree
>   forward"). **Hole-free**, checked under `--no-allow-unsolved-metas`,
>   in `runall.sh`'s ROOTS.
>
> **The two findings worth carrying forward** (both proved, §5e below):
>
> 1. `⊢a` with `rec` OUTSIDE the leaf family is INCOMPLETE for `⊢p` —
>    `Stale/PushRecDerivations.agda.stale`, `Ex6`, carries both a `⊢p`
>    derivation and a refutation of the corresponding `⊢a`. Fixed by
>    moving `rec` into the leaves as `blocked/rec`, so each leaf of one
>    skip tree carries its OWN anchor.
> 2. Every "move the anchor" statement is false — `W ~ K`,
>    `unskip-transfer`, `step-commute`, `advance-anchor`, and the span
>    form `W ⇝ L → G ⇝ L → …`. Do not resurrect them.
>
> Everything after this box is the historical record.

## HOW TO RESUME (read this first)

This file is the handoff. If you have no context: read this section, then
"Acceptance criterion", then the numbered step you are on. Everything below
is written to be actionable cold.

**Where we are:** **Step 1 is done** (1a–1e; slice E, `Definitions/Language/`, was left
optional and is still open). Step 2 (design) is decided and Step 3's
**judgment + soundness are written and compiling**
(`Definitions/Typing/Algorithmic.agda`).

**Next: Step 5**, continuing — the normalisation `⊢p → ⊢a` (`norm`, per
Step 2's design) is being written in `Definitions/Typing/Norm.agda`.
**That file is WIP and deliberately NOT in `runall.sh`'s ROOTS** until it
is hole-free; it compiles clean as of now. Everything else stays green, so
the "only `Check/Decide.agda` has holes" invariant still holds for the
build.

**`norm` itself is written and compiles with exactly one hole** — the
`t/skip` clause (`Norm.agda:206`). All seven other clauses are proved, and
they confirm Step 2's design rather than just restating it:

- `t/unskip tr′ td` → `norm td (skip/cat tr′ tr)`. The accumulated unskip
  really is just the trace parameter; no unskip-pushing pass exists.
- `t/var eq` → `skip/bisim-back eq tr` produces *exactly* `act/var`'s two
  premises, as predicted.
- `t/send`/`t/recv` → `skip/advance`/`branch/before` move the action to the
  far end; the continuation inherits the advanced trace; zero-height tree.
- `t/rec` → `a/rec tr guarded (norm td skip/refl)`: trace parked in the
  anchor, body normalised at its own state.
- `t/if` distributes, `t/end` is `skip/∈T-back`.

Remaining: the `t/skip` clause = walk `tr` into the tree
(`cancel/unskip`, needing the `LeafAlg` plumbing) and then dispatch on the
surviving tree — send/recv/var become `a/act`, `∅` and `if` are eliminated
(5b/5c), `rec` is the open one (5e).

Done in `Norm.agda` so far: `LeafAlg` (stated), `ptd/bisim`, `pskip/unfold`,
`pskip/unfold-top` (all just the `Δ`-general instantiations — the
underlying `skip/unfold-cycle` in `Properties.agda` was already `Leaf`- and
`δ`-generic), and the full bisimulation layer for `⊢a`: `alg/bisim`,
`act/bisim`, `act-tree/bisim`, mutually, generalised over `Δ ~ᵛ Δ′` so the
`a/rec` anchor case falls out of the induction instead of needing a
separate lemma. Still to do: `LeafAlg`, the `leafAlg/*` plumbing,
`cancel/unskip`, `mainLeaf/alg`, `norm`. Step 4 (retiring `⊢head`, repairing `Safety/*`) is deliberately
*after* it: `Algorithmic.agda` is additive for now, so the tree stays green
while the hard proof is written.

`bash runall.sh` is green (`Check/Decide.agda` reported as "expected
holes"). Run `agda --guardedness Tests/RecSkipCounterexample.agda`
separately — see 1c for why it is not in `runall`.

Green as of now: `Definitions.agda`, `LTS.agda`, `Safety.agda`,
`Tests/RecSkipCounterexample.agda`.

**End state, non-negotiable: there are AT MOST TWO judgments** —
`Definitions/Typing/Declarative.agda`'s `_&_⊢p_∶_` (paper-style) and
`Definitions/Typing/Algorithmic.agda`'s `_&_⊢a_∶_` (what the checker
decides). The legacy `_⊢head_∶_` **is deleted** at Step 4; it currently
survives only at the bottom of `Algorithmic.agda`, clearly marked, because
`Normalise.agda` and the three `Safety/*` files are still written against
it. If you are reading this and `⊢head` still exists after Step 4, that is
a bug in the execution, not a design choice.

**Invariant to preserve at all times:** `Check/Decide.agda` (was
`Definitions/TypeChecker/Check.agda`) is the *only* file allowed to have
holes. It currently has 4:

- `791` — `permute-tree`'s `skip/main`: needs `s -[¬ P ]->* s′` (§4).
- `851`, `854`, `855` — `tcGraph`'s `v x`, send, recv clauses.

Check with `agda --guardedness Check/Decide.agda`; the only
output should be "Unsolved interaction metas" at those four positions.

**Working discipline:** every increment ends compiler-green, and this file
is updated *in the same turn* as the change it describes — check the box,
and record anything learnt under the step. Never leave a step half-applied
without a note saying so.


Scope: `Definitions/TypeChecker/Check.agda`'s top-level decision function

```agda
tcGraph : ∀ Γ Δ P Pr s → Dec (Γ & Δ ⊢p P ◂ Pr ∶ s)
```

## 0. The observation (2026-08-03) — decide an *algorithmic* derivation

Deciding `_&_⊢p_∶_` directly keeps running into the same wall: `t/skip` and
`t/unskip` may wrap *any* process, so every clause has to re-solve "could
this have been derived by walking the graph instead?". The way out is to
decide a **normalised** judgment instead, and transport across it:

- **`t/unskip` can always be pushed inward**, until it hits a `t/rec`, a
  `v X`, or a `t/skip`. Past `t/send`/`t/recv` it is absorbed by
  `skip/advance`/`branch/before` (the action survives the trace, and the
  continuation inherits the advanced trace); past `t/if` it distributes;
  in front of `∅` it is absorbed by `skip/∈T-back`.
- **A body under `rec` is `MessageGuarded`**, so its head is a
  communication — never a `rec` or a `v`. Hence in a normalised derivation
  of a guarded body no `t/unskip` survives at all: the only irreducible
  positions (`rec`, `var`) cannot occur at the head of a guarded process.
- Therefore the normal form merges the two skip/unskip forms into the rules
  they cannot pass:
  - **`h/send`/`h/recv` absorb `h/skip`**: each carries a skip derivation
    whose leaves are the direct action rules. Zero height is allowed, so
    today's `h/send`/`h/recv` are the leaf case. `h/skip` disappears as a
    standalone constructor.
  - **`h/rec`/`h/var` carry an unskip trace** — the two positions where a
    `t/unskip` cannot be pushed further in.
  - **`h/var` also absorbs `h/skip`** — see the counterexample below.

### The judgment (proposed shapes)

```agda
  mutual
    data _&_⊢head_∶_ {γ δ} (Γ : Vec Sort γ) (Δ : Vec Behav δ)
       : NProc γ δ → Behav → Set where
      h/act : ∀ {PPr G} → (Γ & Δ ⊢act_∶_) & [] ⊢skip PPr ∶ G
            → Γ & Δ ⊢head PPr ∶ G
      h/var : ∀ {P G} {X : Fin δ} → (Δ ⊢var_∶_) & [] ⊢skip P ◂ v X ∶ G
            → Γ & Δ ⊢head P ◂ v X ∶ G
      h/if  : Γ ⊢e E ∶ s/bool → Γ & Δ ⊢head P ◂ Pr ∶ G → Γ & Δ ⊢head P ◂ Pr′ ∶ G
            → Γ & Δ ⊢head P ◂ ifp E then Pr else Pr′ ∶ G
      h/rec : G -[¬ P ]->* G′ → MessageGuarded Pr → Γ & (G ∷ Δ) ⊢head P ◂ Pr ∶ G
            → Γ & Δ ⊢head P ◂ rec Pr ∶ G′
      h/end : ¬ P ∈T G → Γ & Δ ⊢head P ◂ ∅ ∶ G

    -- skip-blocked leaf: the action is available *here*
    data _&_⊢act_∶_ Γ Δ : NProc γ δ → Behav → Set where
      a/send : G -< P ⟶ Q # i < S > >-> G′ → Γ ⊢e E ∶ S
             → Γ & Δ ⊢head P ◂ Pr ∶ G′
             → Γ & Δ ⊢act P ◂ Q ! i < E >∙ Pr ∶ G
      a/recv : G -< Q ⟶ P # i < T > >-> G′
             → (∀ {j U G″} → G -< Q ⟶ P # j < U > >-> G″
                 → (U ∷ Γ) & Δ ⊢head P ◂ lu Br j ∶ G″)
             → Γ & Δ ⊢act P ◂ Σ Q ？[ S ]· Br ∶ G

    -- unskip-blocked leaf: the anchor reaches (up to `~`) the current state
    data _⊢var_∶_ {γ δ} (Δ : Vec Behav δ) : NProc γ δ → Behav → Set where
      a/var : ∀ {P G H} {X : Fin δ}
            → lu Δ X -[¬ P ]->* H → H ~ G → Δ ⊢var P ◂ v X ∶ G
```

Notes on the shapes:

- **`a/var` is oriented `reach`-then-`~`,** not `~`-then-`reach`. Both are
  derivable from `t/unskip tr (t/var eq)` via `skip/bisim-back`, but only
  this one has the *known* state on the left, so the leaf is decided by one
  `reachVia?` fixed point from `lu Δ X` followed by `bisim?~ _ G` (§2).
- **Zero height is `skip/main`** — `h/act (skip/main (a/send …))` is
  today's `h/send`. Splitting `h/act` into `h/send`/`h/recv` is cosmetic:
  a tree preserves its process, so a send-process tree can only have send
  leaves.
- **Positivity is not a risk.** Self-reference through `⊢skip`'s `Leaf`
  parameter is exactly what today's `h/skip` already does.
- **`skip/cycle` survives into these trees** — a branch that loops without
  reaching the action/anchor, with `P ∈T` holding. That is the existing
  vacuous-cycle behaviour of `⊢skip`, inherited, not introduced here.
  Decide once whether the *decision* procedure treats such a branch as a
  success (it is a valid derivation today).

**`t/skip` in front of `t/var` is essential** (machine-checked,
`scratchpad/SkipBeforeVar.agda`): in the well-behaved graph
`s --β--> K --β--> ended` with `β = B ⟶ C` (so `A` never active) and
`Δ = K ∷ []`, `v zero` types at `s` as `t/skip (skip/step …)` with leaf
`t/var ~refl` at `K`, while `¬ (∃[ H ] (K ~ H) × (H -[¬ A]->* s))` — nothing
reaches `s`, so no trace-only `h/var` exists. Hence the blockers are
asymmetric: `t/unskip` is blocked by `rec`/`var`; `t/skip` is blocked by
`send`/`recv`/`var`.

This is `Safety/Head.agda`'s `⊢head` generalised: it already keeps the trace
exactly where it is irreducible (`h/rec tr guarded td`), and has no `v` case
only because it is used at `δ = 0`. Generalising over `δ`, adding `h/var`,
and folding `h/skip` into `h/send`/`h/recv`/`h/var` turns it into the
algorithmic form to decide.

**Superseded by this observation:** the `rec` "no" case as attempted in
`Check.agda` (`leaf-permute`/`permute-tree`, one hole left at
`permute-tree`'s `skip/main`). Keep it compiling until the algorithmic form
lands, but do not invest further in it — §4 records exactly which part of
it survives the move.

**`⊢head` is edited in place**, and `Safety/*` repaired to match. Not a new
parallel judgment: one algorithmic form, recovered everywhere, even though the
repair is more work up front. `Definitions/Behav.agda` and
`Typing/Substitution.agda` stay untouched.

## Step-by-step plan

- [x] **Trimmed `Core.agda`.** Old semantic-characterization machinery
      (`SemSkipP`/`SkipDecide`/`SkipSem`) deleted.
- [x] **`tcGraph`'s `∅` case.** `find-leaf/remember`, `find-leaf`,
      `end-refute-td/accessible`, `end-refute-td`. Clean, no holes (§1).
- [x] **`rec` "yes" side.** Direct, anchor = `s`.
- [x] **`rec` "no" side, backward worklist.** `step-predecessors`,
      `Covers`/`Covers-from-closed`, `DirectCovered`(+`-seed`/`-true`/
      `-false`), `Table`, `rec-unskip`. Clean; the *refutation* it calls is
      down to a single hole (§4).
- [x] **Step 1 — restructure and triage (mechanical; ends green).** Do
      this before any semantic change: renames are compiler-verified, and
      interleaving them with the `⊢head` surgery makes both unreviewable.
      Target layout:

      ```
      Definitions/
        Language/{Common,Expr,Actions,Proc,Guard}.agda   -- syntax only
        Behav.agda                                       -- BTheory, WellBehaved, ~, skip traces
        Typing/
          Declarative.agda   -- paper-style ⊢p / ⊢skip        (from Definitions/Typing.agda)
          Properties.agda    -- td/bisim, skip/unfold-cycle    (from Safety/Skip.agda)
          Algorithmic.agda     -- ⊢head / ⊢act / ⊢var + head/typing
          Normalise.agda     -- td/head, cancel/unskip, LeafHead (from Safety/Head.agda)
          Substitution.agda                                (from Typing/Substitution.agda)
        Graph/{Core,Action,Algebra,Bisimulation,Reachability,WellBehaved,Decision}.agda
                                                          (from LTS/)
      Safety/{Preservation,Progress,Termination}.agda
      Check/{Core,Decide}.agda                            (from Definitions/TypeChecker/)
      Utils/  Tests/  Examples/
      ```

      Rationale: `Typing/Substitution.agda` and `LTS/` stop being top-level
      siblings of the thing they belong to; the paper-style judgment and
      the algorithmic one become *files*, not conventions; and
      `Safety/Skip.agda`/`Safety/Head.agda` move next to the judgment they
      are about — neither is safety metatheory, both are typing lemmas that
      `Preservation`/`Progress`/`Termination` merely consume. Roots for
      `runall.sh` become `Definitions.agda`, `Safety.agda`, `Check.agda`.
      Grouping the syntax files under `Language/` is the one optional part;
      skip it if the churn is not worth it.

      Sub-steps, each ending compiler-green:
  - [x] **1a. Triage the dead modules.** *(done — 7 files deleted via
        `git rm`, `Definitions.agda` unhooked from the old checker. All
        roots green afterwards, including `Definitions.agda`, which was red
        before this step. Recover any file with
        `git checkout HEAD -- <path>`.)*

        Deleted: `Definitions/TypeChecker/{Restricted,Complete,
        Completeness}.agda`, `Definitions/TypeChecker.agda`,
        `Definitions/Types.agda`, `Tests/Perf08_Restricted.agda`.

        **`TypeChecker/Network.agda` was deleted here and then restored**
        (nothing had been committed, so `git checkout HEAD -- <path>` got
        it back verbatim). It now lives at `Check/Network.agda` (module
        `Check.Network`) and **compiles**: its substance — `WBNet`,
        `netWB`, `wb-net`, the compositional well-behavedness certificate
        for networks — never depended on the deleted checker. Only the two
        API wrappers `typecheckNet`/`typecheckSessionNet` did; they are
        commented out in place, with the recovery command for the deleted
        `Completeness` in the file header. **Restoring them is a Step 7
        deliverable** (they become one-liners over the new `Check.Decide`
        API). The four LTS-level `Network*` modules were never deleted and
        are now `Definitions/Graph/Network*.agda`.
        Removed from `Definitions.agda`: `open import
        Definitions.TypeChecker public`.

        Measured, not guessed (all suspects are **tracked by git**, so every
        deletion is recoverable with `git checkout -- <path>`):

        | module | compiles? | imported by | verdict |
        |---|---|---|---|
        | `TypeChecker/Core.agda` | OK | `Check.agda` | **LIVE — keep** |
        | `TypeChecker/Restricted.agda` | FAILS (`SemSkipP`) | `Completeness`, `Tests/Perf08` | delete |
        | `TypeChecker/Complete.agda` | FAILS | `TypeChecker.agda`, `Completeness`, `Network` | delete |
        | `TypeChecker/Completeness.agda` | FAILS | `TypeChecker.agda`, `Network` | delete |
        | `TypeChecker/Network.agda` | FAILS (via `Completeness`) | `Examples/IndepW`, `TypeChecker.agda` | delete |
        | `TypeChecker.agda` | FAILS | `Definitions.agda`, all `Tests/Perf*`, all `Examples/*` | delete; drop its line from `Definitions.agda` |
        | `Definitions/Types.agda` | FAILS | nobody | delete |
        | `LTS/Network*.agda` (4) | **OK** | each other, `Examples/IndepW` | **keep** — LTS-level, independent of the checker |
        | `Tests/Perf08_Restricted.agda` | FAILS | — | delete: it tests the deleted restricted judgment |

        `LTS/Decision.agda`'s mention of `TypeChecker/Core` is a *comment*,
        not an import — no dependency there.

        **Consequence for the acceptance criterion:** `Tests/Perf*` (9) and
        `Examples/*` (9) all go through `Definitions.TypeChecker`, i.e. the
        *old* checker, and are already red today. They cannot be green
        again until Step 7 wires the new one in. They are **quarantined**,
        not deleted — do not try to fix them before Step 7.
        `Tests/RecSkipCounterexample.agda` does not use the checker and
        must stay green throughout. `Definitions.agda` does **not**
        compile today: it re-exports `Definitions.TypeChecker`, which pulls
        in `Restricted.agda`/`Complete.agda`/`Completeness.agda`, all still
        referencing the deleted `SemSkipP`. Also orphaned (not re-exported
        by any root): `LTS/Network*.agda`, `Definitions/TypeChecker/
        Network.agda`, `Definitions/Types.agda`. Delete or repair each,
        explicitly. `Definitions/TypeChecker/Core.agda` is **live** —
        `Check.agda` imports it.
  - [x] **1b. Move files, fix module headers and imports.** *(slices
        A–D done; slice E deferred — it is optional and does not block.)*
        Purely
        mechanical; the compiler finds every miss. `./clean.sh` first —
        stale `.agdai` files under old paths will otherwise mask errors.
        Done in slices, each ending green:
    - [x] **A.** `Typing/Substitution.agda` → `Definitions/Typing/
          Substitution.agda` (module `Definitions.Typing.Substitution`).
          `Typing/` removed.
    - [x] **B.** `Definitions/TypeChecker/` → `Check/`:
          `Core.agda` → `Check/Core.agda` (module `Check.Core`),
          `Check.agda` → **`Check/Decide.agda`** (module `Check.Decide`).
          *Naming change vs. the layout below: `Check/Check.agda` would
          give the module `Check.Check`; `Decide` reads better and keeps
          the directory name meaningful.* `Definitions/TypeChecker/`
          removed. Note `Check.agda` was untracked, so `git mv` failed on
          it and a plain `mv` was used — it is still untracked.
    - [x] **C.** `LTS/` → `Definitions/Graph/` — all 11 modules (incl. the
          4 `Network*`) plus `LTS.agda` → `Definitions/Graph.agda` (module
          `Definitions.Graph`, still parameterised by `N`). 32 files
          patched. The bare `LTS` aggregator was renamed only in `module`
          headers and `import` lines, by regex, so prose comments saying
          "the LTS" were left alone.
    - [x] **D.** `Safety/Skip.agda` → `Definitions/Typing/Properties.agda`,
          `Safety/Head.agda` → `Definitions/Typing/Normalise.agda`.
          `Safety.agda` now re-exports `Definitions.Typing.Normalise` in
          place of `Safety.Head`, so its public surface is unchanged;
          prune that line later if `Safety` should not re-export typing
          lemmas at all.
    - [ ] **E.** *(DEFERRED — optional, does not block anything)* syntax
          files → `Definitions/Language/`. Pure churn for clarity; pick it
          up whenever, or drop it.
  - [x] **1d. Split `Definitions/Typing.agda`** into
        `Definitions/Typing/Declarative.agda` (module
        `Definitions.Typing.Declarative`, the paper-style judgment) plus a
        thin `Definitions/Typing.agda` that re-exports it. Every existing
        `open import Definitions.Typing` keeps working unchanged, so
        `Algorithmic.agda` can be added beside `Declarative.agda` in Step 3
        without touching importers.
  - [x] **1c. Update `runall.sh`'s roots.** *(done)* It now uses an
        explicit `ROOTS` array — `Definitions.agda`,
        `Definitions/Graph.agda`, `Safety.agda`, `Check/Decide.agda` —
        instead of a top-level `*.agda` glob, since `Definitions/Graph.agda`
        is no longer at top level. Two behaviours worth knowing:

        - `Check/Decide.agda` is expected to be holed, and Agda exits
          non-zero for unsolved interaction metas even without
          `--no-allow-unsolved-metas` (the stdlib is `--safe`, so
          `--allow-unsolved-metas` cannot be passed globally). `runall.sh`
          therefore treats "exit non-zero **and** output contains
          `Unsolved interaction metas`" as expected *for that file only*,
          and only when `--CheckClosedProof` is absent. Agda reaches that
          report only when there is no hard error, so it is a reliable
          signal.
        - **`runall.sh` is now incremental by default.** It no longer
          deletes `*.agdai` unless `--clean` is passed. Use the default
          while iterating; use `--clean` (optionally with
          `--CheckClosedProof`) at the end of a piece of work.
        - **`Tests/RecSkipCounterexample.agda` is opt-in via `--tests`**,
          never in the default run. A
          from-scratch build peaks at **~29 GB resident** / ~3.5 min, which
          OOM-kills the run on a 30 GB machine.
          *Open oddity (2026-08-03):* it appears to cost ~28 GB / ~3:45
          **even with dependencies cached**, and no `.agdai` seems to be
          produced for it, so it may be re-checking its whole dependency
          cone every time. Diagnosis was still running when this was
          written — if it is confirmed, the fix is to find why the
          interface is not written (options mismatch? `--guardedness` on
          the CLI vs. the pragma?) rather than to keep excluding it.
  - [x] **1e. Refresh `CLAUDE.md`.** *(done)* Build section rewritten for
        the incremental `runall.sh` and the two gotchas; a directory-layout
        block added to "Architecture"; §2/§3 headers repointed; the stale
        "Decidability layer" section replaced by a short `Check/` section
        that defers to this file; "In-flight work" now names `TODO.md` as
        the authority. Original text of the deleted paragraphs is in git.
        *(was:)* Its architecture section and every
        path reference in it are stale after 1b — it still describes
        `Definitions/TypeChecker/{Core,Restricted,Complete,Completeness}`
        and the fuel-free restricted judgment, all deleted in 1a.
- [x] **Step 2 — the normalisation order and its metric (design).**
      *Outcome: **one pass**, not two.* Worked through clause by clause
      against `Definitions/Typing/Declarative.agda`:

      ```agda
      norm : Γ & Δ ⊢p P ◂ Pr ∶ G → G -[¬ P ]->* G′ → Γ & Δ ⊢head P ◂ Pr ∶ G′
      ```

      the trace parameter *being* the accumulated unskip, exactly as
      `td/head` already works. Per clause:

      - `t/unskip tr′ td` → recurse with `skip/cat tr′ tr`. The unskip is
        absorbed into the parameter; it never needs a separate phase.
      - `t/send`/`t/recv` → `skip/advance`/`branch/before` move the action
        to `G′`; emit `h/act (skip/main (a/send …))`, a zero-height tree.
      - `t/if` → distribute; `t/end` → `skip/∈T-back`.
      - `t/rec mg body` → `h/rec tr mg (norm body skip/refl)`; the trace is
        parked, the body normalised at `δ+1`.
      - `t/var eq` → `h/var (skip/main (a/var …))`: from `lu Δ X ~ G` and
        `G ⇝ G′`, `skip/bisim-back` gives `lu Δ X ⇝ H` with `H ~ G′` —
        precisely `a/var`'s premises.
      - `t/skip std` → walk the trace into the tree (`cancel/unskip`). If a
        leaf is reached first, recurse on it with the remaining trace. If
        the trace runs out first, the surviving tree becomes the tree of
        `h/act`/`h/var`, its leaves normalised into `⊢act`/`⊢var` leaves.

      **The one new obligation this exposes: `graft`.** A surviving leaf may
      itself be `t/skip`-headed, so normalising it yields *another* tree
      where a leaf is wanted — a tree of trees, which must flatten to a
      tree (with the inner `Ξ`s re-based). This is not hypothetical: the
      deleted `Completeness.agda` had exactly this under the name
      `flatten` ("absorbs the leaves' own skip rounds"). Recover it for
      reference with
      `git show HEAD:Definitions/TypeChecker/Completeness.agda`.

      **Measures.** `norm` recurses structurally on the derivation, with the
      trace as a plain parameter (today's `td/head` discipline — do not
      re-pack the trace into a tuple at the recursive call, or the checker
      loses it). The tree walk is *not* structural, because `skip/cycle`
      unfolding substitutes a subtree; carry `LeafHead`-style **properties**
      rather than trees, as `Definitions/Typing/Normalise.agda` already
      does. `(size Pr, size G ∸ ξ)` (§3) is the fallback if that fails.

      **Why not the two-phase version** (push unskips, then push skips):
      it needs an intermediate judgment for the half-normalised form, and
      the `t/unskip` clause above shows the unskip never needs its own
      pass — it is already just the trace parameter. Revisit only if the
      single pass gets stuck.
- [x] **Step 3 — the algorithmic judgment.** *(done —
      `Definitions/Typing/Algorithmic.agda`, compiles clean, in `ROOTS`.)*

      Delivered: `_&_⊢a_∶_` with `a/act`/`a/if`/`a/rec`/`a/end`, the leaf
      family `_&_⊢act_∶_` with `act/send`/`act/recv`/`act/var`, and
      soundness `alg/typing : ⊢a → ⊢p` (mutually with `act/skip`, which
      maps a leaf-tree to a `⊢p`-tree exactly as `hskip/typing` does).

      Two decisions taken while writing it:

      - **`var` is an action.** There is no separate variable judgment:
        jumping back to a recursion point is a step the process takes, and
        it is blocked by `t/skip` for the same reason a send is, so it is
        `act/var` inside the one leaf family. Besides being simpler, this
        is what makes `γ` inferable — a variable family indexed only by
        `Δ` leaves `γ` un-pinned and Agda gets stuck unifying the
        `NProc γ δ` index.
      - **Additive for now.** `Declarative.agda`'s `⊢head` is untouched and
        `Safety/*` still uses it, so every step stays green. Retiring
        `⊢head` is Step 4, *after* the normalisation exists — not before.

      `Tests/SkipBeforeVar.agda` (the machine-checked counterexample
      forcing `act/var` to carry a tree, not just a trace) moved out of the
      scratchpad into `Tests/`, and is in `TEST_ROOTS`.

      *(superseded plan text:)* `⊢head` generalised over `δ`, edited in place.
      `Definitions/Typing.agda`: `_⊢head_∶_` → `_&_⊢head_∶_` carrying `Δ`;
      `h/rec`'s body at `G ∷ Δ`; `h/skip` deleted and folded into
      `h/send`/`h/recv` (each carrying a possibly-zero-height skip
      derivation over the direct action rule); new `h/var` carrying both a
      skip derivation and, at its leaves, the trace + `~`. Deliverable: the
      datatype and `head/typing` compile.
- [ ] **Step 4 — DELETE `⊢head`; migrate `Normalise.agda` + `Safety/*` to
      `_&_⊢a_∶_`.** *(scheduled after Step 5: it needs `norm` to exist.)*

      The end state is two judgments and no more. Concretely: delete the
      LEGACY block at the bottom of `Definitions/Typing/Algorithmic.agda`
      (`_⊢head_∶_`, `_&_⊢hskip_∶_`, `head/typing`, `hskip/typing`), drop the
      `open Alg wb using (…)` lines from the four consumers, and rewrite
      them against `_&_⊢a_∶_`.

      **This is not a rename.** Measured: `h/skip` is pattern-matched
      **32 times** across those four files (Preservation 12, Normalise 11,
      Progress 7, Termination 2), because `⊢head` keeps the skip tree
      *beside* the action while `a/act` folds it *into* the action. Every
      such case analysis has to change shape: where a proof matched
      `h/send gr etd td` it must now walk a `⊢skip` tree whose leaves are
      `act/send`. Budget for that, and expect `Safety/*` to be red while it
      is in progress — that is the one sanctioned exception to the
      "always green" rule, and it should be a single focused pass.
- [ ] **Step 5 — completeness `⊢p → ⊢head` (the generalised `td/head`).**
      Split, in this order:
  - [~] **5a. Δ-generic `cancel/unskip` + `LeafHead`.** *(in progress —
        bisimulation layer done, see the header.)* Two things learnt:
        `skip-leaf/bisim` **cannot** be reused when `Δ` moves (it fixes one
        `Leaf`, and the leaf family mentions `Δ`), hence the local
        `act-tree/bisim` — same proof, one more index. And
        `skip/bisim-back` was sitting in `Normalise.agda` for no reason
        (it mentions neither `⊢head` nor `⊢p`); it now lives in
        `Properties.agda`. The bulk. Port
        `Safety/Head.agda:486–535`'s machinery (`cancel/unskip-aux`,
        `LeafHead`, `leafHead/unfold`, `pskip/unfold-top`) from
        `Leaf = ⊢head` at `δ = 0` to the `δ`-general one. `skip/unfold-cycle` in
        `Safety/Skip.agda` is already Leaf-generic — reuse, do not
        reinvent. Independent of Step 2; can start after Step 1.
  - [ ] **5b. Skip-in-front-of-`∅` elimination.** The argument already
        exists twice (`end-refute-td` in `Check.agda`, `leaf-from-∈T` in
        `Head.agda`): a tree's `na` forces `P` inactive at every node, so a
        `P ∈T` witness must land on a `skip/main` leaf.
  - [ ] **5c. Skip-in-front-of-`if` elimination.** Port `head/if/split`
        (`Safety/Head.agda:629`) to arbitrary `Δ`.
  - [ ] **5d. Skip-in-front-of-`var`.** Nothing to prove: `h/var` carries
        the tree (the counterexample in §0 shows it must). The clause just
        rebuilds it with `t/var`-shaped leaves.
  - [x] **5e. Skip-in-front-of-`rec`. SOLVED 2026-08-04 by moving `rec`
        INTO the leaf family.** Everything below the "── SOLVED ──" rule
        is the historical record of how it was solved and what was
        refuted along the way; read this box first.

        ── SOLVED ────────────────────────────────────────────────────

        `⊢a`'s leaf family was renamed and `rec` moved inside it:

            _&_⊢act_∶_ → _&_⊢blocked_∶_    a/act → a/skip
            act/send → blocked/send        act/recv → blocked/recv
            act/var  → blocked/var
            a/rec    → blocked/rec         (moved INSIDE the leaves)

            blocked/rec : W -[¬ P ]->* L → MessageGuarded Pr
                        → Γ & (W ∷ Δ) ⊢a P ◂ Pr ∶ W
                        → Γ & Δ ⊢blocked P ◂ rec Pr ∶ L

        A `rec` blocks a skip for the same reason an action does — because
        `t/unskip` does.  Keeping it inside the leaf family is what lets
        the several leaves of ONE skip tree carry DIFFERENT anchors, which
        is exactly what `Ex6` (below) showed is necessary.

        Consequences, all checked (`agda --guardedness`):

        - `push`'s `rec` case collapsed to the same one-liner as the
          actions: `a/skip (agraft (λ { (a/skip t) → t }) std)`.
        - `arec/guard`, `arec/body`, `rec-body`, `reanchor` and
          `advance-anchor` are DELETED — every one of them existed only to
          manufacture a common anchor, and there is no longer one to
          manufacture.
        - `norm`'s `t/rec` clause is now
          `a/skip (skip/main (blocked/rec tr guarded (norm td skip/refl)))`.

        **`Norm.agda` IS HOLE-FREE.**  12 holes → 0, checked under
        `--no-allow-unsolved-metas`, no termination failures.  It is now in
        `runall.sh`'s ROOTS.

        The last four (`aif/exp`, `a∅/notin`) closed by **trace chasing +
        cycle unfolding**, in two phases with two different measures:

        1. **Descend structurally**, so `Ξ` grows and `skip/cycle` becomes
           reachable — that is where the evidence comes from.
        2. **At a cycle, take the `P ∈T G` it carries and CHASE it**,
           unfolding at every step so `Ξ` stays `[]` and no further cycle
           can arise.  `na` forbids a P-action at every `skip/step`, so the
           witness cannot be exhausted inside the tree: it must reach a
           main leaf.  That leaf is the `etd` (for `if`) or the
           contradiction (for `∅`).

        Recursion runs on the structural tree, so the unfolded twin may
        grow freely — hence `aif/exp` takes two arguments.

        Supporting definitions added:

        - `askip/unfold-top` / `bskip/unfold-top` — `skip/unfold-cycle`
          instantiated at the `⊢a` and `⊢blocked` families (transport =
          `alg/bisim ~ᵛ-refl` / `blocked/bisim ~ᵛ-refl`), mirroring the
          existing `pskip/unfold-top` for `⊢p`.
        - `blocked→alg` — every blocker is an `⊢a` in its own right
          (`a/skip` of a one-leaf tree), so a blocker tree IS an `⊢a` tree.
          Structural.  Needed because an `a/skip` twin has no successors to
          descend into; the first attempt without it (`bif/chase-or`)
          failed the termination checker.

        **Stale material** is at `Stale/PushRecDerivations.agda.stale` —
        NOT compilable, deliberately not a `.agda` file, header explains
        what it was.

        ── HISTORY ───────────────────────────────────────────────────

        Confirmed
        2026-08-03 to be *literally the same statement* as
        `Check/Decide.agda:791`'s `permute-tree` hole, so there is one
        problem in this development, not two — fix either and both close.

        In `Norm.agda`'s `a/tree {Pr = rec _}`: inverting a leaf is free
        (`⊢a`'s only rec form is `a/rec`, so the leaf already yields
        `Wᵢ`, `trᵢ : Wᵢ ⇝ Kᵢ`, `bodyᵢ`), and moving `bodyᵢ` from `Wᵢ` to
        `Kᵢ` is free too (`norm (alg/typing bodyᵢ) trᵢ`). The **anchor** is
        what will not move: `rebind` needs `G -[¬P]->* Wᵢ`, the root
        reaching the leaf's anchor.

        **Why the algorithmic judgment cannot help.** `a/rec`'s trace runs
        body-state ⇝ conclusion, so an anchor must sit *behind* `G`; a tree
        only yields states *ahead* of `G`. A direction mismatch is not
        fixable by changing the judgment — which is why this survived a
        rewrite that dissolved `leaf-permute` entirely.

        **Sharpened 2026-08-03 (third derivation of the same fact).**
        `a/tree` is only reached with the trace *exhausted*
        (`cancel/unskip-aux tr/refl …`), and each leaf is normalised with
        `skip/refl`. So a `t/rec`-headed leaf yields `a/rec skip/refl _ body`
        — anchor = the leaf's own state `Kᵢ` — and then `rebind` needs
        `G ⇝ Kᵢ`, **which the tree supplies**. The wall appears *only* when
        the leaf is `t/unskip`-headed, where `norm` accumulates `tr₀` and
        yields `a/rec tr₀ _ body` with `Wᵢ ≠ Kᵢ`. Hence:

            the obstruction is exactly the NON-EMPTINESS of `h/rec`'s
            trace at a tree leaf — nothing else.

        A second normalisation pass does **not** remove it: message-
        guardedness constrains the *body* `Pr` (so a body is never
        unskip-headed — that part of the argument is sound), but the
        offending unskip sits in front of the `rec` itself, which is one of
        the two positions the normal form deliberately keeps (it *becomes*
        `h/rec`'s trace). Do not spend a pass on this.

        **The single-pass shape (most promising attempt, not yet tried).**
        Rather than a separate `advance-anchor`, generalise `norm` so the
        anchor travels with the state:

            norm′ : Γ & (W ∷ Δ) ⊢p P ◂ Pr ∶ W → W ⇝ H
                  → Γ & (H ∷ Δ) ⊢a P ◂ Pr ∶ H

        `norm` already owns the advancing machinery this needs. With it the
        rec-under-tree case closes: the leaf becomes `a/rec skip/refl _ body`
        anchored at `Kᵢ`, and `rebind Kᵢ ↦ G` wants `G ⇝ Kᵢ`, which the tree
        supplies.

        Its `t/var` case works by **run-determinism**: from `W ~ occ`,
        `W -[αs]-> H` and `occ -[αs]-> occ′` one gets `H ~ occ′`, exactly
        `act/var`'s premise. This is why the anchor and the state must
        travel along traces carrying *identical action lists* —
        `skip/advance`'s `-aux` already builds those; only its type hides
        them existentially, which is what the (currently deleted)
        `advance-run`/`branch-run` refinements fixed. Recover them from git
        history if this is attempted.

        **The open part is the invariant/measure, and it is symmetric:**
        the same-labels invariant survives `t/send`/`t/recv`/`t/if`/`t/end`/
        `t/var`, and breaks in exactly two places — inner `t/unskip`
        *prepends* `βs` to the state's trace while the anchor keeps `αs`,
        and inner `t/skip`'s cancellation *consumes* a prefix, leaving the
        state on a suffix. One lengthens, one shortens. A working pass needs
        an invariant surviving both (state and anchor related by traces with
        a common extension?) plus a measure that decreases across the
        cancellation, where the tree shrinks but the trace grows. Nobody has
        that invariant yet — do not start coding before writing it down and
        checking it propagates through those two clauses on paper.

        **E1 WAS RIGHT.  THE EARLIER REJECTION OF IT WAS WRONG, AND
        `⊢a` IS INCOMPLETE FOR `⊢p` — PROVED, 2026-08-04.**

        `Tests/PushRecDerivations.agda`, module `Ex6`, contains both

            recAtG : v[] & v[] ⊢p A ◂ rec (B ! 0 ∙ v 0) ∶ G
            no-alg : ¬ (v[] & v[] ⊢a A ◂ rec (B ! 0 ∙ v 0) ∶ G)

        over one well-behaved graph (`wb`), same process, same
        participant.  So there is NO total `⊢p → ⊢a` translation with the
        current `⊢a`, and `push`'s `rec` case cannot be closed as stated.

        The graph:

            G --B⟶D--> L,  L --A⟶B--> M,
            M --B⟶C⟨0⟩--> L,  M --B⟶C⟨1⟩--> H,  H --A⟶B--> H

        with the anchor at M.  On the ⟨0⟩ branch the variable resolves at
        M itself; on the ⟨1⟩ branch it is `t/unskip (M ⇝ H) (t/var ~refl)`
        — a NON-EMPTY witness, off the join path.  `no-alg` closes because
        `a/rec`'s trace forces the anchor to be G (nothing steps into G),
        `na` fails at L so the send is forced to be L's, the variable at M
        must therefore skip, and the ⟨1⟩ branch lands at H where `act/var`
        is impossible (`G≁H`, `L≁H`) and skipping is impossible
        (`H-cannot-skip`: H's only action mentions A).

        The previous entry here rejected E1 on the strength of
        `scratchpad/OffPathAnchor.agda` being ill-behaved and concluded
        "Do not weaken `a/rec`".  **That was wrong.**  Off-path anchors ARE
        realisable in well-behaved graphs — `Ex2`, `Ex4` and `Ex6` of
        `Tests/PushRecDerivations.agda` all have one.  The old graph was
        rejected for reasons particular to its choice of actions, not
        because the shape is excluded.

        **So: DO weaken `a/rec` — give it a tree.**  Currently

            a/rec : G -[¬ P ]->* G′ → MessageGuarded Pr
                  → Γ & (G ∷ Δ) ⊢a P ◂ Pr ∶ G
                  → Γ & Δ ⊢a P ◂ rec Pr ∶ G′

        folds in only the `t/unskip`.  What `⊢p` has and `⊢a` lacks is the
        `t/skip` in FRONT, and a skip tree branches, so each leaf carries
        its OWN anchor.  `a/rec` needs the shape `a/act` already has:

            RecLeaf (P ◂ rec Pr) L =
              ∃[ W ] (W -[¬ P ]->* L) × MessageGuarded Pr
                   × (Γ & (W ∷ Δ) ⊢a P ◂ Pr ∶ W)

            a/rec : (RecLeaf) & [] ⊢skip P ◂ rec Pr ∶ G
                  → Γ & Δ ⊢a P ◂ rec Pr ∶ G

        Ex6 then types directly: tree from G stepping to L, one leaf with
        W = M, `M ⇝ L`, body at M anchored M — a mirror of `recAtG`.
        Soundness stays trivial (`t/skip` of a tree of
        `t/unskip trᵢ (t/rec …)`) and the checker needs no new capability,
        since it already decides trees for `a/act`.

        NOT yet proved: that this suffices in general.  It handles Ex6.

        **A NOTE ON THE SPAN FORMULATION, ALSO REFUTED.**  The type

            reanchor : W -[¬ P ]->* L → G -[¬ P ]->* L
                     → Γ & (W ∷ Δ) ⊢a P ◂ Pr ∶ S
                     → Γ & (G ∷ Δ) ⊢a P ◂ Pr ∶ S

        is FALSE: Ex6 satisfies both premises (`M ⇝ L`, `G ⇝ L`) and the
        conclusion fails.  Every earlier anchor-moving statement
        (`W ~ K`, `unskip-transfer`, `step-commute`, `advance-anchor`) is
        dead for the same underlying reason — the variable may resolve
        against a state off the join path that cannot skip back onto it.

        **THE ROUTE (2026-08-04).** The `rec` case of `a/tree` closes as:

          1. `advance-anchor trᵢ bodyᵢ` — body at `Wᵢ` anchored `Wᵢ` becomes
             body at `Kᵢ` anchored `Kᵢ`;
          2. `rebind Kᵢ ↦ G` — wants `G ⇝ Kᵢ`, **which the tree supplies**;
          3. `graft` the leaves and emit `a/rec skip/refl guarded body`.

        Steps 2 and 3 already exist. So `advance-anchor` is the *only*
        missing piece in the entire development:

            advance-anchor : W -[¬ P ]->* K
                           → Γ & (W ∷ Δ) ⊢a P ◂ Pr ∶ W
                           → Γ & (K ∷ Δ) ⊢a P ◂ Pr ∶ K

        **Status (2026-08-04, evening — after deleting the scratch).**
        `Norm.agda` now states `advance-anchor` directly; `adv`,
        `act-walk`, `leaf-permute`, `unskip-transfer`, `⇝-confluent` and
        `step-commute` are DELETED (all refuted or unused). 18 holes → 8.

            advance-anchor : W -[¬ P ]->* K
                           → Γ & (W ∷ Δ) ⊢a P ◂ Pr ∶ W
                           → Γ & (K ∷ Δ) ⊢a P ◂ Pr ∶ K

        `a/if` and `a/end` are proved. Two holes remain:

        - **`a/act`** (`Norm.agda:613`): tree rooted at `W` anchored `W`
          ⟹ tree rooted at `K` anchored `K`. The anchor is the tree's own
          root in both cases, so an `act/var` leaf at state `L` needs
          `K ⇝ H` with `H ~ L` and the tree itself walks `K ⇝ L` — try
          `H := L`, `~refl`. UNTESTED.
        - **`a/rec`** (`Norm.agda:619`): `a/rec (skip/cat tr₀ tr) guarded
          {!!}` typechecks, so trace and state are handled; what is left
          is replacing `W` by `K` at Δ's SECOND position — this same
          lemma at a non-head index.

        Anchor and state always coincide (`advance-anchor` is the only
        caller), so do NOT reintroduce separate `W`/`S` or a `W ~ S`
        premise: it makes `~-lockstep` yield `K ~ K` and buys nothing.

        *(superseded experiments, kept for the reasoning)*

        *E1 — make `a/rec` carry a TREE, mirroring `a/act`.* CONFIRMED CORRECT
        above (Ex6); this paragraph's original "rejected" verdict was wrong.
        `a/act` folds
        its skip tree in, `a/rec` does not, so a `rec` under a tree has
        nowhere to put it. Change

            a/rec : G -[¬P]->* G′ → MessageGuarded Pr
                  → Γ & (G ∷ Δ) ⊢a P ◂ Pr ∶ G → Γ & Δ ⊢a P ◂ rec Pr ∶ G′

        to carry a `⊢skip` tree whose leaves are anchored bodies
        (`∃ W. (W ⇝ leaf-state) × MessageGuarded Pr × body at W anchored W`).
        Then `a/tree`'s `rec` case is *immediate* — hand it `std` with the
        leaves' own `(Wᵢ , trᵢ , bodyᵢ)`, no common anchor needed. Soundness
        stays trivial: `alg/typing` maps it to `t/skip` of a tree whose
        leaves are `t/unskip trᵢ (t/rec gᵢ (alg/typing bodyᵢ))`. Cost: the
        decision procedure must decide that tree — which it already must do
        for `a/act`, so no new capability is required. **Try this first.**

        *E2 — thread the original `⊢p` derivation into `a/tree`.* Give
        `a/tree` the un-normalised `Γ & Δ ⊢p P ◂ Pr ∶ O` alongside the tree,
        so the `rec` case can invert it directly (`t/rec` gives the body at
        `O` outright) instead of reconstructing one from the leaves. Fails
        exactly when that derivation is itself `t/skip`-headed, so it is
        `leaf-permute` recursion — but it may bottom out, and it is cheap
        to test.

        *E3 — strengthen `LeafAlg`'s contract.* Currently a leaf yields
        `⊢a` at any `H′` reachable *from* the leaf. Strengthen it to also
        yield, for a `rec`-headed leaf, the body re-anchored at any `A`
        with `A ⇝ leaf-state`. That is assuming the wall rather than
        proving it, so it only pays off if the *callers* can always supply
        such an `A` — worth one afternoon to check, no more.

        **Origin threading (done, kept): `cancel/unskip`/`a/tree` now carry
        `origin : O -[¬P]->* G`**, accumulated across the cancellation. It
        makes `a/rec origin _ _` typecheck at the root, which is necessary
        for all three experiments, but on its own only relocates the
        obligation from `G ⇝ Wᵢ` to `O ⇝ Wᵢ`.

        ── RESULTS OF 2026-08-04's EXPERIMENTS ────────────────────────

        **Proved and available** (`Norm.agda`, no holes, `WellBehaved`
        untouched):

            run-deterministic : G₀ -[ αs ]-> G₁ → G₀ -[ αs ]-> G₂ → G₁ ≡ G₂
            ~-lockstep : W ~ W′ → W -[ αs ]-> K → W′ -[ αs ]-> K′ → K ~ K′

        `~-lockstep` is four lines (`tr-transport` then
        `run-deterministic`). It is the right generalisation: not one source
        `W` with two divergent traces, but two *bisimilar* sources advanced
        along the **same** action list.

        **Dead ends, each tested, do not retry:**

        - *Confluence of two `¬P` traces* (`⇝-confluent`, stated in
          `Norm.agda`): not derivable. `step-diamond` needs `α ⋄ β`, and the
          only `⋄`-producing lemma, `active-inactive/⋄`, requires one action
          to be `P`-active — both are `¬P` here. The residual case is two
          choices of one comm, which cannot be joined.
        - *`W ~ K`* (re-anchoring in place): **false**, refuted by a single
          `¬P` step in `Tests/SkipBeforeVar.agda`.
        - *`unskip-transfer`* (move the variable's witness from `W` to `K`):
          **false**, and it dies at its easiest case — an *empty* witness
          (`H = W`, the ordinary `act/var skip/refl` shape) reduces it to
          `W ~ K` again. Consequence: `advance-anchor` cannot be proved by
          transporting the witness; the `act/var` leaf must be REBUILT from
          `K`'s own reachability.
        - *E1, giving `a/rec` a tree*: rejected, see above.

        **What `~-lockstep` does close.** At `act/var tr eq` with
        `eq : H ~ S`: `tr-transport` gives `H -[αs]-> H′` with `H′ ~ S′`,
        which is the second premise at `K`. When the witness is empty
        (`H = W`), `run-deterministic` identifies `H′` with `K`, so the
        first premise is `skip/refl`. **That case is closed.** What remains
        is a *non-empty* witness, where `K ⇝ H′` needs the witness trace and
        the advance trace to commute.

        **THE NEXT PROOF, with its seed (start here).** Two counterexample
        attempts at that remaining case are saved as
        `scratchpad/DownstreamVar.agda`; **both were rejected by
        `wellBehaved?`, and both failed the same way** — the two branch
        targets came out bisimilar, and `stepback/~` then demands a
        `γ#0`-edge into `K` from something bisimilar to `W`, while
        `step-deterministic` pins `γ#0` from `W` to `H` alone.

        So aim at: *the blocking configuration forces `H ~ K`, which
        well-behavedness excludes.* Skeleton:

          1. Blocking needs `W` offering a `P`-action `α` **and** a
             same-comm branch `γ#0 → H`, `γ#1 → K` (same-comm because
             `recv-overlap⇒same-comm` forces it whenever non-independent,
             and non-independence is what blocks commuting).
          2. `RecvCoherent` at `W` forces `γ` to avoid `α`'s receiver, hence
             `α ⋄ γ#i`, hence `step-diamond` on both branches:
             `W₁ -γ#0-> V₀` with `H -α-> V₀`, and `W₁ -γ#1-> V₁` with
             `K -α-> V₁`.
          3. So `H` and `K` both offer `α`, into the two `γ`-images of `W₁`.
          4. The variable's witness additionally forces `H ~ W₁`.
          5. 3+4 push `H` and `K` to be bisimilar — and `H ~ K` contradicts
             `stepback/~` together with `step-deterministic`.

        **`stepback/~` is the axiom to use; it is the only one untouched so
        far**, and it is what rejected both counterexamples.

        ── VERDICT OF 2026-08-04 (evening): THE SEED IS WRONG, AND THE
        ── ONE-STEP LEMMA IS **REFUTED**. ─────────────────────────────

        The skeleton above was reduced to its single-step core,
        `Norm.agda:722`:

            step-commute : W -< a >-> K → P ∉α a
                         → W -< b >-> H → P ∉α b
                         → H -< a >-> H₀
                         → K -< b >-> H₀

        Its *independent* case is **proved** (`step-diamond` closes the
        square, `step-deterministic` identifies the corner with `H₀`). Its
        overlapping case — two distinct choices of one comm, which
        `recv-overlap⇒same-comm` forces — is **false**.

        All five counterexample attempts now live in
        **`Tests/AnchorAttempts.agda`** (compiling, editable — each verdict
        is a *checked* proof, `not-wb₁…₄` / `wb₅`, not a comment):

        - attempts 1–3 rejected exactly as the seed predicted: the two
          branch targets came out bisimilar and `stepback/~` +
          `step-deterministic` killed them;
        - attempt 4 (targets made observably different) rejected for an
          **unrelated** reason — `no-new-comm/step`, because the
          distinguishing comm `A ⟶ C` appears after a `C ⟶ D` step with
          `A` uninvolved. Inconclusive, which is what forced attempt 5;
        - **attempt 5 is the counterexample.** Minimal premise
          configuration, targets told apart using only participants `γ`
          already involves, so neither of the above escapes applies:

              W --γ0--> K,  W --γ1--> H,  H --γ0--> H₀,
              K --(D ⟶ A)--> end,  H₀ --(C ⟶ A)--> end,  γ = C ⟶ D, P = A

          `wb₅ : WellBehaved (graphTheory G₅)` typechecks. Every premise
          holds (`A` is in neither `γ0` nor `γ1`); the conclusion fails —
          `K` has no `γ1`-edge at all.

        **So no purely graph-level commutation lemma can close the anchor
        case, and `stepback/~` was a red herring.** Do not retry the
        skeleton, and do not attempt the two holes at `Norm.agda:740-741`.

        **The obvious repair does NOT work — attempt 6, also checked.**
        In `G₅` the process `A` is *active* at `K` (it receives in
        `D ⟶ A`), which a `⊢skip` tree would forbid: `skip/step` covers
        all successors of `W` carrying `na`. So the natural fix is to
        strengthen the lemma with the `na`s available at the call site:

            … → P not-active-in K → P not-active-in H₀ → K -< b >-> H₀

        `G₆` is `G₅` with the two distinguishing actions rebased onto `B`
        (`D ⟶ B` out of `K`, `C ⟶ B` out of `H₀`) — senders still inside
        `C ⟶ D`, so `no-new-comm/step` is satisfied, and `A` appears
        nowhere, so both `na` premises hold. `wb₆` typechecks. **The
        strengthened lemma is false too.**

        **Conclusion: the commutation is not a graph fact at all**, with
        or without `na`, and no further counterexample hunting is
        warranted — the shape is realisable and that is settled. The one
        piece of leverage none of `G₁…G₆` models is the *typing*
        constraint at the leaf: `act/var tr eq` carries `eq : H ~ S`
        tying the witness's target to the tree's leaf state. Any further
        attempt must use that bisimilarity; a statement about steps and
        `na` alone cannot be true.

        **Failing all that, the fork is unchanged, and it is a decision,
        not engineering:** either prove
        the semantic lemma (`advance-anchor`: `W ⇝ H` + body at `W`
        anchored `W` ⟹ body at `H` anchored `H`) — which I argued is
        probably *true*, since `recv-overlap⇒same-comm` forces any `¬P`
        edge out of a `P`-active state to be `⋄`-independent of the
        `P`-action and `step-diamond` then copies that action forward, and
        two attempted counterexamples died exactly there — or build the
        counterexample that kills it. Do not attempt a third re-plumbing of
        the surrounding code; it will land here again. Since a `rec` body is `MessageGuarded`, its head is a
        communication, so the intended route is to push the skip *into the
        body*, where it merges into the body's `h/send`/`h/recv`. That
        transformation re-anchors each leaf, which is where the
        `Check.agda` attempt stopped — §4. Verify it against the phase-1
        normal form (leaves already `h/rec tr guarded body`) before
        assuming it goes through.
- [ ] **Step 6 — decide `⊢head`, constructor by constructor.** Each clause
      becomes local: `h/var` is one reachability query from the *known*
      source (§2), `h/send`/`h/recv` a reachability query for a matching
      edge, `h/rec` per Step 0, `h/if`/`h/end` direct.
- [ ] **Step 7 — wire into `tcGraph`.** `map′ head/typing td/head` over the
      `⊢head` decision. Only here does `Check.agda`'s existing `rec`
      worklist get retired or reused.

## Acceptance criterion (what "done" means for this plan)

Every step ends compiler-green, and the plan as a whole ends with:

- `./runall.sh` clean on all roots (`Definitions.agda`, `Safety.agda`,
  `Check.agda`) — note `Definitions.agda` does **not** compile today (§1a),
  so Step 1 already improves on the status quo;
- `agda Check/Check.agda` reporting *only* unsolved interaction metas —
  i.e. `Check.agda` is the sole file with holes, and every dependency of it
  compiles clean;
- `Tests/RecSkipCounterexample.agda` compiling (it uses the typing rules
  directly, not the checker).

`Tests/Perf*` and `Examples/*` are **excluded** until Step 7: they import
the old `Definitions.TypeChecker` and are red today, before any of this
work. See §1a.

Anything that leaves a second file holed, or a root red, is not a finished
step — split it further instead.

## 1. Done, compiler-confirmed

`tcGraph`'s `∅` case, built on `find-leaf/remember`, `find-leaf`,
`end-refute-td/accessible`, `end-refute-td` — all clean, no postulates.

**Lessons learnt (compiler-confirmed), essence only:**

1. A witness-following helper and an `Accessibleᵗ`-decreasing driver must be
   two separate functions, never mutually recursive.
2. A destructured HOF (`accN`) must be applied directly, syntactically, in
   the clause that destructured it — never via an intermediate call's return
   value.
3. Reuse `Safety/Skip.agda`'s cycle-folding — don't reinvent it.
4. Keep `~Leaf`/`~MainLeaf` out of a helper's public interface.
5. Generalize a helper over `Pr` when its logic doesn't depend on it.
6. Pin `visited`/vector implicits explicitly (`lookup` is non-injective);
   otherwise Agda leaves unsolved metas at every call site.

## 2. Per-case notes (to be re-read as `⊢head`'s rules, not `⊢p`'s)

### `ifp E then Pr else Pr′` — direct, no skip handling
`t/if`'s premises are state-independent, so `h/if` needs no trace. Skip in
front of an `if` splits over the branches (Step 5c).

### `rec Pr` — "yes" direct, "no" is Step 2/5e
`t/rec`'s premises are state-independent, so the "yes" construction never
searches for an anchor other than `s`. The "no" side is the open one.

### `v X` — reachability-up-to-bisim from the known source
`Safety/Head.agda`'s `skip/bisim-back : G ~ G′ → G′ -[¬P]->* H′ →
∃[H] (G -[¬P]->* H) × (H ~ H′)` turns `t/unskip tr (t/var eq)` into
`∃[s′] (Δ[X] -[¬P]->* s′) × (s′ ~ s)` — one `reachVia?`/`PathVia`
fixed-point from the *known* source `Δ[X]`, then `Fin.any?` against
`bisim?~ _ s`. **Correction to the previous version of this file:** that is
*not* the only shape of a `v X` derivation — `t/skip` can wrap a `v X` just
as it wraps anything else. Either Step 5d rules that out (making the claim
true of the algorithmic form), or the `v` clause must handle the tree.

### Send / recv — needs reachability, not `P ∈T`
A send/recv needs a specific edge at `s`, and the process genuinely can be
skip-wrapped waiting for it. `P ∈T` is *not* the relevant tool (`P` may
never become active). In `⊢head` this is exactly the "skip merged with the
action" rule, so the clause is one reachability query for a matching edge.

## 3. Termination measure for the walking cases

Lexicographic `(size Pr, remaining-states)`. `Ξ` is the *skip judgment's
own* visited set, scoped to one `t/skip` derivation via `skip/step`; it
carries no meaning outside it, and `t/unskip` has no `Ξ` at all — a search
that tries `t/unskip` needs its own, separate visited-states bookkeeping
(same `size G` ceiling, not to be conflated with `Ξ`). Structural steps
decrease the first component; skip-walking steps decrease `size G ∸ ξ`.
Already realised for the `rec` worklist as `_≺_` + `remaining`/
`mark-decreases` in `Check.agda`.

## 4. State of the `rec` refutation (keep compiling, do not extend)

```agda
    rec-refute/unskip mg visited table cov td with leaf-permute mg td
    ... | s′ , tr , body = table s′ (cov tr) body
```

`leaf-permute : MessageGuarded Pr → Γ & Δ ⊢p P ◂ rec Pr ∶ H →
∃[ s ] (s -[¬P]->* H) × (Γ & (s ∷ Δ) ⊢p P ◂ Pr ∶ s)` — anchor as *output*,
body typed *at* the anchor, trace running *into* `H`. That is exactly
`Table`'s shape and exactly `Covers`' input, which is why the refutation is
one line with no case analysis. `t/rec` and `t/unskip` clauses are closed
(`skip/refl`, `skip/cat tr′ tr₀`, body passed through untouched).

**The single hole** is `permute-tree`'s `skip/main` clause: with
`tr : s ⇝ H` (root to leaf) and `tr′ : s′ ⇝ H` (leaf's anchor to leaf), it
needs `s -[¬P]->* s′`. Two states reaching a common state, wanting a trace
between them — not derivable from the graph axioms (they constrain
*outgoing* edges; `stepback/~` relates steps into *bisimilar* targets, never
two distinct traces into the same state).

Note the direction matches `h/rec` exactly: `h/rec (K ⇝ G′) guarded (body at
K)` is the same "body at a state that reaches the conclusion" shape that
`leaf-permute` returns. So `leaf-permute`'s *statement* is the `rec`
normalisation, and it survives the move — as does the worklist, `Covers`
and `Table`. What does not survive is `permute-tree`'s mirroring, which
only exists because the anchor was forced to be the tree's root.

## 5. Notes for whoever implements this

1. **Useful fact for 3b and any "find the leaf" step.** A skip tree can
   never cycle on every branch: `skip/cycle` needs `P ∈T G` plus a
   `Ξ`-ancestor `~ G`, ancestors are `skip/step` nodes (so `P` inactive
   there), and a `P`-active state cannot be bisimilar to a `P`-inactive
   one. So the `P ∈T` witness always lands on a real `skip/main` leaf.
   `find-any-leaf`/`leaf-or-∈T/ml` in `Check.agda` already implement the
   walk.
2. **Structurality.** The `t/skip` case of the normalisation is not
   structural — unfolding a cycle substitutes a subtree. `Head.agda` keeps
   it honest by carrying `LeafHead` *properties* rather than trees; 3a must
   preserve that discipline or the termination checker rejects it.
3. **Cost.** Step 3a dominates: `Safety/Head.agda` is 666 lines, ~58 of
   them the `LeafHead`/`cancel/unskip`/`if-split` machinery. Steps 1, 2, 4
   are mechanical by comparison.
